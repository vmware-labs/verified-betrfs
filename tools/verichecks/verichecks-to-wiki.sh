#!/bin/bash

function debug() {
    echo "::debug file=${BASH_SOURCE[0]},line=${BASH_LINENO[0]}::$1"
}

function warning() {
    echo "::warning file=${BASH_SOURCE[0]},line=${BASH_LINENO[0]}::$1"
}

function error() {
    echo "::error file=${BASH_SOURCE[0]},line=${BASH_LINENO[0]}::$1"
}




if [ -z "$GITHUB_REPOSITORY" ]; then
    error "GITHUB_REPOSITORY environment variable is not set"
    exit 1
fi

if [ -z "$GH_PERSONAL_ACCESS_TOKEN" ]; then
    error "GH_PERSONAL_ACCESS_TOKEN environment variable is not set"
    exit 1
fi


if [ -z $GITHUB_REF ]; then
    COMMITID=$GITHUB_SHA
else 
    COMMITID=`basename $GITHUB_REF`
fi

if [ -z $COMMITID ]; then
    error "Could not determin commit ID."
    exit 1
fi

if [ -z "$GH_PERSONAL_ACCESS_TOKEN" ]; then
    error "GH_PERSONAL_ACCESS_TOKEN environment variable is not set"
    exit 1
fi

GIT_REPOSITORY_URL="https://${GH_PERSONAL_ACCESS_TOKEN}@${GITHUB_SERVER_URL#https://}/$GITHUB_REPOSITORY.wiki.git"

tmp_dir=$(mktemp -d -t ci-XXXXXXXXXX)
function finish {
  rm -rf "$tmp_dir"
}
trap finish EXIT

debug "Checking out wiki repository"
(
    cd "$tmp_dir" &&
    git init &&
    git config user.name "$GITHUB_ACTOR" &&
    git config user.email "$GITHUB_ACTOR@users.noreply.github.com" &&
    git pull "$GIT_REPOSITORY_URL"
) || exit 1

debug "Removing old results"
(
    cd "$tmp_dir" &&
    git rm -rf --ignore-unmatch verichecks-results/$GITHUB_SHA
) || exit 1

debug "Copying new results"
(
    mkdir -p "$tmp_dir"/verichecks-results/$GITHUB_SHA &&
    cp -r build "$tmp_dir"/verichecks-results/$GITHUB_SHA &&
    echo -n $COMMITID > "$tmp_dir"/verichecks-results/$GITHUB_SHA/commitid
) || exit 1

debug "Regenerating table of contents"
(
    cd "$tmp_dir" &&
    for d in `ls -t verichecks-results`; do
        echo -n "[\`${d:0:10}\`](${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY}/commit/$d)" " "
        if [ -f verichecks-results/$d/commitid ]; then
            echo -n "\(\`"
            cat verichecks-results/$d/commitid
            echo -n "\`\)" " "
        fi
        echo -n "- "
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.verified ]; then
            echo -n \[summary\]\(verichecks-results/$d/build/Impl/Bundle.i.verified\) " - "
        fi
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.status.txt ]; then
            echo -n \[details\]\(verichecks-results/$d/build/Impl/Bundle.i.verified.err\) " - "
        fi
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.status.svg ]; then
            echo -n \[status-SVG\]\(verichecks-results/$d/build/Impl/Bundle.i.status.svg\) " - "
        fi
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.status.pdf ]; then
            echo -n \[status-PDF\]\(verichecks-results/$d/build/Impl/Bundle.i.status.pdf\) " - "
        fi
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.syntax-status.svg ]; then
            echo -n \[syntax-status-SVG\]\(verichecks-results/$d/build/Impl/Bundle.i.syntax-status.svg\) " - "
        fi
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.syntax-status.pdf ]; then
            echo -n \[syntax-status-PDF\]\(verichecks-results/$d/build/Impl/Bundle.i.syntax-status.pdf\) " - "
        fi
        echo
        echo
    done > verichecks-results.md
) || exit 1

debug "Committing and pushing"
(
    cd "$tmp_dir" &&
    git add verichecks-results.md &&
    git add -f verichecks-results/$GITHUB_SHA/* &&
    git commit -m "Veri-checks results for $GITHUB_SHA" &&
    git push --set-upstream "$GIT_REPOSITORY_URL" master
) || exit 1

