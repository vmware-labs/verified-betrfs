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

# When a user requests a run manually, we can't use GITHUB_REF or
# GITHUB_SHA because they point to the branch of the workflow file,
# not the branch being checked (unless they happen to be the same).
# So, instead, we get the identity of the branch being checked from
# the horses mouth.
COMMIT_SHA=`git rev-parse HEAD`
BRANCH_NAMES=`git rev-parse --abbrev-ref HEAD`

if [ -z $COMMIT_SHA ]; then
    error "Could not determin commit SHA."
    exit 1
fi

if [ -z "$GITHUB_REPOSITORY" ]; then
    error "GITHUB_REPOSITORY environment variable is not set"
    exit 1
fi

if [ -z "$GH_PERSONAL_ACCESS_TOKEN" ]; then
    error "GH_PERSONAL_ACCESS_TOKEN environment variable is not set"
    exit 1
fi

echo GITHUB_HEAD_REF $GITHUB_HEAD_REF
echo GITHUB_BASE_REF $GITHUB_BASE_REF
echo GITHUB_REF $GITHUB_REF
echo GITHUB_SHA $GITHUB_SHA
echo BRANCH_NAMES $BRANCH_NAMES
echo COMMIT_SHA $COMMIT_SHA

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
    git rm -rf --ignore-unmatch verichecks-results/$COMMIT_SHA
) || exit 1

debug "Copying new results"
(
    mkdir -p "$tmp_dir"/verichecks-results/$COMMIT_SHA &&
    cp -r build "$tmp_dir"/verichecks-results/$COMMIT_SHA &&
    echo -n $BRANCH_NAMES > "$tmp_dir"/verichecks-results/$COMMIT_SHA/commitid
    git add -f verichecks-results/$COMMIT_SHA/* &&
    git commit -m "Veri-checks results for $COMMIT_SHA"
) || exit 1

debug "Regenerating table of contents"
(
    cd "$tmp_dir" &&
    # Timestamp all the directories based on their git history, so
    # they will be sorted from newest to oldest in the output
    for d in verichecks-results/*; do
        DATE=$(git log --pretty=format:%cd -n 1 --date=format-local:%Y%m%d%H%M.%S $d) &&
        touch -m -t "$DATE" "$d";
    done &&
    for d in `ls -t verichecks-results`; do
        echo -n "[\`${d:0:10}\`](${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY}/commit/$d)" " "
        if [ -f verichecks-results/$d/commitid ]; then
            echo -n "\(\`"
            cat verichecks-results/$d/commitid
            echo -n "\`\)" " "
        fi
        echo -n "- "
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.verified ]; then
            echo -n \[summary\]\(https://raw.githubusercontent.com/wiki/${GITHUB_REPOSITORY}/verichecks-results/$d/build/Impl/Bundle.i.verified\) " - "
        fi
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.status.txt ]; then
            echo -n \[details\]\(https://raw.githubusercontent.com/wiki/${GITHUB_REPOSITORY}/verichecks-results/$d/build/Impl/Bundle.i.verified.err\) " - "
        fi
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.status.svg ]; then
            echo -n \[status-SVG\]\(https://raw.githubusercontent.com/wiki/${GITHUB_REPOSITORY}/verichecks-results/$d/build/Impl/Bundle.i.status.svg\) " - "
        fi
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.status.pdf ]; then
            echo -n \[status-PDF\]\(https://raw.githubusercontent.com/wiki/${GITHUB_REPOSITORY}/verichecks-results/$d/build/Impl/Bundle.i.status.pdf\) " - "
        fi
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.syntax-status.svg ]; then
            echo -n \[syntax-status-SVG\]\(https://raw.githubusercontent.com/wiki/${GITHUB_REPOSITORY}/verichecks-results/$d/build/Impl/Bundle.i.syntax-status.svg\) " - "
        fi
        if [ -f verichecks-results/$d/build/Impl/Bundle.i.syntax-status.pdf ]; then
            echo -n \[syntax-status-PDF\]\(https://raw.githubusercontent.com/wiki/${GITHUB_REPOSITORY}/verichecks-results/$d/build/Impl/Bundle.i.syntax-status.pdf\) " "
        fi
        DATE=$(git log --pretty=format:%cd -n 1 $d)
        echo -n "\($DATE\)"
        echo
        echo
    done > verichecks-results.md
) || exit 1

debug "Committing and pushing"
(
    cd "$tmp_dir" &&
    git add verichecks-results.md &&
    git commit -m "Veri-checks table-of-contents for $COMMIT_SHA" &&
    git push --set-upstream "$GIT_REPOSITORY_URL" master
) || exit 1

