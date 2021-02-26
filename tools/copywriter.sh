#!/bin/bash -x

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT

DRY_RUN=
if [ "$1" == "-d" ]; then
    DRY_RUN=echo
fi

COPYRIGHT_NOTICE="Copyright 2018-2021 VMware, Inc."
COPYING_PERMISSION_STATEMENT="SPDX-License-Identifier: MIT"

function starts_with_bang_line() {
    FILENAME="$1"
    head -n 1 "$FILENAME" | grep "^#!" > /dev/null 2>&1
    status=("${PIPESTATUS[@]}")
    echo ${status[0]} ${status[1]}
    if [ ${status[0]} != 0 ]; then
        return 2
    fi
    return ${status[1]}
}

while [ $1 ]; do
    FILENAME="$1"
    shift

    TMPSUFFIX="${FILENAME##*.}"
    SUFFIX="${TMPSUFFIX,,}"
    COMMENT_PREFIX=""
    BANGLINES=0
    if [ "$SUFFIX" == "dfy" ]; then
        COMMENT_PREFIX="//"
    elif [ "$SUFFIX" == "c" ]; then
        COMMENT_PREFIX="//"
    elif [ "$SUFFIX" == "h" ]; then
        COMMENT_PREFIX="//"
    elif [ "$SUFFIX" == "cpp" ]; then
        COMMENT_PREFIX="//"
    elif [ "$SUFFIX" == "hpp" ]; then
        COMMENT_PREFIX="//"
    elif [ "$SUFFIX" == "sh" ]; then
        starts_with_bang_line "$FILENAME"
        RESULT=$?
        if [ $RESULT == 0 ]; then
            BANGLINES=1
        elif [ $RESULT != 1 ]; then
            continue
        fi
        COMMENT_PREFIX="#"
    elif [ "$SUFFIX" == "py" ]; then
        starts_with_bang_line "$FILENAME"
        RESULT=$?
        if [ $RESULT == 0 ]; then
            BANGLINES=1
        elif [ $RESULT != 1 ]; then
            continue
        fi
        COMMENT_PREFIX="#"
    fi

    grep -F -m 1 "$COPYRIGHT_NOTICE" "$FILENAME" > /dev/null 2>&1
    CONTAINS_COPYRIGHT_NOTICE=$?
    grep -F -m 1 "$COPYING_PERMISSION_STATEMENT" "$FILENAME" > /dev/null 2>&1
    CONTAINS_COPYING_PERMISSION_STATEMENT=$?

    if [ $CONTAINS_COPYRIGHT_NOTICE != 1 ]; then
      continue
    fi
    if [ $CONTAINS_COPYING_PERMISSION_STATEMENT != 1 ]; then
      continue
    fi

    if [ "$COMMENT_PREFIX" ]; then
        TMPFILE=`mktemp` &&
        head -n $BANGLINES "$FILENAME" > "$TMPFILE" &&
        if [ $BANGLINES -gt 0 ]; then echo >> "$TMPFILE"; fi &&
        echo "$COMMENT_PREFIX" "$COPYRIGHT_NOTICE" >> "$TMPFILE" &&
        echo "$COMMENT_PREFIX" "$COPYING_PERMISSION_STATEMENT" >> "$TMPFILE" &&
        echo >> "$TMPFILE" &&
        tail -n +"$[ $BANGLINES + 1 ]" "$FILENAME" >> "$TMPFILE" &&
        $DRY_RUN cp "$TMPFILE" "$FILENAME"
    fi

done
