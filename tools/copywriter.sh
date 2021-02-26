#!/bin/bash

COPYRIGHT_NOTICE="Copyright 2018-2021 VMware, Inc."
COPYING_PERMISSION_STATEMENT="SPDX-License-Identifier: MIT"

while [ $1 ]; do
    FILENAME="$1"
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
        BANGLINES=1
        COMMENT_PREFIX="#"
    elif [ "$SUFFIX" == "py" ]; then
        BANGLINES=1
        COMMENT_PREFIX="#"
    fi

    if [ "$COMMENT_PREFIX" ]; then
        TMPFILE=`mktemp` &&
        head -n $BANGLINES "$FILENAME" > "$TMPFILE" &&
        if [ $BANGLINES -gt 0 ]; then echo >> "$TMPFILE"; fi &&
        echo "$COMMENT_PREFIX" "$COPYRIGHT_NOTICE" >> "$TMPFILE" &&
        echo "$COMMENT_PREFIX" "$COPYING_PERMISSION_STATEMENT" >> "$TMPFILE" &&
        echo >> "$TMPFILE" &&
        tail -n +"$[ $BANGLINES + 1 ]" "$FILENAME" >> "$TMPFILE" &&
        echo cp "$TMPFILE" "$FILENAME"
    fi

    shift
done
