#!/bin/bash

scriptdir="$(dirname "$0")"
krun --directory "$scriptdir/out/type-checker" $@
code=$?
if [ $code -eq 2 ]
then
    exit 2
fi
if [ $code -eq 113 ]
then
    exit 3
fi
krun --directory "$scriptdir/out/interpreter" $@
exit $?