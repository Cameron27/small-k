#!/bin/bash

scriptdir="$(dirname "$0")"
krun --directory "$scriptdir/out/type-checker" $@
code=$?
if [ $code -eq 2 ]
then
    exit 2
fi
if [ $code -eq 139 ]
then
    exit 3
fi
if [ $code -eq 0 ]
then
    krun --directory "$scriptdir/out/interpreter" $@
    exit $?
fi
exit $code