#!/bin/bash

echo "Running Tests..."
scriptdir="$(dirname "$0")"
cd "$scriptdir"
absolutepath=`pwd`
if [[ -z "$1" ]]
then
    cd "../small-haskell"
else
    cd "$1"
fi
stack test --ta "-k $absolutepath k"