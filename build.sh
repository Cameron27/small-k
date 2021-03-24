#!/bin/sh

echo "Compiling..."
scriptdir="$(dirname "$0")"
cd $scriptdir
kompile -d . "./src/small.k" $1