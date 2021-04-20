#!/bin/sh

echo "Compiling..."
scriptdir="$(dirname "$0")"
cd $scriptdir
kompile -d . "./src/Interpreter/small-interpreter.k" "--gen-glr-bison-parser" "--syntax-module" "SMALL-SYNTAX" $@