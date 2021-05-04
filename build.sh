#!/bin/bash

scriptdir="$(dirname "$0")"
cd $scriptdir
if [[ "$@" != *-ni* ]]
then
    echo "Compiling Interpreter..."
    kompile -d "./out/interpreter" "./src/Interpreter/small-interpreter.k" "--gen-glr-bison-parser" "--syntax-module" "SMALL-SYNTAX-BASE" $@
fi
if [[ "$@" != *-nt* ]]
then
    echo "Compiling Type Checker..."
    kompile -d "./out/type-checker" "./src/TypeChecker/small-type-checker.k" "--gen-glr-bison-parser" "--syntax-module" "SMALL-SYNTAX-BASE" $@
fi