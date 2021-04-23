#!/bin/bash

echo "Running Tests..."
scriptdir="$(dirname "$0")"
cd "$scriptdir"
cd "../small-haskell"
stack test --ta k