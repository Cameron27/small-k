# Small-Haskell

An implementation of the semantics of the language Small using the K Framework.

## Build and Running

### Dependencies

First Git and the K Framework need to be installed. This can be done on Ubuntu 20.04 with:
```sh
wget https://github.com/kframework/k/releases/download/v5.1.11/kframework_5.1.11_amd64_focal.deb
sudo apt update
sudo apt install git ./kframework_5.1.11_amd64_focal.deb
```
For other platforms see https://git-scm.com/downloads and https://github.com/kframework/k/releases/tag/v5.1.11. Please note that version 5.1.11 of the K Framework must be used otherwise the semantics may not work.

### Clone Repository

The git repository can be cloned with:
```sh
git clone https://github.com/Cameron27/small-k
cd small-k
```

### Build

The project can be build with Stack using the command:
```sh
./build.sh
```
This build process can take a few seconds and the kompiled directories are put in `./out/`.

### Run

If you wanted to run the Small program `example.sm` then you would use the command:
```sh
./run.sh example.sm
```
The `-o none` is a parameter for `krun` that suppresses printing the final K configuration.

### Tests

This project is dependant upon https://github.com/Cameron27/small-haskell for testing. To run the test, follow the instructions at https://github.com/Cameron27/small-haskell to build that project. The tests can then be run with:
```sh
./test.sh /path/to/small-haskell
```
If the path to the Haskell project is `../small-haskell/` then the path parameter can be ignored.