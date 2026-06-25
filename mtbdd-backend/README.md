# MTBDD backend for the Amaya SMT solver
This repository holds the code implementing automata operations used in the Amaya SMT solver. 

## Building
The backend depends on the `Sylvan` BDD library which can be found [here](https://github.com/trolando/sylvan).
It is important to checkout the *version 1.5.0*, as the newer versions introduced breaking changes for which
some adaptations need to be made (in other words: not supported yet).

Steps to build `Sylvan`:
```sh
git clone git@github.com:trolando/sylvan.git
cd sylvan
git checkout v1.5.0
mkdir build
cd build
cmake -DBUILD_SHARED_LIBS=ON ..
make
make test
sudo make install
```

After `Sylvan` has been built and installed:
```
git clone git@github.com:MichalHe/amaya-mtbdd.git
cd amaya-mtbdd
make
ln -s <AMAYA_REPO>/amaya/amaya-mtbdd.so build/amaya-mtbdd.so
```

## How does it work
The code gets compiled into a shared object that is loaded by the Amaya solver using the `ctypes` python library. 

The interface currently is not very efficient as it typically requires often memory allocations to move data 
back and form between python and the C++ side. It is likely that this will be addressed in the future, but for 
the experimentation purposes it is sufficient.

## Known limitations
Due to the nature of the interface (many memory allocations) it is possible that the program will be leaking memory. This
is a subject of ongoing investigations, however, the process is slow (running valgrind to run the entire python process 
and searching for leaks).
