CXX=g++
CC=gcc
CXXLIBS=$(shell pkg-config --libs sylvan)

COMMON_FLAGS := -O2 -g
SHARED_LIB_FLAGS=-shared -fPIC

CXXFLAGS=$(COMMON_FLAGS) --std=c++20 $(SHARED_LIB_FLAGS)
CFLAGS=$(COMMON_FLAGS) $(SHARED_LIB_FLAGS)

.PHONY := clean

lazy-tests: build/lazy-tests.o build/lazy.o build/base.o build/custom_leaf.o build/operations.o build/sylvan-extra.o build/pareto_set.o build/tfa_leaf.o build/rewrites.o build/bit_set.o build/bit_set_leaf.o build/algorithms.o
	$(CXX) -o $@ $^ $(CXXLIBS)

build/lazy-tests.o: src/lazy-tests.cpp
	$(CXX) -c $(CXXFLAGS) -I ./external -o $@ src/lazy-tests.cpp

shared-lib: build build/amaya-mtbdd.so

build/lazy.o: src/lazy.cpp include/lazy.hpp include/base.hpp include/pareto_set.h include/tfa_leaf.h include/vectors.h include/rewrites.h
	$(CXX) -c $(CXXFLAGS) src/lazy.cpp -o build/lazy.o

build/amaya-mtbdd.so: build/wrapper.o build/operations.o build/custom_leaf.o build/base.o build/lazy.o build/sylvan-extra.o build/tfa_leaf.o build/pareto_set.o build/rewrites.o build/bit_set_leaf.o build/algorithms.o
	$(CXX) $(CXXFLAGS) $(SHARED_LIB_FLAGS) -o $@ $^ $(CXXLIBS)

build/wrapper.o: src/wrapper.cpp include/wrapper.hpp include/operations.hpp include/base.hpp include/custom_leaf.hpp
	$(CXX) -c $(CXXFLAGS) src/wrapper.cpp -o build/wrapper.o

build/operations.o: src/operations.cpp include/operations.hpp include/base.hpp include/sylvan-extra.h
	$(CXX) -c $(CXXFLAGS) src/operations.cpp -o build/operations.o

build/custom_leaf.o: src/custom_leaf.cpp include/custom_leaf.hpp include/base.hpp
	$(CXX) -c $(CXXFLAGS) src/custom_leaf.cpp -o build/custom_leaf.o

build/base.o: src/base.cpp include/base.hpp
	$(CXX) -c $(CXXFLAGS) src/base.cpp -o build/base.o

build/vectors.o: src/vectors.cpp include/vectors.h
	$(CXX) -c $(CXXFLAGS) src/vectors.cpp -o build/vectors.o

build/pareto_set.o: include/base.hpp include/pareto_set.h src/pareto_set.cpp
	$(CXX) -c $(CXXFLAGS) src/pareto_set.cpp -o $@

build/rewrites.o: include/base.hpp include/rewrites.h include/lazy.hpp src/rewrites.cpp
	$(CXX) -c $(CXXFLAGS) src/rewrites.cpp -o $@

build/tfa_leaf.o: include/base.hpp include/tfa_leaf.h include/operations.hpp include/pareto_set.h src/tfa_leaf.cpp
	$(CXX) -c $(CXXFLAGS) src/tfa_leaf.cpp -o $@

build/bit_set.o: include/bit_set.hpp src/bit_set.cpp
	$(CXX) -c $(CXXFLAGS) src/bit_set.cpp -o $@

build/bit_set_leaf.o: src/bit_set_leaf.cpp include/bit_set.hpp
	$(CXX) -c $(CXXFLAGS) src/bit_set_leaf.cpp -o $@

build/algorithms.o: src/algorithms.cpp include/custom_leaf.hpp
	$(CXX) -c $(CXXFLAGS) src/algorithms.cpp -o $@

build/sylvan-extra.o: include/sylvan-extra.h src/sylvan-extra.c
	$(CC) -c $(CFLAGS) -o $@ src/sylvan-extra.c

build:
	-mkdir build

clean:
	rm -r build/* || true

build/test.o: src/test.cpp
	$(CXX) -c $(CXXFLAGS) src/test.cpp -o build/test.o

test: build/test.o build/wrapper.o build/operations.o build/custom_leaf.o build/base.o
	$(CXX) -o $@ $^ $(CXXLIBS)

