#!/bin/bash

for f in bin/ipasir-*
do
    parallel ./runPair.sh $f ::: benchmarks/incremental/*.xcnf
done
