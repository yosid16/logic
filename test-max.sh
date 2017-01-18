#!/bin/bash

for f in bin/genipamax-*
do
    parallel ./runPair.sh $f ::: benchmarks/pmaxsat/*.wcnf
done
