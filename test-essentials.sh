#!/bin/bash

for f in bin/genipaessentials-*
do
    parallel ./runPair.sh $f ::: benchmarks/sat50/*.cnf
done
