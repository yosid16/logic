#!/bin/bash

tlimit=10m
fname=results/`basename $1`-`basename $2`.log
timeout $tlimit /usr/bin/time -f "wtime=%e" $1 $2 &> $fname
#echo $1 $2 $fname
