#!/bin/bash

ANALYSIS=$1
BENCHMARKS=$2

declare -a dirs
dirs=(`ls $BENCHMARKS`)

if [ "$ANALYSIS" == "monolithic" ]
then 
FLAGS=" --havoc --unwind 5 --32 --inline"
else
FLAGS=" --havoc --unwind 5 --32 --spurious-check ${ANALYSIS}"
fi

EXECPATH=../src/summarizer/summarizer

for filename  in `ls ${dirs[@]}`;
do
echo "Running *${ANALYSIS}* analysis on $filename"
echo "timeout 900 ${EXECPATH} ${FLAGS} $filename > ${filename}_${ANALYSIS}.log"
timeout 900 ${EXECPATH} ${FLAGS} $filename > ${filename}_${ANALYSIS}.log
done

