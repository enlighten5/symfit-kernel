#!/bin/bash

# DKIMG="sym_dev"

# lightweight env for running symfit
# map local folders and compile
DKIMG="system-mode-sym"
# DKIMG="sym_dev"

docker run --rm -ti --ulimit core=0 \
            -v $PWD:/workdir        \
            $DKIMG /bin/bash
#  -v /data/zhenxiao/aixcc/testvirtme/challenge-001-exemplar-source:/challenge-001-exemplar-source \

# -v /data/zhenxiao/fuzzbench_seeds/:/fuzzbench_seeds \
            # -v /data/zhenxiao/fuzzbench_programs/:/fuzzbench_programs \
            # -v /data/zhenxiao/magma_experiment:/magma_experiment \