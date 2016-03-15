#!/bin/bash

(
  while read n
  do
    echo "$n $(./test/ifgen $n > test/if.c && compcertSSA/ccomp -stdlib compcertSSA/runtime -ssa on -c test/if.c | egrep "Cytron  |Braun  " | awk '{print $NF}' | tr '\n' ' ')"
  done
) > ifplot_with_cytron.data
