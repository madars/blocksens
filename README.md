blocksens --a SAT instance generator for investigating the sensitivity vs block sensitivity problem
===================================================================================================

The code here implements the search for a Boolean function with maximal separation between its sensitivity and block sensitivity. The number of all Boolean functions on `n` variables is `2^{2^n}`, but this code was able to search up until `n=12` by using a reduction to Boolean satisfiability problem and state-of-the-art SAT solvers. (This was in 2010, so probably improvements in SAT solvers and chip technology will let one search even further.)

The approach is described in our paper "Sensitivity versus block sensitivity of Boolean functions" ([Journal version](http://dx.doi.org/10.1016/j.ipl.2011.02.001), [arXiv pre-print](http://arxiv.org/abs/1008.0521)). Our paper attained a new separation of `bs(f) = 1/2 s^2(f) + 1/2 s(f)`.

We conjectured the separation to be optimal. This conjecture was later shown to be false by Ambainis and Sun, who constructed a sequence of functions `f` for which `bs(f) = 2/3 s^2(f) - 1/3 s(f)` ([ECCC](http://eccc.hpi-web.de/report/2011/116/)).

BibTeX
======
```
@article{Virza11,
title = "Sensitivity versus block sensitivity of Boolean functions",
author = "Madars Virza",
journal = "Information Processing Letters",
volume = "111",
number = "9",
pages = "433 - 435",
year = "2011",
issn = "0020-0190",
doi = "http://dx.doi.org/10.1016/j.ipl.2011.02.001",
}
```
