#!/usr/bin/env python
#
# SAT instance generator for investigation of the block sensitivity problem
#
# Made by Madars Virza <madars@gmail.com> (c) 2009-2011
#
# This work is part of ``Sensitivity versus block sensitivity of
# Boolean functions'' (preprint at http://arxiv.org/abs/1008.0521)
#

# Version history:
# 2011-01-10: cleaned up internal version for the public release
# 

import operator
import os
import sys

MINIMAL_BLOCKS=False

# Variables with numbers 0..(2^n-1) will correspond to values of
# f(x_1, .., x_n).  We keep a special table of auxilarily variables
# and auxilarily clauses that will be shared between SAT instances for
# functions of size n, for example, the constraints describing tables
# { c_{i,j} }. Correspondance between human-readable representation of
# auxilarity variable name (say, c_{i,j}) and its DIMACS "name" will
# be kept in aux_vars. Prepare_aux and get_aux_vars knows a little
# about semantics of other functions. This behavior can be decoupled,
# but was not done to decrease the amount of code.

# Unfortunately the DIMACS numbering of variables is 1-based, which
# makes us to define the name of variable to equal the *number* of
# variable plus one. aux_vars translates between human-readable names
# of variables and DIMACS names for variables.

def name(i):
    """Returns DIMACS name for variable number i"""
    return i+1

aux_vars, last_aux_var, aux_clauses = {}, 0, []
def prepare_aux(n):
    """Initializes auxilarlily variables."""
    global aux_vars, last_aux_var, aux_clauses
    aux_vars = {"f": 2**n+1, "t": 2**n+2} # false, true
    last_aux_var = 2**n+2 # the name of last aux variable

    # demand false to take 0 and true to take 1
    aux_clauses = ["%d 0" % aux_vars["t"], "-%d 0" % aux_vars["f"]] 
    pass

def get_aux_var(w, i, j, aux='c'):
    """Gets the DIMACS name for auxilarly variable aux_{w,i,j}."""
    global aux_vars, last_aux_var
    
    # for each w variable c_{i,j} is actually aux_{w,i,j} with
    # appropriate semantics:
    if i < j and aux == 'c':
        return aux_vars["f"] 
    elif j == 0 and aux == 'c':
        return aux_vars["t"]
    else:
        if not aux_vars.get((aux,w,i,j)):
            last_aux_var += 1
            aux_vars[(aux,w,i,j)] = last_aux_var
        return aux_vars[(aux,w,i,j)]

def itakej(i, j):
    """Generator that takes j items from list i."""
    # this is esentially itertools.combinations(), but the latter is
    # only available in Python >= 2.6
    if len(i) < j:
        return
    elif j == 0:
        yield []
    else:
        for l in itakej(i[1:], j-1):
            yield i[0:1] + l
        for l in itakej(i[1:], j):
            yield l

def sensitivity_tables(n):
    """Generates sensitivity tables (i.e. tables { c_{i,j} } for each w)
    for a n variable function.

    We will build table { c_{i,j} } so that last row c_{n,1} ... c_{n,n}
    contains exactly k True's in first k positions (and everything
    else is set to False) iff exactly k of given variables are true.

    The table is built this way:
    c_{i,j} = (c_{i-1,j-1} && b_{i}) || (c_{i-1,j})
    c_{i,0} = True
    c_{i,i+1} = False
    
    To obtain the CNF we notice that:
    A = ((B && C) || D)
      <=>
    (!A || B || D) && (!A || C || D) && (A || ! B || ! C) && (A || ! D)

    (noticing can be done by BooleanConvert[Equivalent[A, (B && C) ||
    D], "CNF"] ;-))
    """
    global aux_clauses

    for w in xrange(2**n):
        for i in xrange(1, n+1):
            for j in xrange(1, i+1):
                A = get_aux_var(w, i, j)
                B = get_aux_var(w, i-1, j-1)
                C = name(w ^ (1<<(i-1))) # b_i = w^{i}
                D = get_aux_var(w, i-1, j)
                aux_clauses.append("%d %d %d 0" % (-A, B, D))
                aux_clauses.append("%d %d %d 0" % (-A, C, D))
                aux_clauses.append("%d %d %d 0" % (A, -B, -C))
                aux_clauses.append("%d %d 0" % (A, -D))

def sensitivity_less_than(n, k):
    """Returns a set of DIMACS clauses that means that n-degree
    function's sensitivity is less than k. We assume that aux_vars
    have already been defined.

    For variable a this means (!a && !a_{n,k}) || (a && a_{n,n+1-k})
    (if a is false then less than k of b_i's are true)

    (!A && !B) || (A && C) <=> (A || !B) && (!A || C)
    """
    if n < k:
        return []
    clauses = []
    for w in xrange(2**n):
        clauses.append("%d %d 0" % (name(w), -get_aux_var(w, n, k)))
        clauses.append("%d %d 0" % (-name(w), get_aux_var(w, n, n+1-k)))
    return clauses

def sensitive_on_blocks(blocklist):
    """Returns a formula with the following meaning: function is
    sensitive on blocks specified in blocklist on assigment 0....0 AND
    that the blocks cannot be further reduced (if MINIMAL_BLOCKS is
    set). Block numbers are 0-based"""
    def block_to_int(b):
        return reduce(operator.or_, (1<<z for z in b), 0)
    clauses = ["%d 0" % (-name(0),)]
    for block in blocklist:
        clauses.append("%d 0" % name(block_to_int(block)))
        if MINIMAL_BLOCKS:
            for k in xrange(1, len(block)):
                for subblock in itakej(block, k):
                    clauses.append("%d 0" % (-name(block_to_int(subblock)),))
    return clauses

def all_partitions(n, parts, maxpartsize):
    """Returns list of all partitions of `n` in `parts` parts, with
    maximum partition size being `maxpartsize`. The parts will be
    non-increasing."""
    if n <=0:
        return
    elif parts == 1 and n <= maxpartsize:
        yield [n]
    else:
        for part in xrange(1, maxpartsize+1):
            for remaining in all_partitions(n-part, parts-1, part):
                yield [part] + remaining

def filename(n, maxsens, partition):
    """Returns filename for n-argument function with s<=maxsens, which
    is sensitive on blocks of sizes in `partition'"""
    return "n%dms%dp%s" % (n, maxsens, "-".join(str(s) for s in partition))

if __name__ == '__main__':
    modulo, residue = int(sys.argv[2]), int(sys.argv[3])
    curres = 0
  
    for n in [int(sys.argv[1])]:
        prepare_aux(n)
        sensitivity_tables(n)
        for max_sens in xrange(1, n):
            sl = sensitivity_less_than(n, max_sens+1)
            for nn in xrange(1, n+1):
                for part_count in xrange(max_sens+1, nn+1): # nav jeegas njemt mazaak vai tikpat parts par part_count
                    for partition in all_partitions(nn, part_count, nn):
                        # skip set of blocks if the number of one blocks exceeds maximum sensitivity
                        if sum((1 if i==1 else 0) for i in partition)>max_sens:
                            continue
                        
                        curres = (curres + 1) % modulo
                        if curres != residue:
                            continue
                        
                        i = 0
                        blocks = []
                        for p in partition:
                            blocks.append(range(i, i+p))
                            i += p
                        
                        sb = sensitive_on_blocks(blocks)

                        fn = filename(n, max_sens, partition)

                        f = open("%s.cnf" % fn, "w")
                        
                        f.write("c %s\n" % fn)
                        f.write("p cnf %d %d\n" % (last_aux_var, len(sb)+len(sl)+len(aux_clauses)+len(opt)))
                        for it in [sb, sl, aux_clauses]:
                            for l in it:
                                f.write("%s\n" % l)
                        f.close()

                        # os.system("./cms %s.cnf > %s.rez" % (fn, fn))
