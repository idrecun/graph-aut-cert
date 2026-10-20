# Nullstellensatz certificate generator for graph automorphism groups

This repository contains the accompanying artifacts for the manuscript titled
_An algorithmic construction of Nullstellensatz certificates for graph
automorphism groups_.

The implementation consists of three parts: the solver, the prover, and the
verifier. The solver implements a modification of the McKay-Piperno algorithm
for computing the generators of the automorphism group of a graph. The prover
implements the construction of the certificate based on the input graph and the
solver's output. The verifier independently checks the certificate given the
input graph and claimed automorphism group generators.

## Building and running

The executables can be built using the `make` command from the `src/`
directory.

Run the solver by calling `solve <input_graph> <output_automorphisms>` with
optional flags `-s <stats_file>` for outputting JSON statistics and `-l
<vertex_limit>` for limiting the number of vertices in the input graph. The
input graph is expected to be in the DIMACS format for undirected graphs.

Run the prover by calling `prove <input_graph> <input_automorphisms>
<output_certificate>` with optional flags `-v` for verbose output, `-s
<stats_file>` for outputting JSON statistics, `-m <buffer_limit>` for limiting
the memory buffer usage (in bytes), `-g <vertex_limit>` for limiting the number
of vertices in the input graph, and `--in-memory` for building the unpruned
certificate in-memory rather than utilizing the disk directly.

Run the verifier by calling `verify <input_certificate> <input_graph>
<input_automorphisms> <stats_file>`. On success, the verifier outputs `OK` and
exits with code zero. Otherwise, the verifier prints the error message and exits
with a non-zero code.

It is expected that the same input graph is used for all three calls, as well
as that the automorphisms used are exactly the ones that were output by the
solver.

## Results

The raw results of the experiments are available in the JSON format in
`results/`. The input graphs are available
[here](https://pallini.di.uniroma1.it/library/undirected_dim.zip). The exact
setup used for the experiments is described in the manuscript.
