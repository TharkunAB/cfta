# Stored reconstruction does not commute with prior union normalization

The selected kernel gives a physical counterexample in the repaired Lean
constructor model. Both schedules use actual available source values. No
production source or Haskell source changes in this component.

## Initial construction

The source is an ordinary container with three children. Its initial inputs
are the available references uninterned 0 and uninterned 1. Empty Ready and
the actual source build derive Ready for the returned source heap.

The first child is the union of A and a raw unused Mu that captures the
first input. A has one leaf row with symbol 0 and full guard true. The
second child is the second input reference z. The third child is B, with
one leaf row with symbol 1 and full guard true. The replacement map sends
uninterned 0 to the actual stored B and leaves other references unchanged.
The kernel derives source availability and replacement availability.
It does not take a future execution, result, heap, or resource premise.

## Two exact schedules

1. Apply actual makeUnion to the original first two children. It flattens
   the inner union to [A, rawMu, z]. Reconstruct this normalized record.
   Smart reconstruction removes the unused Mu and returns B. The final
   mixed union has members [A, B, z].
2. Start at the exact heap returned by schedule 1. Reconstruct the original
   first two children in order. Reconstructing the inner union merges the
   ordinary A and B into one node AB. The final mixed union has [AB, z].

The source contains no forged records. The proof retains both exact done
outcomes and the full sequential heaps. Keeps retains Ready, record-table
growth, and issued-name growth at each stage. Both returned Values are
available in the exact final heap. Private literal equations identify the
complete Values, including entry keys, rows, guards, children, cached depth,
and free names. The public distinct_grouping theorem proves Value inequality.

The public same_open_observations theorem proves Same at every finite depth
and every common view. Thus full row fields, ordered child observations,
and exposed bare references agree despite the different union grouping.
This is stronger than comparison of symbols or cache identities alone.

## Scope

This refutes general physical commutation of stored reconstruction with
prior makeUnion normalization. It does not refute equality of the two
reconstructions of one selected Mu's stored body and ordinary probe. These
inputs are related by additional actual writer constraints. It establishes
no Haskell defect and no general language or outer-termination result.
No general mixed-union permutation law follows from this example.

## Validation

Selected printer-free kernel attempt 4 passes with an empty log. Selected
public attempt 1 contains two full signature and axiom pairs. It has all
eight required options, no printer omissions, and only the three standard
axioms. The small evaluator attempt 2 independently reports the same member
grouping and different returned references.

The first larger closed-source evaluator timed out after five minutes and
produced no result. Its source and raw diagnostics remain unselected.
Small evaluator attempt 1 and kernel attempts 1 and 3 retain elaboration
failures. Kernel attempt 2 passed but had an unused simp warning and is not
selected. Every run records memory.max and memory.high of 4294967296 bytes
and swap.max of zero. The largest peak across all retained runs is 328 MiB.
