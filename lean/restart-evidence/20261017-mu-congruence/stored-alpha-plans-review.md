# Stored alpha plans review

Final production: `lean/MicroCFTA/SourceCurrentStoredAlphaPlans.lean`.
SHA-256: `d22bfde6346a17a652969742af9483e3cc928dedec66088686a31f834d7d540c`.

The pure mutual relations compare two different stored values. `Alpha`
retains a closed left capture by literal value equality. An open left value
requires an open right value and the same constructor. Reference leaves
compare their lexical resolved values. Nodes retain full row symbols and
guards, edge order, and child order. Unions retain member order. An open Mu
binds its respective original interned name to the same arbitrary Value
argument on both sides. The relation contains no execution equation.

The three plan theorems use two independently covered and available capture
contexts in one coherent source heap. Their local value and name lengths
match. They derive Equivalent, ManyEquivalent, and EdgesEquivalent for the
complete existing encoded plans. `execute_exact` uses each value's own
leaves and the original two replacement environments. It proves equality of
full repaired outcomes at any common current heap. The source heap can be
earlier than the current heap. No current semantic invariant, replacement
availability, completion, output equality, finite Cap, or shallow-preparation
premise is required. The source availability facts justify captured lookups.

The relation is deliberately ordered and structural. It does not identify
arbitrary normalized row permutations, duplicate removal, union flattening,
or an open raw Mu with its erased body. It is not claimed for arbitrary
actual callback outputs. A producer from actual callback histories, including
general warm selected winners, remains open. General retained-Mu fusion and
whole outer completion remain separate obligations.

Validation:

- Direct4 executes its immutable absolute snapshot with all linters. Its raw
  log is empty. Canonical1 builds the single target successfully (175 jobs).
- Public1 checks all seven public definitions/theorems with complete explicit
  signatures, full proof printing, and axiom printing. No output is omitted.
- Kernel3 is an empty-log strict check. It builds an actual closed source from
  empty tables. The outer Mu and its nested inner Mu both use their locals.
  The stored outer body and ordinary probe are physically distinct. The
  fixture proves their Alpha relation for EVERY common replacement directly
  from its finite constructor structure. The inner Mu clause proves the
  relation for EVERY common argument. A closed leaf also exercises the exact
  opaque-capture branch. Only then does execute_exact derive full outcome
  equality at every common heap. No desired execution equality supplies the
  relation proof.
- Kernels-public2 prints the complete constructive theorem and its axioms.
  Selected declarations use only propext, Classical.choice, and Quot.sound.
- Every run reads memory.max and memory.high as 4294967296 and memory.swap.max
  as 0. The largest observed peak is 342 MiB.

Direct attempts1-3 contain elaboration errors and remain preserved. Kernel1
contains a missing import and an unfinished binder proof. Kernel2 and its
public1 run have zero exit status but an unreachable test tactic warning;
these are not selected as final evidence. Kernel3 and kernels-public2 remove
that unused test tactic. All raw sources and logs remain unchanged. No old
source, Audit file, Haskell file, or frozen evidence file was changed.
