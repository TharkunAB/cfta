# Inherited normalization and actual prefix progress

Updated: 2026-10-17 22:01 CEST. Proof checkpoint: `85fd098d`.
Starting published checkpoint: `eb18c2a5`. Source main remains `c0cc8a05`.

The whole-library target remains termination and the specified result for
each public operation on valid supported inputs. General recursive outer
progress and repeated-pass convergence remain the largest mathematical gap.
This checkpoint closes the normalization invariant needed by the local
empty-own progress argument. It does not prove general outer termination.

## Established results

- Actual source normalization is idempotent in literal class and path order.
  The proof derives the fixed point from the completed array normalizer.
  It uses the actual preparation, completion, and congruence phases.
- WellFormed physical payloads have exact readback from their class paths.
  This includes arbitrary class order and repeated records. Valid ascending
  tries determine the complete physical representation. No whole-class
  normalization premise is needed for this readback law.
- The actual source sort orders its output under a transitive relation and
  branch-choice correctness. The proof retains the fused merge workers,
  ascending and descending natural runs, and special run-reduction cases.
  The Record.paths specialization needs no sorted-input premise.
- Actual trie descent preserves active, canonical, consistent, disjoint,
  and saturation-closed classes. Actual sorting then gives exact ordered
  normalization fixedness for the complete descended payload.
- Actual allocated normalization and combination produce FixedPayload.
  Actual indexed descent preserves it together with Ready and valid storage.
  The full inherited accessor/prefix/descent sequence derives it from initial
  operation validity, inherited readiness, and field availability. The caller
  supplies no Fixed input, empty-own field, or future completed call.
- For an initially normalized inherited value, an actual empty-own accessor
  and combiner retain that same complete value. Nonempty inherited descent
  after this prefix strictly lowers path height and changes its identity.
  A separate initial theorem constructs the normalized input from raw classes.

The main actual-operation endpoints are
`SourceCurrentEqualityOperationFixed.inherited_prefix` and `prefix_descend`.
They cover contradiction, empty and nonempty live payloads, and cold and warm
caches. Contradiction retains its separate case. The two-empty shortcut
returns a fixed empty payload. Other live combinations run normalization.
Standalone descent requires a fixed input. The prefix theorem derives it.

`SourceCurrentNormalizedInheritedPrefix.normalized` constructs the initial
normalization and proves the actual empty-own prefix and strict descent.
The arbitrary-own prefix theorem establishes fixedness, not a decreasing
measure. A nonempty local field can add paths before indexed descent.

## Constructed checks

The normalization cases include unsorted overlaps, repeated classes,
trivial-class removal, and generated suffix equalities. Physical readback
retains repeated ordered records. A coherent nonascending trie changes on
readback, which checks the need for the ascending premise.

The source-sort cases exercise mixed natural runs, tied values, five-, six-,
and seven-run reductions, and repeated complete physical records. Descent
cases include an actual reversal of retained class order and generated
suffix closure followed by empty descent. They invoke the general theorem.

One initial prefix case allocates the empty field, normalizes raw classes,
and checks the same complete inherited value through cold and warm prefixes.
Actual descent at the prefix return separates same-value node request keys.
The warm prefix retains the full operation state.

Another case starts with Ready but unsaturated overlapping classes
[[0,0],[0,1]] and [[0,1],[0,2]]. It explicitly proves that the initial payload
is not Fixed. The actual prefix merges the classes. Actual descent at index
0 produces [[0],[1],[2]]. The general prefix_descend theorem supplies the
fixed child payload. Later prefix, combination, and descent calls are exact
warm hits that retain the complete operation state.

## Remaining proof

The next general outer obligation is causal progress when returned rows add
nonempty local classes. Construct an order for actual child requests that
respects physical memo keys, then exclude every active ancestor key.
The relevant transition is the actual parent return, inherited prefix,
indexed descent, and recursive node call. The new normalization invariant
does not supply that order. Ordinary height and maximum constrained depth
remain insufficient. Repeated-pass convergence also remains open.

Retained-Mu body/ordinary writer correspondence, smart cleanup, frontend
adapters, concrete runtime adapters, and complete public Haskell pipelines
remain open. Keep those boundaries separate from this equality-operation
result. Preserve the optimized interned core and all earlier proof targets.

## Validation and external handoff

The pinned full Audit passes 3133 jobs and 68560 dependency checks.
All seven new strict source logs are empty. Thirty-three public checks and
eleven constructed checks pass in fourteen groups. Seven component manifests
check 363 hash entries. Only propext, Classical.choice, and Quot.sound occur.

All checks use verified 4 GiB MemoryMax, 4 GiB MemoryHigh, and zero swap.
The Audit peak is at most 363 MiB. Its completion timestamp shares a second
with a public check; the evidence uses the larger of both recorded peaks as
the Audit upper bound. All failed snapshots and logs remain unchanged in
`restart-evidence/20261017-inherited-normalization/`.

No Haskell behavior patch or new production defect is added. FINDINGS keeps
the external repair registry first. Field-pool repair `b9219b9e` remains
merged and validated in source `c0cc8a05`. Record each later repair with its
failure, reproducer, paths, commit, checks, and upstream status.
