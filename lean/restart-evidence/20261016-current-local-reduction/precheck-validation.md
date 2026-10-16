# Warm checked allocated precheck

Date: 2026-10-16 09:46 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedPrecheck.lean`.
SHA256: `3f4f770754e70986a50381edcff959d99209e45b590a94af547bf8477ab5f28c`.
Length: 211 lines. Source frozen.

The focused pinned Lean 4.34.1 Lake build passed with 1319 jobs. The only
warning came from the preexisting unused `inputs` binding in
`InternedFreshOrdinaryClosedCompletion.lean:24`. The new module has no warning.
Raw output: `precheck-build-1.log`.

Direct probes passed with exit code 0. They check 13 public axiom dependencies,
13 public signatures, and eight kernel compositions. The kernel probes cover
resident-field completion, all native table and literal operation retention,
rejection of accepted joint obligations, live ordered class satisfaction,
empty equality meaning, retained earlier loads, fourth-memo correctness, and
unchanged global memo validity. `precheck-probes-1.log` contains no warning,
error, or `sorryAx`. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

The namespace is `MicroCFTA.SourceCurrentAllocatedPrecheck`. `state before
loaded inherited` advances the actual returned equality-operation cache at
the same heap. `state_native` proves equality of the whole native state,
including both memo tables and domain cache. `state_operations` identifies
the literal `PartialPrecheckAllocation.run` output cache.

`loaded_complete` derives a receipt from an actual current successful load,
normalized cached raw equalities, initial class readiness and inventory, and
inherited payload readiness. `complete` derives that load from `FieldAvailable`.
`resident_complete` obtains field availability from an actual resident edge
and the initial loaded-field heap invariant. None requires a future precheck
answer, final cache validity, whole input forest closedness, or cold machine.

The receipt derives actual run success, the literal source physical entry,
operation validity and growth, full physical effects, native extension,
current class readiness, and the same inventory admission. All branch facts
refer to the complete original source equality accessor, including equalities
extracted from positive guards. Residual guard acceptance implies accessor
satisfaction; no converse is claimed for residual guards.

The unchanged branch has two literal empty equality payloads. It does not
assert an unchanged operation cache: the preceding accessor can allocate.
The empty-children branch excludes every jointly satisfying own/inherited
payload and therefore every accepted full original guard under inherited
satisfaction. The classes branch derives the original physical records,
literal ordering, coherent ascending nontrivial tries, proper paths, and
exact equality meaning in the returned order.

This module does not model raw contradictory-constructor skipping, later
class Scan, fallback edits, checked edge acceptance, lazy GHC demand/CAF
forcing, pending operation publication, or native container representation.
Those source/runtime boundaries remain separate. No Haskell or older Lean
source changed.
