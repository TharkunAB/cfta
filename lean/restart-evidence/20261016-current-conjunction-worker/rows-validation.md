# Current conjunction row workers: completion, stability, and actual receipts

All three new proof sources are frozen. Their exact hashes and counts are in `rows-validation.json`.

## Validation

Pinned Lean 4.34.1 direct checks passed without warnings. Canonical Completion passed with 1069 jobs. The Stability and allocated wrapper batch passed with 1148 jobs. Actual passed with 1195 jobs. All processes returned exit 0 and are closed. Only the preexisting unused-input dependency warning remains in canonical logs.

All 28 public axiom reports and 29 full public signature checks passed. Seven external integration kernels and seven kernel signature checks passed. The 35 final axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. Final public/kernel logs contain no errors, warnings, or `sorryAx`. Earlier failed logs remain as diagnostic evidence.

## Completion and stability

Completion derives stable projection/read bounds for actual Exposures, Projections, ClassRequirements, Requirements, Tuple, Tuples, and Rows graphs. Every sufficient larger pair retains the exact output, constructor heap, and equality-operation cache. `rows_complete` and `rows_stable` expose the same endpoint. `stable_uniform` derives one shared upper bound.

Stability proves direct successful projection monotonicity from actual lower-worker control. Completed exposure replay is the only exposure stability primitive. The public row pipeline endpoints derive larger-bound success without semantic readiness or future callback assumptions. `rows_done_unique` identifies the complete physical return across incomparable bound pairs.

## Actual graph and physical endpoints

Actual reconstructs successful exposure/projection/class graphs with exact equality-cache retention. Standalone Requirements and Tuple reconstruction carry explicit SameArity. The worker does not check this property. Whole `rows_graph done` has no physical premise: it derives SameArity from the literal matching tuple filter before reconstructing the complete graph. Contradictory tuple reconstruction uses the exact accessor fold and returned allocation cache. Errors and missing fields do not become successful graphs.

`rows_finite nodes before ready available closed probes` constructs an actual finite graph from legitimate initial physical invariants. It returns Effects, RowsReady, ProbeHeap, and literal StableRun. `rows_verified ready available closed probes done` aligns the supplied literal return with that constructed graph by unconditional success uniqueness. It returns the same physical effects and requirement readiness. Neither endpoint accepts a completed future row callback or an output law.

## Integration kernels

The kernels verify contradiction before projection at zero bounds, the explicit standalone arity scope without an invented source check, repeated projection-job occurrences, uniform execution derived from initial invariants, a generated requirement starting the next finite row worker with derived readiness, source matching tuples reconstructed without physical input assumptions, and complete heap/equality equality across incomparable successful bound pairs.

The generated-requirement kernel derives the next input residency and closedness from the first actual RowsReady. It derives the next Ready and ProbeHeap from the first physical effects. It supplies no future readiness, completed row graph, or desired semantic callback.

## Scope

The row worker completes the chosen finite serial exposure/projection schedule. This does not establish Haskell lazy demand order. In particular, exposing every operand does not prove that an early empty operand permits the host to skip later reads. Logical global memo receipts, concrete host table execution, external solvers, runtime publication, and general outer-caller termination remain separate boundaries.

Only the three new proof modules and assigned evidence were written. No older proof, Haskell source, Audit file, restart authority, or Git state was changed. No Haskell bug or repair was introduced in this task.
