# cfta formal model

## Node-counter growth in pair comparison

Updated: 2026-10-23 17:56 CEST. Proof checkpoint: `39da661878`.
Start: `de085728eb`. Imported main remains `794903b3f`.
Read `lean/notes-current-pair-node-counter-growth.md`.

The public outcomeState returns the complete pair State from all five outcomes.
It requires no equality instance. The two counter theorems use only the existing instances.
They bound the input constructor node counter by the counter in the SAME actual
pair step or finite execute outcome state, for arbitrary states, controls, widths and fuel.
They cover yielded, done, failed, constraintError and blocked outcomes.
They have no validity, readiness, success, callback-bound or final-counter premise.
Memo call, demand, order and return phases retain the checked state.
The native phase uses H36 step_mono at the same body and checked state.
Fuel induction uses only the actual yielded next control and complete after state.
No earlier implementation or proof body, constructor order or counterexample changes.
Lifting this counter bound through Scan/H23, fixed-source initial counter order
and transport of the original global domain history remain separate targets.
Earlier H23 completion and language-preservation results remain proved under their premises.
Upper bounds, full-pipeline Room/WordRanges and complete resources, generated execution,
Mu/full pass, practical width, Haskell and solver correspondence, and convergence remain open.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.

The unchanged 96-line source passed its first strict check with an empty log.
The sole complete public output check passed.
The aggregate Audit passed with 3656 build jobs and 75572 theorem dependency checks.
It replayed one older unused-variable warning. The new source has no warning.
Root and an independent reviewer read all three complete checked public TYPEs.
Actual raw TYPE byte identity is false for the accessor and true for both theorems.
All three four-ASCII-whitespace lexical identities are true. Both raw hashes are retained.
The accessor has no axioms. The theorems use only the three allowed standard axioms.
Complete BODY retention and raw reconstruction were checked programmatically.
The baseline contains 122017 files/modes, 3654 older Lean sources,
298 Haskell files and 207 package files. No Haskell repair was needed.
FINDINGS keeps its external Haskell repair index FIRST.
H36 was pushed and remote-verified at `de085728ebe1e905ae339eaba8d26348126e5ada`.
This record precedes the H37 seal and push. It claims neither result.
Standing authorization permits pushing formalize after the verified local seal.

