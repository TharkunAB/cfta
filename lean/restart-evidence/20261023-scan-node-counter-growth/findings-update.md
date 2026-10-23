## Node-counter growth through row cluster scans

Updated: 2026-10-23 19:12 CEST. Proof checkpoint: `27cebaf220`.
Start: `527a5cd981`. Imported main remains `794903b3f`.
Read `lean/notes-current-scan-node-counter-growth.md`.

The public outcomeState returns the complete Pair.State from each of the five Scan outcomes.
It requires no equality instance. Only the two existing equality instances occur on the theorems.
The step_mono and execute_mono theorems bound the input constructor node counter
by the counter in the SAME actual Scan step or finite execute outcome state.
Width, control, state and fuel are arbitrary. Yielded, done, failed, constraintError
and blocked outcomes are included. No validity, readiness, success or counter premise is added.
The four cluster/scan list cases retain their input state. Comparison uses the public
H37 bound at the same Pair.step inner control and state, and retains its actual after state.
Pair.done selects a conditional Scan control but keeps that state. No ID split is required.
Fuel induction uses only the actual yielded next control and full after state.
Earlier implementation and proof bodies are unchanged. Audit adds the one new module import.
The new counter composition through the SAME H23 chain and literal rebuild remains pending.
Fixed-source initial counter order and the new global-domain-history composition remain separate.
Earlier H23 conditional completion, domain-Trace and language results remain proved.
Complete upper resource bounds and full-pipeline Room/WordRanges, generated execution,
Mu/full pass, practical width, Haskell and solver correspondence, and convergence remain open.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.

The unchanged 80-line source passed its first strict check with a literal-empty log.
Its sole complete public-output job passed and retained 656026 raw bytes.
Audit passed with 3657 build jobs and 75584 theorem dependency checks.
It replayed one older unused-input warning. The new source has no warning.
Root and an independent reviewer read all three complete checked public TYPEs.
Raw TYPE byte identity is false, true and false in declaration order. All lexical identities are true.
Both raw hashes and canonical hashes remain retained. The accessor has no axioms.
The two theorem axiom sets contain only Classical.choice, Quot.sound and propext.
All twelve slices reconstruct the raw output. BODY checks were programmatic only.
The baseline contains 124005 files/modes, 3655 older Lean sources, 298 Haskell and 207 package files.
No Haskell repair is required. FINDINGS keeps the full external repair index FIRST.
H37 was pushed and remote-verified at `527a5cd981b6b406cf7078ac2fe96c288379afb7`.
This record precedes the H38 seal and push. It claims neither result.
Standing authorization permits Root to push formalize after verified local publication and seal.
