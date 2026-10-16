# Output compiler validation

Date: 2026-10-16 19:22 CEST.

## Frozen source

- OutputCode: 112 lines, SHA256 `58f0c4fb8884851d5f94ef5e8af76646b07b2970805e5da506f50e3ab87d75b2`.
- OutputNode: 142 lines, SHA256 `91aaec83674cd4dc2f836b242adc4761a24985609d37c264f9771cff7cf744e3`.
- OutputEdge: 225 lines, SHA256 `c2b1b9e055f9acd69f4d756a23cde1c060d2a04fea002871f6d9230a0eb96406`.

The source copies are byte-identical. No older proof, Haskell, Audit, or root document was edited. This owner ran no Git or Lake command.

## Checks

- OutputCode direct check 1: terminal exit 0, no diagnostics.
- OutputNode direct check 1: terminal exit 0, no diagnostics.
- OutputEdge direct checks 1 and 2: terminal exit 0, no diagnostics. Check 2 follows two corrected profile-specific comments.
- Parent canonical OutputCode: terminal exit 0, 1086 jobs.
- Parent canonical OutputNode: terminal exit 0, 1116 jobs in the ProfileBudget batch.
- Parent canonical OutputEdge: terminal exit 0, 1136 jobs in the producer batch. That batch also built OutputExecution and OutputFinite.
- Imported public probes: terminal exit 0. All 13 public declarations have an axiom probe and a full signature probe. Counts are 7 Code, 2 Node, and 4 Edge.
- Imported integration probes 3: terminal exit 0. All 6 kernels have an axiom probe and a full signature probe.
- The final public and kernel logs contain no warnings, errors, or `sorryAx`. Reported axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

The canonical logs retain only the historical unused-input dependency warning. Kernel draft logs 1 and 2 retain failed elaborations. Their failures are not validation evidence.

## Integration coverage

1. The actual closed-self compiler branch returns the original resident node profile.
2. The empty row join checks its literal Work return at the unchanged machine.
3. Accepted nullary child code derives the profile of the exact returned raw edge. Validity, Extension, and SemanticReady are derived from the current Work inputs.
4. The actual nullary sentinel has profile rows 0, arity 1, exact children `[Empty]`, and does not have profile rows 0, arity 0.
5. The compiler certificate admits the full guard and equality fields without an extra guard restriction.
6. Actual arity mismatch certifies the emitted sentinel at the checked returned state without a field-load premise.
