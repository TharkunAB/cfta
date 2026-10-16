# Contextual physical native cache validation

Checked on 2026-10-16, Europe/Stockholm. Source frozen after the focused build and public probe.

- Source: `lean/MicroCFTA/SourceCurrentAllocatedNativeContextualPhysicalCache.lean`.
- SHA256: `c4f93b35a2ebc8e457aa5d41108227086187d389a7d327d602a7a93e55f43262` (167 lines).
- Focused build: terminal 0, 1063 jobs. The only warning is the existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion`.
- Direct public probe: terminal 0. Twelve public axiom reports, twelve printed public signatures, and eight kernel examples pass. All reports use only `propext` and `Quot.sound`.
- The final kernel example derives the literal empty-input NodeLaw independently, starts the actual typed node cell, finishes it, then recovers that law from an actual warm lookup and demand. Seven earlier examples check the exact suspended/evaluating/returned phases, warm operations, and separate handle counts.

## Exact commands

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeContextualPhysicalCache
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-recursive/contextual-physical-cache-probe.lean
```

The exact terminal outputs are `contextual-physical-cache-build.log` and `contextual-physical-cache-probe.log` in this directory. The probe and source snapshot remain beside this note.

## Contracts

`initial_valid`, `advance`, `lookupNode`, `lookupEdge`, `demandNode`, and `demandEdge` preserve paired physical validity and Contextual. Actual growth needs Kernel.Valid at the returned machine and its physical Extension. No result language or Produced receipt occurs in these lifecycle premises.

`node_started` and `edge_started` consume literal actual lookup and evaluate-demand equations. Physical key coherence derives captured request equality. Their conclusions retain both invariants and the exact original evaluating cell.

`node_observed_ready` and `edge_observed_ready` consume literal actual lookup and ready-demand equations. They derive the requested NodeLaw or EdgeLaw, Contextual at the actual returned state, returned-state equality with the selected state, and result availability or residency. They use PhysicalCache.Valid, not the stronger historical Provenance.Valid.

`finishNode` and `finishEdge` require the literal evaluating cell, returned physical availability or residency, and a separately proved local law for that exact request and result. They preserve both invariants. The local semantic law remains an explicit obligation for the joint recursive proof. This component does not derive that law, assume whole-body completion, or assert the desired root law.

All laws retain the fixed InputMeaning, RankedInput, actual request domain, and original operand premises from ContextCache. This component does not prove result closedness, general contextual completion, GHC forcing/publication, concurrent cache behavior, or machine-key capacity. No old proof or Haskell file was edited. No Git operation or aggregate build was run by this worker.
