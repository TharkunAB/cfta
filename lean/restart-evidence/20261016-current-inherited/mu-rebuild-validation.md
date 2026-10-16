# Current Mu-rebuild validation

Frozen at 2026-10-16 10:17 CEST. Source:
`lean/MicroCFTA/SourceCurrentAllocatedMuRebuild.lean` (172 lines).
SHA256:
`f11da978680f1ac7fb928583fda070f30b22cd391475f5a6f104eba24bc95d46`.

Direct pinned Lean passed at terminal 0 with no warnings in
`mu-rebuild-direct-2.log`. The first direct log retains two missing
import/open errors; no proof statement was weakened to fix them.

Focused command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedMuRebuild
```

`mu-rebuild-build-1.log` reports terminal 0 and 1,188 jobs. Only the
preexisting unused-input dependency warning appears. Live session 36075
was polled to terminal. The canonical slot was released to guard_inventory.

Direct public/kernel command:

```
LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-inherited/mu-rebuild-probes.lean
```

`mu-rebuild-probes-2.log` is terminal 0 with no warnings or errors. All
nine public theorem axiom checks and nine full signatures pass. Only
propext, Classical.choice, and Quot.sound appear; no sorryAx appears.
Eight named kernel integrations pass: original construction, raw edge,
actual optional binder, arbitrary finite checked observation, physical
Trace, exact independent language/free-list result, unchanged whole
checked state, and actual current raw binder graph retaining the WHOLE
Caller state with the exact cleanup result. The first probe log records
only a rewrite elaboration error in that external integration kernel;
the source remained frozen.

Raw logs, source text, probes, counts, and SHA256 manifest use the
`mu-rebuild-*` prefix. No compiled artifact remains in the evidence folder
or at the owned temporary output path. `current-mu-origin-boundary.md`
records the explicit initial ProbeHeap premise, current graph review,
and pending whole-local/caller transport.
