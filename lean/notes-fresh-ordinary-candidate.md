# Separate model for the ordinary-placeholder repair

Updated: 2026-10-13 16:44 CEST.

The source repair is committed locally as `e0e1b37`. It changes
`createMuDontCleanup` and `matchMu` together. The original source counterexample
and its executor remain preserved as baseline evidence. The original protocol's
general closed completion claim is false. Completion for the repaired protocol
is a new obligation.

`InternedFreshOrdinaryConstruction` retains the original syntax, ordinary
constructors, requests, record layout, and source execution order. It changes
the ordinary callback argument in a separate executor. The original executor
and `InternedClosedPendingBoundary` remain unchanged.

For the actual completed Depth result `d`, the candidate chooses

```
max d.depth (maximum (level + 1) for each free Unint level in d)
```

The empty maximum is zero. The arithmetic proof establishes that this is
the least level which retains the old depth bound and exceeds every free
ordinary level. The chosen ordinary name is absent from `d.free`. The
candidate retains `d.depth` when every free ordinary level is smaller.

`probeReadback` uses this same choice from the stored Depth probe. It returns
the exact stored Depth and ordinary components at those two arguments.
The source `matchMu` branch must use the stored Depth probe for this choice.
The actual stored body's depth need not equal the chosen ordinary level.

`InternedFreshOrdinaryExamples` checks the original open and closed pending
fixtures under the separate candidate. Kernel checking establishes
completion of the open case with its ordinary capture retained, and
completion of the closed case with depth one and no free names. The closed
observation also checks that some stored record's chosen ordinary level
differs from its body's depth. The build passes 273 jobs with Lean 4.34.1.
The closed computation uses a local two-million-heartbeat budget; the
kernel checks the resulting proof without native evaluation axioms.
The focused audit checks 9,723 theorem dependencies and permits only
`propext`, `Classical.choice`, and `Quot.sound`.
The log is `/tmp/mcfta-fresh-ordinary-audit.log`.

## Independent execution evidence

The repaired Python mirror completes both original failing cases. The open
case returns a raw Mu with depth one and free `Unint 1`. The closed marked
case returns a union with depth one and no free names. The baseline mirror
still stops at the exact previously checked pending keys. The old closed
level-change control returns empty under both policies.
The script and log are `/tmp/mcfta-fresh-ordinary-repair.py` and
`/tmp/mcfta-fresh-ordinary-repair.log`.

The source repair in `/tmp/mcfta-fresh-probe-20261013` changes constructor
choice and matcher readback together. Both independent closed reproductions
complete in 10–12 ms. The open reproduction and both completing controls
also pass. All 620 existing source examples pass. These native checks use
the Nix/cabal environment. The detailed report is
`/tmp/mcfta-fresh-probe-validation.md`.

A focused mirror search varies marker fields, marker placement in returned
and discarded branches, additional discarded computations, raw nesting,
ordinary-producing depth, and cleanup mode. All 320 systematic cases
complete with an increased evaluation budget. Another 2,512 structured
random cases complete. Neither run skips a case for resource limits or
finds a pending result. Logs:
`/tmp/mcfta-fresh-repair-search-wide.log` and
`/tmp/mcfta-fresh-repair-hidden-search.log`.

## Exact proof boundary

Freshness against returned free names does not cover every ordinary name
used by discarded computations. `InternedProducerPathBoundary` still
demonstrates that difference. The search above tests this concern but does
not prove it harmless. General closed completion and complete language preservation remain separate
obligations. Repaired cache facts, normalization, source origins, root profiles,
and free-name semantic heaps are now proved. See
[record facts](notes-fresh-ordinary-records.md) and
[free-name semantics](notes-fresh-ordinary-free-names.md).

Existing binder heap and callback proofs use the old ordinary name
`Unint d.depth`. They must be generalized to the chosen name or rederived
before they establish source correspondence for the repair. The new modules
now supply the repaired profile/free-name heaps and stored-probe readback. The natural
number chooser proof also leaves the source machine-integer range condition
explicit. No universal repair theorem follows from the fixture checks.
