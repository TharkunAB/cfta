# Edit forecast review

Reviewed at 2026-10-17T11:16:24.391680+02:00.

The module defines a pure initial numeric envelope. It does not construct an Edit execution. It does not assume a future execution, future result profile, or callback law.

The record and captured forest count stay fixed. A stage joins the computed recursive Head profile, the constructor profile at the incoming scalar width, and the missing-slot Leaf profile for each token in the original record. The shared monotonicity theorem bounds either actual slot branch by that missing-slot profile. The constructor profile uses the same primitiveGrowth definition as EditFrame. Head profile and fuel also match EditFrame.

A successor level first fixes start = stageProfile entry and W = scalar start. It scans W rows. Each row scans W child plans at the preceding level and then reserves one stage. A final stage covers the enclosing constructor. The proofs compare component bounds and fixed scan counts. They do not derive widths from future returned values. The caller must derive actual original row and child counts from the causal incoming heap mass.

plan_child_return contains the entire child plan at its literal preceding scheduled profile. The kernel then uses plan_stage to bound stage(childEntry) by the final enclosing plan. This extra stage bound supplies Room for a reached Leaf. Entry <= final alone would not supply Room(stage(final)). No such stronger room premise is introduced.

The first kernel constructs a finite symbolic word width for an arbitrary plan. It derives all original token reservations, output profile domination, and the shared fuel ceiling for either slot branch. The second kernel does the same for an arbitrary selected child within the fixed row and child scan. Both retain the exact scheduled entry. Neither kernel evaluates a numeric majorant.

Actual supported Edit completion still belongs to the next composition. It must retain exact signed domains, prove recursive Head is Ordinary, and connect original list widths and syntax descent to the schedule. Cap alone does not imply closedness. A root editBelow [] is not HasLeaf, even though its domain condition can be vacuous. This module does not impose whole-forest closure or infer that missing property.

Validation: strict direct attempt 2 exited 0 with an empty log. Canonical target completed 1518 jobs. Its only warning is a replay from unchanged InternedFreshOrdinaryClosedCompletion.lean:24. Imported public probes contain all 58 declarations. The two schedule kernels also pass. All 60 complete axiom/signature pairs use only standard Lean axioms. The first strict attempt and first kernel attempt remain preserved with their diagnostics and exact sources.
