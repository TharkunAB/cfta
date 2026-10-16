# Current inherited-prefix validation

Frozen at 2026-10-16 10:08 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedInheritedPrefix.lean`.
SHA256: `277ef3ea1688684e9ee45d0d6b99feaccc4469995eda42937bb89459dce1e1e6`.
Source length: 196 lines.

## Exact API and premises

Namespace: `MicroCFTA.SourceCurrentAllocatedInheritedPrefix`.

`run original inherited operations` returns an exact
`Except String (Option EqValue) × Operations`. Inherited contradiction
returns `ok (some contradiction)` with the same operation state before
any own accessor. A live inherited value executes the current accessor.
An error or missing field retains that accessor's actual returned state.
A present own value enters `combine inherited own` at that state.
Combination errors and returned states are retained. The combination is
not repeated for each child.

`state before original inherited` uses `advancePhysical` with the original
heap and literal `run.2`. `state_native` proves equality of the WHOLE native
state. `state_operations` exposes the literal operation return.
`state_contradiction` proves equality of the WHOLE checked state.

`Receipt formulas solver inventory original inherited before combined`
contains the actual successful output, native and operation equalities,
operation validity/growth, combined-value readiness, full current Ready,
the same inventory At, physical Effects, machine Extension, and exact
independent equality satisfaction. It states

```
Sat term combined.payload <->
  Sat term inherited.payload /\
  GuardReadback.Sat term (sourceEqualities original)
```

`contradiction formulas solver inventory original before ready admitted`
constructs this receipt with inherited and combined contradiction. It
needs no field, load, child, or inherited-value readiness premise.

`finite formulas solver inventory original inherited before ready
admitted field inheritedReady` derives a combined value and Receipt.
The field is CURRENT `FieldAvailable before.operations original` and
inheritedReady refers to CURRENT `before.operations.constraints`.
`resident_finite formulas solver inventory edge inherited before ready
admitted resident inheritedReady` derives the field from the actual
returned edge's residency and Ready.good.fields.

`Receipt.guard_satisfied receipt term accepted inheritedSat` supplies the
actual combined payload's satisfaction. Acceptance uses the independent
complete `PCSGuard.holds`, including the original residual guard. Existing
`PCSGuard.own_sat` derives the own-accessor obligations; no desired guard
or result law is a premise. No public declaration needs a DecidableEq
typeclass parameter.

## Source correspondence and limits

The order matches `Equality/Operations.hs:93–96` and the inherited-first
short circuit at `Equality/Constraint.hs:449–453`. It uses the actual
returned raw constraint. In particular, the sentinel from the checked
parent supplies Top and `[Empty]`; the caller must not reuse the rejected
original fields. The current FieldAvailable receipt derives its load.

The implementation preserves the caller's equality interner, completed
combination table, descent table, both native memo families, the domain
cache, and constructor heap. It uses neither the local precheck nor a
cold machine. Physical allocation effects derive field retention and
all final invariants. No future state, completed recursive callback,
whole-forest closedness, Top-coverage, or universal conjoin premise occurs.

This is an actual finite allocation prefix. It makes no recursive child
call. Indexed descent, outer caller completion, the separate outer and
reduced-edge memo wrappers, runtime pending publication, GHC forcing,
machine identity capacity, and native mutable-container correspondence
remain separate. The chosen resident accessor/combine schedule does not
establish a GHC evaluation-order theorem.

## Validation

Direct source command:

```
LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedInheritedPrefix.lean -o /tmp/SourceCurrentAllocatedInheritedPrefix.olean
```

`prefix-direct-1.log`: terminal 0, first attempt, no warning. The temporary
compiled artifact was removed after canonical compilation and probes.

Focused canonical command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedInheritedPrefix
```

`prefix-build-1.log`: terminal 0, 1,320 jobs. Build session 34432 was polled
to terminal completion. Only the preexisting unused-input dependency
warning appeared. The canonical slot was released to guard_inventory.

Public and integration command:

```
LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-inherited/prefix-probes.lean
```

`prefix-probes-1.log`: terminal 0, no warnings/errors. All 14 public
declaration axiom checks and 14 complete signatures pass. These cover the
11 theorems, two functions, and Receipt structure. Only propext,
Classical.choice, and Quot.sound occur. No sorryAx occurs.

Ten named kernel compositions pass: raw contradiction skips an arbitrary
own field; error retention; missing-field retention; no-field warm
contradiction receipt; exact native tables/domains/heap; residency-derived
load; full-guard and inherited satisfaction; actual indexed descent with
same-cache readiness and child satisfaction; combined-contradiction
exclusion; and the checked returned Top/[Empty] sentinel integration.

Raw source, logs, probes, machine-readable counts, and SHA256 manifest are
stored under the `prefix-*` evidence names. No old proof source, Haskell,
Audit, documentation, or Git state was edited.
