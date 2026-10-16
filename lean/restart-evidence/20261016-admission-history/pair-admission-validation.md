# Actual entered pair admission

Frozen source: `lean/MicroCFTA/SourceCurrentAllocatedNativePairAdmission.lean`.
The source has 157 lines. SHA256:
`2a0221ba9257ddadac067e86e552f9ba2f498a20c88753986a389e0b9e9c8a12`.

Only this new proof module and its evidence files were written. No older
proof source, Haskell source, Audit, documentation, or Git metadata was
changed. The root owns pull, baseline preservation, and aggregate checking.

## Contracts and source correspondence

The module derives the admission of the names and pairs in the actual
recursive intersection domain. It does not derive execution-wide cache
admission or a result language.

* `identity_input` reads the actual physical identity of a value. A
  successful read derives `inputOf value ≠ .empty` and equality with the
  semantic input identity. It needs no supplied Original or nonempty
  premise. `physical_name_covered` combines this with actual input admission.
* `name_covered` covers the identity of an admitted nonempty input.
  `pair_covered` retains both names under the source's independent canonical
  `(min first second, max first second)` ordering.
* `empty_seen` discharges the actual constant empty domain.
  `restrict_seen` retains remaining pairs. `extend_seen` proves coverage of
  the new pair and all old pairs by the actual `extend_seen` membership law.
* `bindings_covered` derives admission of the literal Mu binding identities.
  It inspects `Environment.bindings := binder left ++ binder right`.
  Non-Mu operands add no free-map binding.
* `entered_seen` reads the structural key returned by the actual
  `Environment.enter cache domain left right first second`. It derives
  `SeenCovered` from old seen coverage, admitted operand inputs, and the two
  actual successful physical identity equations.
* `entered_names` derives `NameCovered` for the actual entered free-map
  names. Old covered names are retained; new names come from literal Mu
  operands. The first/second parameters need not satisfy identity equations
  for this endpoint because they affect only the seen pair, not free names.
* `request_entered_seen` consumes parent `NodeInputs` and parent
  `SeenCovered`, plus actual successful identity reads and cache validity.
  It derives coverage of the exact entered child domain.
  `request_entered_names` is the corresponding free-name wrapper.

The generic name/seen endpoints work for any finite input interface and
physical symbol/guard types. Only the two NodeInputs wrappers use the
existing concrete FullSyntax source specialization.

The source-domain schedule is already modeled by
`SourceRecursiveIntersectionEnvironment.enter` and
`SourceRecursiveIntersectionDomain.extend`. This module uses the proved
actual constructor key equation
`SourceRecursiveIntersectionSchedule.entered_key`; it does not substitute
a desired entered key. `extend_seen` gives exact inserted-or-old membership
after sorted duplicate elimination. Old seen coverage is an explicit
inductive invariant, not a result-law assumption.

## Validation

Direct pinned command before taking the canonical slot:

```text
env LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedNativePairAdmission.lean
```

Final direct result: **PASS, exit 0, no warnings**.
Log: `pair-admission-direct-2.log`.
The first log retains the repaired tactic-block comma parsing error.

Canonical command after the root released the build slot:

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativePairAdmission
```

Result: **PASS, 1065 jobs, exit 0**. Only the preexisting
`InternedFreshOrdinaryClosedCompletion.inputs` warning was replayed. The
new source has no warning. Raw log: `pair-admission-build.log`.

Public and kernel command:

```text
env LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-admission-history/pair-admission-publicprobes.lean
```

Result: **PASS, exit 0, no warnings**. Raw final log:
`pair-admission-publicprobes-2.log`. Twelve public axiom reports use only
`propext` and `Quot.sound`; twelve complete public signatures are printed.
All twelve kernel examples pass. The first probe log is a development
failure, not validation evidence.

The kernel fixture uses actual fresh construction of a raw Mu and an
ordinary leaf. Their identities are 1 and 2. It derives admission from the
actual common source inventory. Two actual domain entries check empty
coverage, reversed operand canonical ordering, old pair retention, new
pair coverage, literal Mu binding-name coverage, domain-cache counters
`1 → 2`, and an exact repeated entry with unchanged cache/result.

## Remaining scope

Old seen and free-name coverage and current operand admission remain
explicit input invariants. The new pair's coverage is derived from those
operands and their literal identity reads. Cache validity supports actual
domain key readback. No physical- or contextual-cache validity is treated
as a substitute for admission.

Recursive NodeInputs body, union, reference, and row-child closure belongs
to the separate RequestAdmission module. Causal preservation through
actual execution, new returned-cell admission, and generated query-history
soundness remain separate integration steps. Runtime GHC publication,
container correspondence, and machine capacity remain explicit boundaries.
No Haskell defect or repair was found or made in this task.
