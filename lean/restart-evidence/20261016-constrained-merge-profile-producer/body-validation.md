# General merge body profile validation

Date: 2026-10-16 20:07 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryMergeProfileBody.lean`.
The source has 327 lines. Its SHA256 is `8f0331b691cee911ba8aebaef12739de208a76d3a75604936ca87e37f6ce1ed9`.
The evidence copy is byte-identical. The production source is frozen.

## Checks

- Final direct source check 2: terminal exit 0, no diagnostics.
- Parent canonical build: terminal exit 0, 1129 jobs. Parent confirmed the terminal result. `profile-body-build-1.log` contains the historical unused-input dependency warning. The new module has no diagnostics.
- Imported public checks: terminal exit 0. All 6 public declarations have an axiom probe and a full signature probe.
- Final imported integration checks 3: terminal exit 0. All 6 kernels have an axiom probe and a full signature probe.
- Final imported logs contain no warnings, errors, or `sorryAx`. The reported axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

Direct draft 1 retains four elaboration errors and one unused cost binder warning. Direct source check 2 fixes them. Kernel draft 1 retains a private-abbreviation simplification error. Kernel draft 2 passes five kernels. Final kernel check 3 adds the same-actual-body producer integration and passes all six. No production source changed after direct source check 2.

## Public local certificate

The six public endpoints are `small_certified`, `column_certified`, `large_certified`, `group_certified`, `root_certified`, and `body_certified`.

`body_certified clear top input before semantic costs available rows arity profile` proves the complete fixed-profile body certificate. Its result has `NodeShape (envelope rows (height input)) arity` and height at most `height input`. The initial profile permits arbitrary guards and equality classes. It excludes Mu, explicit union, and reference constructors throughout.

Small rows process actual child requests in order. Each request supplies its universal captured-original certificate. Ordered All₂ retains the actual child count. The raw edge constructor keeps the original full guard.

Columns select original values before normalization. Actual selection preserves their profile and cannot increase multiplicity. A retained singleton returns directly. Other ordinary retained columns run the literal ordinary union, then request that exact returned record at its returned heap. The union has at most squared input rows. `column_envelope` embeds its recursive result in the parent's envelope. The empty selected list still uses the literal union and request instructions.

Large groups process every original column before the Top edge constructor. Their output arity is bounded by the first original row's arity. Both threshold branches return no more rows than the original group. The final root flattens the exact ordered group results before normalized node construction. Canonicalization cannot add rows. Heights are derived from actual resident records and coherent constructor readback.

All intermediate heap readiness, costs, and availability come from actual primitive effects or the local recursive request contract. Profiles and actual counts accompany the returned records through subsequent effects. The proof does not recover complete child records from identities.

## Integration checks

1. Five literal rows choose the source column branch and return its singleton result.
2. Five rows with arbitrary guards and a shared source child list obtain the complete group profile and count certificate.
3. A resident five-row ordinary input obtains the full body certificate from initial facts. It supplies no successful body or result profile.
4. Ordered recursive child requests retain every original position, exact list length, and each child-relative height bound.
5. The empty-column branch keeps the ordinary union and recursive request. Its fixed profile is derived through the complete column certificate.
6. A supplied actual five-row body Run is interpreted by the general profile producer using this fixed-profile body certificate. It returns the profile, height bound, physical storage, and profile storage at the same actual heap and memo. The producer discharges every recursive request contract.

## Scope

This module proves local code certificates. It does not assert recursive execution completion by itself. Its recursive contract is the conjunction of the physical contract and the universal profile certificate. The separate actual Run/Call producer discharges that contract by graph induction.

The body uses the existing sequential MemoGraph. The allocated wrapper adds the actual Top equality-field allocation separately. The proof does not claim a GHC demand schedule, early lazy publication model, comparison allocation budget, or complete caller reservation bound.

No older source, Haskell, Audit, root document, or earlier evidence file was edited. This owner ran no Git or Lake command. Owned new text has one final newline and no blank line at EOF. Derived compiled objects remain outside the evidence directory.
