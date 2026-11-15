# Actual native entry at a common continuation

Status: UNCOMPILED CANDIDATE. No Lean proof credit.
Root supplied base: `513474ffd`. No compiler, live source, Git, board,
Haskell, or `/tmp` operation was used.

## Proposed receipt

The only public theorem is
`MicroCFTA.SourceCurrentNativeEnterCommonOperand.enter_prefix_common_operands`.
It consumes physical validity at the actual entry and one checked `Trace`
which starts with the literal `.enter domain left right first second next`.
The trace has exactly `fuel + 1` yielded instructions. It ends at the
supplied actual control and full checked state.

The proof obtains both complete operands and the old domain from the first
instruction's existing physical input check. No operand availability,
future extension, future model, result contract, or source inventory is an
additional premise. The native step determines the exact allocated domain,
actual next control, and full intermediate checked state. Its heap and
operation cache stay equal to their entry values.

A private 16-line induction composes the existing actual `step_valid` and
`step_extension` theorems. It derives physical validity and machine extension
from the checked suffix. It adds no execution or history datatype. The
public proof uses that extension to retain BOTH complete operands and the
exact allocated domain at the same actual continuation heap.

For either literal operand, closedness plus its actual control identity
allows a closed available candidate at that common heap to be identified
with the full operand. Their prefix heights are equal. This invokes the
existing `closed_identity_injective` producer. It does not select an
arbitrary value with the same numeric ID.

Instantiate one operand with the literal original stored Mu value and the
other with the full entered pattern. The theorem covers both operand
orders. It does not identify a Mu value from an atom marker.

## Exact existing producers and why this is not a duplicate

- `SourceRecursiveIntersectionNative.enter_step` already gives the exact
  native entry transition. It takes the full operands as arguments.
- `SourceRecursiveIntersectionKernel.entered` already gives allocation
  validity, extension, and the new full `Domain` invariant. It takes the
  current operand availability and old domain as premises.
- `SourceCurrentAllocatedRecursivePrefixCode.enter_next` preserves its local
  code certificate through the entry. It takes that certificate as a premise.
- `Kernel.Extension.available` and `Kernel.Domain.grows` transport values
  and domains. They take an extension as a premise.
- `SourceSynthesisUniverseMixedDescendantFreshness.closed_identity_injective`
  identifies the SAME closed complete records at ONE coherent heap.
- `mixed_entry_strict_descendant_fresh` already derives identity and seen-pair
  separation below one literal mixed entry. It takes original pattern
  availability and an extension to the later machine as premises.

The new receipt connects the actual entry instruction, its physical input
check, the exact checked suffix, and common-heap record identity in one
statement. It derives the availability and extension used by these existing
producers. It does not replace or copy their proofs.

## Source admission and remaining recursive-history obligation

`SourceCurrentNativeKeyAdmission.node_prefix` derives a checked `Trace`,
`Good`, and field checks for an actual raw prefix from initial closed
available operands and the ORIGINAL source width/headroom assumptions.
The new receipt takes a local segment of this already-derived trace. It
adds no stronger top-level caller contract.

`SourceCurrentNativeOptionalChildOrigin.Origin` already recovers a queried
request, its complete left and right values, a real compiler entry, operand
identity equations, exact `compileMu` step, and entered child trace from an
actual optional site. `SourceCurrentNativeRequestSourceScope.optional`
adds fixed-input `NodeScope` and domain inventory membership. These are
existing exact producers and must be reused.

A raw `.enter` instruction does NOT check that `first` and `second` equal
the control identities of its operands. The new receipt does not assert
that claim. The actual `compileMu` origin supplies those equations. The
closed candidate equality uses the control identity of the literal full
operand, rather than trusting the two numeric constructor arguments.

`SourceCurrentAllocatedNativeDomainTrace.CodeEntered` and its allocation
trace retain the extended structural KEY and cache sequence. `binder`
retains full Mu values while non-Mu operands add no binding. The key has
only their identity pair in `seen`. Thus key or inventory membership alone
does not recover the full non-Mu pattern or its prefix height.

The next missing producer is a SAME-execution decomposition for each reached
nonempty-domain recursive request: recover the particular earlier actual
Mu/pattern entry, its full closed pattern, both real identity equations,
exact entered domain, and the actual control descent which bounds the
current operand by that ORIGINAL pattern height. The existing optional-site
owner theorem proves such an origin at optional sites. It is not a theorem
that every later recursive request has the required mixed-entry origin.
After the entry and common suffix are identified, this new receipt supplies
the physical availability and complete-record identity part. It does not
prove that global request-to-entry origin or the height descent relation.

## Full objective retained

The full same-root finite accepted-completion goal is unchanged. This module
constructs no finite assignment. It proves no compatibility of removed
buckets, all historical obligations, supported native domains, residuals,
aliases, and the original emitted readback. It does not prove noStop,
arbitrary supplied-fuel completion, runtime correspondence, or Haskell
correctness. Outputs before a later stop retain their original obligations.
No Haskell defect or fix was established.

## Validation

`PROBE.lean` contains one exact `#print axioms` probe and one `#check`.
Root owns dependency preparation, strict compilation, axiom review, and
publication. No failed local attempt exists because no compiler was run.
`PUBLIC-HEADER.lean.txt` retains the full proposed public header.
`SOURCE-PINS.json` records the inspected live source hashes and ranges.
