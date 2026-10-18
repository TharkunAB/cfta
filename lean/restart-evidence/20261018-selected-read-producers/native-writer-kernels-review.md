# Distinct cold native writer integration

Frozen on 2026-10-18 at 05:26 CEST.

This component adds one constructed proof. It does not edit production.
The production dependency is `SourceCurrentNativeAdmissionWriter`, whose
public `node_written` theorem was checked by the root component.

## Actual source and execution

`NativeAdmissionWriterCheck.distinct_recursive_writer` has no theorem
inputs. It builds a closed source from the empty interner. The captured
left value is an ordinary pair node with a raw Mu child. That Mu body has
a finite base row and a repeat-self row. The captured right value is an
ordinary pair node with a different raw Mu child. That Mu body has the
same finite base row and a distinct right-tag row. Both binders use the
literal raw-Mu flag. The right raw Mu is retained even though its local
binder is unused. The theorem proves both stored Mu shapes and distinct
complete operand references.

Actual covered equality-field allocations and the completed source build
derive initial strong physical `Good`, loaded fields and semantic heap.
The exact native tables start empty. `History.initial` derives the causal
history without a returned writer premise. Actual source-child selection
derives operand availability; concrete cached fields derive closedness.
All node, edge and finite-domain headroom inequalities are checked at the
initial state with `bits = 128` and native key width 130. This is the
explicit Lean numeric-width model. It is not a claim that this headroom
fits the host Haskell word width.

The fixture evaluates the literal empty-domain native request with fuel
128. It proves a nonempty actual returned value, more than one native
node cell, and at least one edge cell. Distinct ordinary operand roots
force the cold ordinary branch; the differing child Mu values then reach
the recursive native branch. This is not a root self-query fixture.

The proof invokes `node_written` on that exact actual completion and
those derived initial facts. Its result supplies final causal history,
strong physical validity, heap growth, the checked native trace and an
exact returned node cell for the complete original request. The same
handle carries `NativeWriterReadyRetention.Written`, including the
captured request, actual compileNode body and protected finish provenance.
No future trace, completed graph, semantic Reads, result relation or
historical writer law is a theorem input. The public theorem aliases its
checked private proof with the same full statement.

## Boundaries

The result tests one cold completed execution. It does not add a warm
scenario or establish completion at a universal initial fuel. It does not
compare retained Mu reconstruction schedules or prove a language law.
The production theorem still requires initial exact-key memo validity,
closed available operands, causal history and numeric headroom. Weak
physical residency alone does not imply those exact-key facts.

## Validation and retained attempts

Attempt 1 uses a larger source and 512 admission bits at recursion limit
30000. It reports only recursion-depth errors while checking headroom and
literal execution. Its complete raw source, log and receipts remain.
Attempt 2 simplifies the two Mu bodies, uses 128 admission bits and
recursion limit 100000, and passes with an actual zero-byte raw log.
The result still exercises cold ordinary and recursive branches.

`native-writer-kernels-public-1` is the selected constructed group. Its
source contains all eight explicit print/linter options and one complete
signature/proof/axiom triple. It prints no omitted terms, diagnostics or
printer failures and uses only standard axioms. Root dependency public
group `native-writer-public-1` is separately pinned and checked; it adds
no owned public declarations. Root dependency strict1 has a zero-byte log;
canonical1 passes 1506 jobs with the unchanged old dependency warning.
All selected executions have effective 4 GiB maximum, 4 GiB high and zero
swap. The verifier checks exact source, log, metadata and readback hashes.

The frozen `native-key` component remains byte-identical. This package
uses only the new `native-writer-kernels-*` prefix. Root production,
root direct/canonical/public probes, old evidence, Audit, Haskell,
authority documents and Git state were not changed.
