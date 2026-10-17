# Structural mass and stored-encoding bounds

The two owned production sources are frozen:

- `InternedValueMass.lean`, 208 lines, SHA-256
  `ea2d4e567fdede7d481d5c1819813c8e5f64aa68d8773d6fdb0599f3b5f5c628`.
- `InternedStoredEncodingMass.lean`, 155 lines, SHA-256
  `0710561fe583c113a1c4f95da0dcb6af44f30b32bf6641abcd607b74d63e070d`.

## Metric

`value`, `edge`, `values`, and `edges` count structural constructors. Empty and
reference values have mass one. Ordinary and union values add one to their row
or member-list mass. A Mu adds one to the sum of its stored body, depth probe,
and ordinary probe masses. An edge adds one to its child-list mass. A list has
mass zero at nil and adds one plus the head and tail masses at cons.

The metric ignores keys, identity magnitudes, cached depth, cached free names,
symbols, and guards. It is not a byte count, allocation count, or runtime count.
All Mu payloads are counted. The encoder itself traverses only its stored body;
including both probes gives a conservative complete-payload measure for later
cache-result bounds.

Append, filtered-list, length-plus-sum, membership, and strict child/probe descent
lemmas follow the literal structure. Strict mass descent here does not prove
recursive native termination. A native source transition can revisit an equal
request without descending through a structural child.

The four `*_le_sizeOf` theorems explicitly take the caller's `SizeOf Symbol` and
`SizeOf Guard` instances. They compare the same generated value/edge/list SizeOf
instances with this metadata-free mass. No silent default-zero field instance
is substituted for the caller's instances.

## Encoding theorem

`encode_bound context locals node` proves both full Fresh budgets plus two are
at most `2 * 3 ^ value node`. It permits arbitrary lexical contexts and local
name lists. `encodeMany_bound` and `encodeEdges_bound` use the corresponding list
masses. Closed values use the exact captured-variable shortcut. Open ordinary
and union values retain every encoded row or member. Open Mu uses the exact
nested binder plan with its own local reference.

The shifted bound fits the full binder recurrence:
`(3 * cost + 4) + 2 = 3 * (cost + 2)`. One mass layer pays the factor three.
List cons layers also cover ordered sums and raw edge work. This is an upper
bound for the complete repaired constructor schedule, not a binder-free model.
No Facts, availability, no-open-Mu preparation, normalization-success callback,
or successful execution premise appears in these pure encoding bounds.

`execute_charges` and `unfold_charges` lift this result to the actual local charge
functions. `execute_bound` and `unfold_bound` bound each literal outcome counter
plus two by its initial counter plus the power potential. They apply to normal
and pending outcomes and any replacement environment. They require no size bound
on replacements. They do not establish semantic validity for arbitrary malformed
replacement values or guarantee completion from an arbitrary cache.

## Validation

Canonical `canonical-value-mass-1.log` passed 107 jobs. Canonical
`canonical-encoding-mass-1.log` passed 176 jobs. Final standalone strict logs are
empty. Failed source snapshots and logs remain present. The first mass attempt
used the wrong working directory. The next exposed only equation reduction and
filter proof details. The first encoding attempt omitted the actual reference
lookup equation from its simplification. No older production file was changed.

All 24 mass and seven encoding public declarations have imported explicit full
signatures and axiom reports. Final public logs have no diagnostics. The only
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Two imported integration kernels passed:

1. `initial_payload_bound` uses actual available recorded input in an initial
   source and its successful source payload SizeOf sum. It derives mass from that
   initial sum under the caller's SizeOf instances, then derives actual local
   execute and unfold stopping-counter bounds for any current heap and replacement
   function. No result or future mass bound is supplied.
2. `constructed_nested_unfold` constructs its own raw source with an open nested
   Mu and a captured intersection reference. It proves that the actual input is
   not `PreparedWithoutMu`, constructs its own successful repaired unfolding, and
   derives output availability and both mass-based counter bounds at that return.

A separate executable check returns masses four and six. Large identities,
reference names, cached depth, and guard/symbol fields do not change the metric.
Adding an ordinary row payload inside a stored probe increases it. This check
confirms that mass remains executable rather than using runtime SizeOf.

## Remaining scope

This component bounds full local stored encoding from a complete initial value
mass and links that mass to successful initial source payload sums. It does not
produce a bound for every generated native result, derive whole-query initial
headroom, count arbitrary instruction steps, or prove whole-library Haskell
correspondence. Causal cache-result mass production and initial caller composition
remain separate proof obligations.
