# Actual cache capacity and complete native Sized queries

Updated: 2026-10-14 22:43 CEST.
Proofs: `a9cae6f5`, `8dab9b3c`, and `d094c368`.
Source base: `7bfb69d1` (PR #129). All work remains local.

## Derived request bounds

`SourceRecursiveIntersectionNativeCapacity.Capacity bits machine` checks
the three actual source counters for native width `bits + 2`:

- The node counter is less than `2 ^ bits`.
- The raw domain counter is less than `2 ^ (bits + 1)`.
- The edge counter is at most `2 ^ (bits + 2)`.

The node bound reserves two tag bits and excludes the all-ones empty sentinel.
The domain proof includes the actual reserved-zero shift. A nonempty domain
has identity `raw.identity + 1`. Its identity stays below the signed first-key
limit. The empty domain has identity zero without a raw cache entry. Resident
edge records give raw identities below the edge supply. These facts derive
node and edge `KeySafe` from actual request provenance. No request-word safety
premise is supplied.

`CacheRanges` checks only caches at actual yielded prefixes of one native call.
It assumes no successful call, sufficient fuel, request provenance, or word
encoding law. It does not quantify over unrelated future heaps. Trace, body,
and continuation lemmas retain the same exact cache checks.

## Actual prefix proof

`SourceRecursiveIntersectionNativePrefixSplit.steps_bind_cases` splits an
actual prefix into a nonreturning inner body or an exact complete body followed
by an outer prefix. It retains step counts and shared caches.
`Steps.length_le_complete` bounds every other prefix by a known completed body.

`prefix_words` uses strong induction on the actual prefix length. It follows
every source effect, direct placeholder bypass, ready memo hit, and new native
node or edge body. Inside a body, the induction hypothesis derives current
word checks. After a body returns, shorter prefixes derive its full `Bounds`.
The existing checked correspondence then proves the completed memo's validity
and actual returned-record provenance. The proof continues from that exact
memo-completion cache. Neither whole-body completion nor prefix provenance is
supplied at the public theorem.

`wordRanges` derives the original `WordRanges` contract from `CacheRanges`,
initial source safety, body syntax, and valid native memos. `node_wordRanges`
derives source safety and body syntax for an actual ready node request.
`SourceFreshOrdinaryNativeCallback.complete_capacity` therefore derives finite
actual overlap callbacks, exact common-term Booleans, and the complete next-call
cache invariant from actual cache capacity.

## Ordered scans and complete Sized entry

`SourceShortCircuitScan.Ranges.transfer` retains the state invariant through
actual continuing callbacks. It does not demand a suffix after a decisive result.
`SourceFreshOrdinaryNativeKeyCapacity` uses resident finite input records to
derive operand provenance. Child, edge, and all-row resource checks then derive
the original ordered scan's word contract. A mismatched symbol or arity needs
no callback capacity. Actual caches pass through every reached call.

`SourceFreshOrdinaryNativeCompiler.CapacityRanges` retains empty, open, and
constrained precheck precedence. Only the actual ambiguity-scan branch checks
reached callback capacity. `ranges_of_capacity` derives the original word
contract. `complete_capacity` derives finite actual compilation and literal
reference compiler-result equality, including errors.

`SourceFreshOrdinaryCapacityNativeSized.complete` starts from actual closed
construction and normalized original annotations. Actual cold traversal derives
Ready, root scope, the exact finite map domain, resident and replayed rows,
declared children, raw child-key closure, and normalized row constraints.
Reached cache counters derive every native word check. No final row metadata,
rowwise normalization, native completion, product law, scan equality, or request
provenance is supplied.

Every accepted output has literal equality of all four optimized/reference
query fields, including signed inputs. One finite stable minimum prepass
supports every size. Each size has finite count/decoder evaluation, exact
distinct accepted terms, counts, and decoder order. The reference classes
equal that same sequence. Bounded prefixes are distinct and nondecreasing in
node count. Rank coverage and both global distinct-term inverse laws hold.
The earlier bounded query and position/replay theorems apply to the same actual
compiler execution.

## Physical root checks and next entry target

`SourceFreshOrdinaryNativeEntryPrecheck.check` follows the source's literal
`EmptyNode` case, then its `freeVars` check. Its lemmas prove exact empty,
open, and row-phase conditions. A recursion reference takes the open error
before any traversal or native callback.

`closed_empty_exact` proves that the cold adapter's `reference.isNone` flag
equals the actual constructor decision on closed roots. `reference_boundary`
shows why the adapter must retain that domain: an open physical reference
also encodes as `none`, but the actual compiler rejects it as open. This does
not refute the closed-root theorems or identify a Haskell runtime defect.
The source `automatonRows _ EmptyNode` also returns an empty map directly;
the singleton empty-state table remains an auxiliary cold readback certificate.

Next connect these root-only decisions to a staged public execution relation.
Empty and open roots must return without a cold table or native callback.
Only the nonempty closed branch may invoke the complete cold/native result.
Return a common query API or the exact source error so finite-key carriers
remain internal to the row phase. Derive the actual root decision from the
physical value. Do not supply an arbitrary `freeVariables` list or identify
every `reference = none` root with `EmptyNode`.

Cache capacity remains an explicit resource boundary. The theorem derives
word checks from concrete counters; it does not prove that arbitrary natural
caches fit a fixed native width. Normalized input annotations also remain an
input boundary. Public raw equality patterns do not normalize arbitrary values.
Concrete Haskell container extraction, lazy scheduling, and external solver
correctness retain their earlier boundaries. Preserve the optimized interned
core and all older proofs, fixtures, counterexamples, repairs, and marked drafts.

## Validation

The pinned Lean 4.34.1 aggregate build passes 1,542 jobs and checks dependencies
of 44,313 theorems. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Log: `/tmp/mcfta-capacity-entry-precheck-20261014-audit.log`.
The earlier capacity aggregate logs are
`/tmp/mcfta-native-capacity-words-20261014-audit.log` and
`/tmp/mcfta-capacity-native-sized-20261014-audit.log`.
Focused logs for each new component are saved in the current checkpoint.
No new warning remains. The old unused `inputs` warning remains.
No production Haskell code changed. The unchanged base already passed 645
source examples, five updated probes, and formatter checks. They were not
repeated for these Lean-only additions.
