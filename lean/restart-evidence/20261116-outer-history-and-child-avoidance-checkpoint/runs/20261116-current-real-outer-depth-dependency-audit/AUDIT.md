# Outer depth dependency audit

Status: READ-ONLY audit. No compilation or proof credit. No source repair is indicated by the checked headers.

The source owner SHA256 is unchanged from the candidate base: `b5ac50c040b628920a02e12766f54a1508f3cc1ff3c9de049648633415cb8331`.
The full depth header is byte-identical to frozen `a2251c0a`. The expand header
is byte-identical to `b24c7612`. All source pins are in `SOURCE-PINS.sha256`.

## Dependency applications

The parked call passes the original config and resource IH, then the structural
IH, original caller/cache/Packet/resource facts, original selection, and held
facts. Its actual prefix receipt is the final explicit argument. This matches
`real_parked_restart_held_fragment_history` header `48f3356b`.

The narrowed call passes the same config and both IHs. Its actual narrowed
receipt precedes the held facts. This matches
`real_right_prefix_prepared_held_history` header `ae970078`.
The resulting prepared-child expression retains the exact original caller,
queries, candidate cache, seven work-budget arguments, and callback closure.
The local split distinguishes actual missing preparation from an actual folded
result. It does not assert that every preparation succeeds.

The Nat induction keeps all config parameters fixed. Its predecessor IH is the
exact existing `RealEagerHeldFragmentHistoryAtDepth` predicate at that predecessor.
It still quantifies every caller, cache, held class, seed, and original work
budget. The resource IH comes from the existing checked
`real_eager_emitted_complete_at_every_depth (bits := bits)`. It is not a new
caller premise. The zero case reuses checked
`real_held_fragment_history_depth_zero`.

## Seven actual prefix branches

The branch order matches `SharedPreparedRecursiveChildPolicy.resumeWithNarrow`.

| Branch | Actual emitted result | Candidate treatment |
| --- | --- | --- |
| Parked, retained cache, empty restart list | `[]` | Empty membership elimination |
| Parked, retained cache, singleton restart | Exact smaller-depth resume emissions | Parked companion |
| Narrowed, empty action list | `[]` | Empty membership elimination |
| Narrowed, singleton true callback | `[]` | Empty membership elimination |
| Narrowed, retained cache, singleton false callback, no ordinary shortcut | Actual preparation result emissions | Right-prefix companion |
| Other narrowed observations | `[]` from selected stop | Empty membership elimination |
| All other prefix observations | `[]` from selected stop | Empty membership elimination |

The two continuing branches retain the complete actual emitted list. A later
stop does not remove earlier emissions. The other five branches are literal
empty-output runtime branches. Their native endpoint values are not used as an
enum-cache transition receipt.

## Original 906 target

The 146-line candidate does not declare the public original 906 theorem. It
proves the stronger private full-depth history predicate if it passes Lean.
The final public projection is still required.

No additional semantic premise is needed for that projection. For each output,
use the resulting history's `isolated` and `protectedHeld` fields. Its third
clause follows from the EXISTING exact public producer:

`EnumerationDischargeHistory.HeldFragmentHistory.pending_target_avoids`

in `SourcePruningEnumerationOpaqueSuffixIsolation.lean:329`, with arguments
`held heldHandle before.core output.cache.core packet.safe history`.
Its conclusion has the exact original pending slot, representative, full
fragment, and final SameClass relation from the 906 target. It excludes an old
expanded origin by using the retained old-class receipt and original Packet
safety. It does not identify targets from equal tries.

All original source/root, full emitted lists, budgets, and held native read
qualifications remain intact. This audit found no semantic scope or dependency
argument mismatch. Lean may still expose elaboration failures. The original
public 906 theorem and the one compatible finite accepted completion remain
unproved by this audit.
