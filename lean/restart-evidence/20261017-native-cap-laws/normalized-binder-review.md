# Direct-union normalized binder producer

Validated 2026-10-17 03:15 CEST. Production source: `lean/MicroCFTA/SourceCurrentConstrainedCapNormalizedBinder.lean`, SHA-256 `29b80af9c041f73fd5fc002f7ad42819ac80f8d63913fda51b3a5a9851d6039c` (231 lines). No older production source changed.

## Produced family and public API

`body old entry node edges level outerLevel` is the literal stored root union `[reference old, node node edges level []]`. The ordinary alternative is closed. Its guards are unrestricted. Initial `Facts` and `Available` require this record to be an actual coherent resident input. These premises are not output or future execution laws.

- `callback old name ... state facts available reference`: actual stored substitution followed by actual root filtering returns the exact ordinary alternative. Its returned heap is exactly the heap from literal `makeUnion [reference name, ordinary]` at the callback entry. This theorem retains that union allocation even when filtering discards the union record. It permits legitimate warm union cache hits.
- `complete annotation bound pair ... state facts available bounded fresh`: constructs its own actual `maybeMu pair body state = done ordinary final`. It derives `Facts final`, record growth, issued-history extension, availability, and the original input cap at that exact final heap. It does not accept a completed optional-binder call, a callback oracle, a desired result cap, or a future native trace.
- `complete_replay`: constructs the same first completion, then proves `maybeMu pair body later = done ordinary later` for every later heap with record-table growth from its actual returned heap. It preserves the entire supplied later state. It does not assert `Facts later` without that separate premise.

The cap argument is an initial cap on the immutable ordinary alternative. The producer derives that the output is exactly that input record. The family includes nonhereditary ordinary guards, and permits hereditary recursive records in closed descendants. It does not require a whole-heap guard predicate.

## Initial freshness and exact state sequence

`fresh` states that `state.nodes.table (muKey ordinary ordinary) = none` at the INITIAL call entry. It does not refer to a post-probe cache or a future result. Both normalized probes return that same ordinary record, so their canonical Mu key is known before either probe executes.

Each actual callback first interns a union key with members `[reference name, ordinary]`. Root filtering then returns the existing ordinary value without more work. The private `union_keeps_mu` proves pointwise preservation of BOTH the identity table and the payload table at every Mu key through this union step. The two probe allocations therefore preserve the initial missing Mu key. After its literal reservation, the final body callback also preserves that reserved key and its missing payload.

The proof follows actual depth probe, selected fresh ordinary probe, Mu reservation, actual normalized body, first-writer payload publication, and smart cleanup. The fresh payload stores the exact ordinary body and both exact ordinary probes. Cleanup returns that body because it is closed. `SourceRecursiveIntersectionMaybeMu.verified` then derives all physical facts at the exact constructed return. No allocation or discarded probe state is replaced by the initial heap.

An arbitrary pre-existing warm Mu at this canonical key is outside `complete`'s premise. Coherent key readback alone does not relate an arbitrary stored Mu body to two nonhereditary probes. The replay theorem permits warm reuse only after the producer has established the actual completed return. This restriction remains explicit.

## Validation and constructive integration

Absolute-path strict direct compilation, with `-Dlinter.all=true` and the pinned Lean 4.34.1 executable, passed in `normalized-binder-direct-9.log` (exit 0, zero bytes). Root canonical compilation passed in `normalized-binder-build.log` (exit 0, 1003 jobs). The canonical log replays one old dependency warning in `InternedFreshOrdinaryClosedCompletion`; this new source has no diagnostics.

`normalized-binder-public.lean` checks all four public declarations with `#print axioms` and full explicit signatures. `normalized-binder-public-1.log` passed with four pairs and no diagnostics. Printing includes proofs, universes, deep terms, and ten million output steps.

`normalized-binder-kernels.lean` has one substantive imported theorem with NO premises. It constructs an edge with a false guard, its nullary ordinary parent, and the direct pair-reference union from the actual empty heap. It derives its own physical facts, available body, `Cap P 1`, nonhereditary annotation failure, and initial missing canonical Mu key. It invokes the new finite producer on that SAME actual body and heap. It obtains the exact original ordinary result, its physical facts and cap, then exact replay after arbitrary later growth. `normalized-binder-kernels-3.log` passed with one axiom/full-signature pair and no diagnostics. The Boolean guard predicate isolates the shared constructor algorithm; it is not a new concrete equality-allocator theorem or Haskell runtime test.

Every failed source and raw log is retained under its numbered name. Later successful checks do not relabel those failed attempts.

## Remaining boundary

This closes one actual normalized-binder producer family. It does not prove that every mixed native compiler body belongs to this family. Multiple alternatives, nested unions, and recurrence below ordinary layers need a stronger occurrence classification. Arbitrary warm mixed native cells also need a causal cap certificate before a general hit theorem can consume them. General mixed-cap native preservation, selected-class closure without hereditary leaf placement, general completion, and GHC lazy/pending correspondence remain open. No Haskell behavior defect was established or repaired here.
