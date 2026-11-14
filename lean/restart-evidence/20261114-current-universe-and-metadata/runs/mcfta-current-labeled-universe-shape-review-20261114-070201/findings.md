Source review only. No counterexample was found to the frozen no-Mu-or-one-resident-native-Mu target. The exact source rules exclude the proposed cleanup failure for the current allTypes expression. The corresponding labeled same-build callback-shape and first-occurrence theorems remain UNPROVED. No compiler, live source edit, Git action, board write, or Haskell action occurred.

1. The returned body and the returned universe have different tags.

SourceSynthesisTypeSyntax.allTypesBody always contains arrowType top (.var 0) (.var 0), followed by four rigid variable leaves and the actual catalog rows. This holds even when CurrentContext.constructorCatalog is empty. CurrentContext computes that catalog from escaped current constructors and last-binding query types. ordinarySymbols maps each name to (name, .top), keeps every child and guard, and retains the binder. The map is injective on names by its first projection.

During a real callback at name, .var 0 returns .reference name. The arrow marker has no children and cannot be removed by the Empty-child rule. The arrow therefore has the nonempty children [marker, .reference name, .reference name]. Its edge survives. Every catalog row has only copies of that same nonempty reference. Every alternative returns an ordinary node. makeUnion uses its ordinary-node fast path and combines their edges. Canonical deduplication retains the arrow row, and childFree retains exactly [name]. withoutSelfReference changes only a top-level union containing a bare self member. The normalized body here is an ordinary node, so it is unchanged.

The existing String theorem UniverseBody.callback_node proves this exact shape at an arbitrary coherent incoming state with an available local name: callback body [] name state = done (node entry edges 0 [name]) final. It is not limited to an empty catalog or a cold state. Its labeled current counterpart is specified in next-header.txt. That counterpart has not been proved in this packet.

2. Cleanup cannot erase a Mu with that actual body shape.

request wraps the completed body in Value.mu before finish applies cleanup. The first cleanup branch requires the reserved interned self name to be absent from body.free. It is present because body.free = [self]. The second branch requires body.referenceOf = ref self. Its tag is node, so that equality is false. The returned universe remains the exact raw Mu record. Its free list is [] because Value.free for Mu filters the self name from body.free.

CleanupRetainsUniverseMu.lean contains only the small generic cleanup equation for this node shape. It is UNCOMPILED. It does not assume or establish that a particular actual callback has the shape. The historical String finish_shaped_mu theorem already uses this same calculation. The labeled callback proof must supply the actual shape from the same build.

3. A reservation is not a placeholder Mu payload.

On a request miss, request first updates nodes with Cache.intern. It leaves nodeRecords unchanged while the actual interned callback runs. Only after that callback completes does it publish the complete candidate Mu through keepFirst. A hit with no nodeRecords payload is pending. The allTypes body is binder-free, so neither probe nor the actual body callback can request another binder. Ordinary makeNode and makeUnion work cannot introduce a Mu record. The existing cold-probe proofs derive exactly this NoNewMu property and use coverage/coherence to exclude a pending Mu key. These derivations still need transport to the actual labeled first-call prefix.

The Depth and ordinary placeholder REFERENCES remain in ordinary probe nodes and in the stored Mu's probe fields. They are not additional Value.mu records. The target retains those complete fields. It must not confuse placeholder references with additional binder owners.

4. A dead outer branch can retain the universe, but this does not contradict the target.

Use this actual current source input:

    lib = { libraryGroups := [], libraryArgumentOnly := [],
            libraryAvoid := [], libraryEncoding := .firstOrder }
    query = { queryArguments := [], queryGoal := .tCons "Int" [] }
    signed = 2

Its current catalog is [("Int", 0)]. Let E = node [], U = allTypes top [("Int", 0)], and G = CurrentContext.typeNode query.queryGoal. Reducing the actual row algorithms gives:

    A = application U (union [E, E]) (union [E, E, E])
    whole = ofType (union [A]) G

In the same labeled root build, G executes first. A then executes U before its other children, because application stores U at child zero and buildMany evaluates every child in source order. The function and argument unions both return Empty. makeNode removes the application edge for its Empty children. The candidate union and filter consequently return Empty. The previously published universe Mu remains in nodeRecords because all later operations preserve records.

This source reduction is not a compiler evaluation. It exposes the exact case that a formal first-occurrence argument must cover. It disproves a proposed strengthening that requires the root result to be Mu or requires the universe to remain reachable from the root. The frozen target makes neither demand: it requires Available heap U, closedness, replay, and uniqueness of Mu records in the original heap. Cached availability is independent of root reachability. If no source atom executes at all, the original no-Mu branch remains necessary.

5. The header remains plausible; the missing proof has a precise boundary.

Apply the checked current-source OverUniverse law to the same accepted root. Decompose that same successful labeled build to extract its first executed atom, including atoms in branches later removed. Derive the incoming Facts, coverage, absence of previous Mu payloads, and actual reservation availability from the preceding ordinary execution. Prove next-header.txt for that actual labeled callback and derive the fresh Mu readback and closedness. Subsequent source atoms have the same expression and [] environment. Existing InternedFreshOrdinaryReplay.build_replay then preserves their complete returned Mu value and performs no new allocation after the actual first completion and actual heap growth.

The frozen header quantifies uniqueness only in the original source heap. Its later-heap clause asks only replay of this U. A later heap may contain other Mu records. The existing replay theorem requires validity of the original call's incoming heap, derived from the actual prefix; it does not require an additional validity gate on every later heap.

No separate String-only cold construction may be used to choose or identify the current labeled owner. No new callback or supplied universe is needed. The review supports keeping the target header unchanged while proving the labeled callback shape and the actual first-occurrence trace.

All prior packets remain untouched. prior-packet-pins.json inventories them. source-pins.json and source-excerpts.txt pin the reviewed definitions. This packet contains no claimed new verified theorem.
