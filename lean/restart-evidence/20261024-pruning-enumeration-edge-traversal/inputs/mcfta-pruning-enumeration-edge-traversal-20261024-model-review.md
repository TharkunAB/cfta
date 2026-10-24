# Independent edge-traversal body and model review

Review cut: 2026-10-24 11:30:42 CEST. Verdict: SOURCE_ONLY_MODEL_SCOPE_CLEAR for the retained246-line first body and251-line strict2 body identified below. No mathematical/model/scope correction is requested. This verdict is not a compiler-pass claim: both observed strict attempts failed and remain retained. A later corrected body needs its exact delta correlated before final acceptance.

I authored the frozen declarations and inventories. Root authored all executable definitions and proof bodies. This review is independent of those bodies; it does not claim an independent review of my own declarations. Guard's separate full declaration review precedes the Root exact body gate. I read every line of the original246-line body, the complete25-line retained patch, and the changed strict2 sites. I checked that the retained patch reconstructs the251-line strict2 snapshot exactly and that all14 frozen literal fragments remain exact single occurrences. The83-file frozen payload set and its byte/hash pins remain exact. No old owner or current source was changed.

## Actual operation and state

runStaged matches the captured list. An absent head returns pure None at the current state. A present childAction executes before recursion on the actual tail. The returned fragment is consed only through the tail's Option.map. Therefore an earlier reject or Except error precedes later absence, earlier allocation/write effects persist on later None, and the worker has no preflight, rollback or recomputation. The definition uses existing EnumerateM/List/Except behavior. It adds no carrier, failure tag or callback law.

prepare matches existing EdgePrefix.prepare once and executes its captured prefixAction once. It passes packet.2.1 directly to runStaged. A None child result returns pure None without recordResidual. Only Some fragments constructs the node with packet.1 and invokes recordResidual on packet.2.2. Native projection absence stays the OUTER Option; inner unsupported, List rejection and Except errors remain distinct. The full constraint and actual returned fragment are retained at residual insertion.

The helper's only recursion proof is the reviewed proper-tail induction. It introduces actual before/realized/aligned and three native input predicates after induction. A supported head uses prepareChild_complete to derive its real action, actual middle and invariants. The IH is applied only to rest at that SAME middle, with actual restricted tail predicates. The two Success observations share the same actual after: the complete worker returns None or Some, and the take-stop worker returns its ordered completed-prefix holes at that after. The latter is a proof certificate, not a second runtime call in prepare. Counter grows by stop, including zero and first-unsupported cases; no arbitrary replacement state or whole-list counter is substituted.

The strict2 absent proof uses only inventoried constructor cases. Empty contradicts genuine nonempty; reference contradicts closedness; node/union/Mu reduce the same terminal Boolean before encoding. Its explicit cases replace broad simp_all without a new premise, local have, helper, Eq instance or result law. The other retained patch line adds rfl after List.map_map in stagedSame. This is definitional composition reduction, not a changed staged list.

Main child availability follows from parentAvailable.children and the SAME selected edge's flatMap membership. Closure follows from node_children_closed on ready.semantic.1.normal.facts and parentClosed. Nonempty follows from resident_live on ready.semantic.1.normal.live for the SAME parent and actual selected edge; an Empty child violates its any-false fact. No desired-success/nonterminal/child-output premise or second exposure is supplied. The helper map equals the exact captured prefix map through stagedSame; its actual start is suspendedState tries.length before, not a reconstructed counter-only state.

The main result retains actual childrenAfter and the exact final state. None keeps childrenAfter and records no parent residual. Some with no residual also keeps it. Some with a residual prepends exactly the complete constraint and same symbol/children fragment to obligations. Existing modify_success/pure/bind facts construct the corresponding action success. These updates retain counter and values, hence alignment and PendingRealized. No full Frame is asserted across child allocation/write or obligation changes, and no final heap or state is supplied as an input oracle.

## Inventory, limits and observed failures

The body has the exact four heads in order, one named LOCAL Monad List, six reviewed have declarations, one proof let inputs, one structural worker and one proper-tail proof induction. There is no private helper, new type/predicate, LawfulMonad/global instance, classical command, axiom, sorry/admit or option/proof-limit override. Both retained bodies fit hard260. Full fixed Symbol/Constraint and complete payloads are preserved.

strict-source-1 actually exited1. Its5245-byte raw log reports default simp step/200000-heartbeat exhaustion at the broad unsupported-case simplification and a remaining definitional map-composition goal. The retained strict2 patch changes only those two proof sites. strict-source-2 also actually exited1; its165161-byte raw log has repeated elaboration diagnostics at the main existential refine line225, where action/final-state witnesses are still underscores. I inspected its diagnostic index and initial explicit missing-implicit/placeholder diagnostics, not every repeated3064-line context. Root can give explicit actual action and conditional final-state witnesses without changing the accepted statement/model. I made no proof edit and ran no compiler. There is no source/public/build/Audit success or future seal/push claim in this review.

## Boundaries

The result is a genuine ordered fixed-native-heap partial traversal, with actual unsupported-prefix state and concrete Some completion. It does not implement terminal merging, union/representative/assimilation/native intersection or a native continuation after None. Ordinary nonterminal children keep full suspended buckets; Mu/retained unions keep the documented diagnostic truncation slots. No suspended-language preservation follows from that truncation. The inherited arity-true premise bounds the main producer; the raw definitions retain existing earlier arity rejection. Constructor-receipt-to-own-arity transport, native Value/Graph/ID realization, index updates/selection, native Int/containers, solver/runtime/resources, whole-driver language/termination and H6 remain separate. The full goal is active.

Only read/search/hash/JSON operations and this new /tmp report were performed. No compiler/parser/candidate/prepared program/import/native probe/Git/network/board operation or repository/old-review mutation occurred.

## Exact input identities

| Input | Bytes | SHA-256 |
|---|---:|---|
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-1/MicroCFTA/SourcePruningEnumerationEdgeTraversal.lean` | 14871 | `2079797f14571982c962d281d3330f46da2ab3d7e82b9fa32018102730324a42` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-2/MicroCFTA/SourcePruningEnumerationEdgeTraversal.lean` | 15072 | `7a37c5dc044ab3c6796b25f7d34478c7ba1eefc037402a0b95bb21410d39e2c7` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/explicit-unsupported-cases.patch` | 1373 | `385c8ee7a07d68cb885419a33426ea04cdd240e8d57c368a644517b483019652` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/body-gate.json` | 10050 | `54a6b05d801b7b8e7333477837953883d3314ad12fc2aef584222e61fc3c3a38` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024-proposal/pins.json` | 11390 | `dbca3703e6e8c77b0aefd78bafadcdb04976323f4a61e38837c83db887ab682b` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024-proposal/FROZEN.json` | 1192 | `17143e875e00952da47b29939b234b232a3214401348a0aa562ab908c99c2a76` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024-declaration-review.md` | 11929 | `eaa1edb8e4ab485751f2e41ef01ca1ba34b74f91fa718cba99441ea425147566` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-1/report.json` | 716 | `12400e3f80a169706072343a2ec1dddaf58afeb2f7bce6b88821adf16fa648b5` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-1/raw.log` | 5245 | `8c389246aeef5e6f7fd199cd78aea1113a4ab91990c1743f48c2ba54217c428f` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-2/report.json` | 718 | `3ec0f30d263ad621d36fe2e5aeb41b19bc3c8c02777d18972d14a217c5b193f9` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-2/raw.log` | 165161 | `554a188482b93a1c5321d4194d673d5809c8cf8a09d6aac5a04db06d2b6b5041` |
