# Source-only review

The proposal covers exactly two public theorems. Allocation derives a computed handle, actual allocation success, the exact returned-counter slot, and all-slot realization. Raw write derives a computed handle, actual setValue success, exact full final state, the written slot and all-slot realization. Alignment and in-range premises are explicit. The native and enumeration guard types remain distinct. Suspended constraints are arbitrary and keep their original order.

No new Ready, Good, Total, semantic acceptance, counter oracle, canonical-root, or available-output premise is introduced. Coherent/Available/closed are genuine current inputs to the existing codec theorem. No payload is identified using only an interned reference. The global realization conclusion includes old unreferenced slots.

The model List.set does not create an out-of-range entry, unlike source IntMap.insert. The raw-write inside premise closes this boundary. Allocation's alignment binds the returned counter to the appended storage index. Neither follows from realization alone.

Native writeUVarValue also maintains waiting and expandable caches. The existing EnumerationState action models the value/ancestry state, not those cached fields. This package does not claim their preservation, native NodeId extraction, or full Haskell state equality. Narrowing, native intersection/assimilation and full typedTypes composition remain deferred.

Arity authored these declarations and this review. Root will author bodies and owns compiler checks. This is an author review, not independent validation or compilation. The source import routes are checked as literal declarations only. No proof body or executable candidate is present.
