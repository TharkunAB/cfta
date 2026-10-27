/-- Empty rejects before partition, prefix execution or any native query. -/
theorem empty
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) :
    run checkEmpty representativeFuel nativeFuel p h indexFuel scs .empty beforeCaller before queries =
      ((.ok (some []), beforeCaller, queries, before.core, before.waiting), some before) := by
  simp only [run, ↓reduceIte]

/-- Genuine nonterminal inputs derive the same fresh child and its maintained indexes. -/
