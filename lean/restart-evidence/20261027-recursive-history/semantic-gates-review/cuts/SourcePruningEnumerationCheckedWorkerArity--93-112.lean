      (SourceEqualityConjoinAllocation.readback combined) cached)
  obtain ⟨values, after, trace, built, symbolSame, guardSame, childrenSame, lengthSame⟩ :=
    SourceEqualityNativeCheckedCode.children_readback nodes edges calls domain left right combined
      state valid known leftResident rightResident sameArity result final done
  rw [guardSame] at projected
  have projectionSame := Option.some.inj (canonicalProjection.symm.trans projected)
  have triesSame : EnumerationEquality.readClasses classes = tries := congrArg Prod.fst projectionSame
  refine ⟨values, after, trace, built, symbolSame, guardSame, childrenSame, lengthSame, ?_, ?_⟩
  · rw [← triesSame]
    exact validTries
  · intro start
    rw [← triesSame, lengthSame]
    apply (fresh_arity_iff left.children.length start (EnumerationEquality.readClasses classes)).mpr
    intro trie member index suffix path
    obtain ⟨paths, pathsMember, same⟩ := List.mem_map.mp member
    subst trie
    exact rootBounds paths pathsMember (index :: suffix)
      ((pathReadback paths pathsMember (index :: suffix)).mp path)

end MicroCFTA.SourcePruningEnumerationCheckedWorkerArity
