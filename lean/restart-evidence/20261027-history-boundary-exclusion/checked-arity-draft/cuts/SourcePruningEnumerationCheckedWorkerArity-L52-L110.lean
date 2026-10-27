    by_cases same : left.children.length = right.children.length
    · exact same
    · have impossible := congrArg Prod.fst
        (SourceEqualityIntersectionEdgeAllocation.run_mismatch le first second
          left.children.length right.children.length operations same)
      rw [prepared] at impossible
      cases impossible
  obtain ⟨branch, literal, sourceSame, _prefixValid, _growth, ready⟩ :=
    SourceEqualityIntersectionEdgeAllocation.run_correct le first second
      left.children.length right.children.length operations operationsValid firstReady secondReady
  have branchSame : branch = .ready combined := Except.ok.inj (literal.symm.trans prepared)
  subst branch
  obtain ⟨_combinedReady, cached, _physical⟩ := ready combined rfl
  have accepted : SourceEqualityMkEdgeAllocation.accepted
      (SourceEqualityConjoinAllocation.readback combined) left.children.length = true := by
    change SourceEqualityIntersectionEdgeAllocation.Branch.ready
      (SourceEqualityConjoinAllocation.readback combined) = _ at sourceSame
    unfold SourceEqualityIntersectionEdgeAllocation.source at sourceSame
    split at sourceSame
    next _mismatch => cases sourceSame
    next _matched =>
      dsimp only at sourceSame
      split at sourceSame
      next kept =>
        have readbackSame := SourceEqualityIntersectionEdgeAllocation.Branch.ready.inj sourceSame
        rw [readbackSame]
        exact kept
      next _rejected => cases sourceSame
  have fits : SourceEqualityMkEdgeAllocation.fits left.children.length
      (SourceCompactGuards.sourceEqualities (SourceEqualityConjoinAllocation.readback combined)) = true := by
    by_cases rejected : SourceEqualityMkEdgeAllocation.contradictory
        (SourceEqualityConjoinAllocation.readback combined) = true
    · simp only [SourceEqualityMkEdgeAllocation.accepted, rejected, ↓reduceIte,
        Bool.false_eq_true] at accepted
    · simpa only [SourceEqualityMkEdgeAllocation.accepted, rejected, Bool.false_eq_true,
        ↓reduceIte] using accepted
  obtain ⟨classes, source, rootBounds⟩ := (SourceEqualityMkEdgeArity.fits_exact
    left.children.length (SourceCompactGuards.sourceEqualities
      (SourceEqualityConjoinAllocation.readback combined))).mp fits
  obtain ⟨canonicalProjection, validTries, pathReadback, _meaning⟩ :=
    (source ▸ SourcePruningEnumerationConstraint.project_complete
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
