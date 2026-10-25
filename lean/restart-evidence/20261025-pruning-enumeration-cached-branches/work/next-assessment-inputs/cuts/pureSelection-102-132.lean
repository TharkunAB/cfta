/-- Apply both empty-delta assimilation writes and retain the waiting table. -/
def assimilate (graph : Graph Symbol Guard) (target source : Nat) (merged : UVarValue Symbol)
    (state : Cached Symbol Guard) : Cached Symbol Guard :=
  ⟨assimilated state.core target source merged,
    fun uv => if uv = source then false else if uv = target then candidate graph merged else state.expandable uv,
    state.waiting⟩

/-- Completed assimilation preserves the canonical invariant at its actual endpoint. -/
theorem assimilate_correct (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (state : Cached Symbol Guard) (correct : Correct graph roots state)
    (target source : Nat) (oldSource oldTarget merged : UVarValue Symbol) (different : target ≠ source)
    (sourceRead : state.core.values[source]? = some oldSource)
    (targetRead : state.core.values[target]? = some oldTarget)
    (intersection : intersectValues graph oldSource oldTarget = some merged) :
    Correct graph roots (assimilate graph target source merged state) := by
  refine ⟨by simpa [assimilate, assimilated] using correct.aligned, ?_, ?_⟩
  · intro uv
    have sourceBound := (List.getElem?_eq_some_iff.mp sourceRead).1
    have targetBound := (List.getElem?_eq_some_iff.mp targetRead).1
    by_cases atSource : uv = source
    · subst uv
      simp [assimilate, assimilated, sourceBound, candidate]
    · by_cases atTarget : uv = target
      · subst uv
        simp [assimilate, assimilated, atSource, Ne.symm different, targetBound]
      · simp [assimilate, assimilated, atSource, atTarget, Ne.symm atSource,
          Ne.symm atTarget, correct.expandable uv]
  · exact EnumerationCanonicalWaiting.assimilation_correct roots state.core.values
      target source oldSource oldTarget merged different sourceRead targetRead
      (EnumerationIndexSource.intersection_references graph oldSource oldTarget merged intersection)
      state.waiting correct.waiting
