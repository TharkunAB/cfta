theorem assimilation_correct (roots : Nat → Nat) (values : List (UVarValue Symbol))
    (target source : Nat) (oldSource oldTarget merged : UVarValue Symbol)
    (different : target ≠ source) (sourceRead : values[source]? = some oldSource)
    (targetRead : values[target]? = some oldTarget)
    (mergedRefs : references merged = references oldSource ++ references oldTarget)
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) :
    Correct roots ((values.set target merged).set source .eliminated) waiting := by
  unfold Correct at *
  rw [List.map_set, List.map_set]
  intro key
  have targetStored : (values.map (canonicalValue roots))[target]? =
      some (canonicalValue roots oldTarget) := by simp [targetRead]
  have sourceStored : ((values.map (canonicalValue roots)).set target
