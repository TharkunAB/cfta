theorem finish_hook_outputs (uv : Nat)
    (result : SourcePruningEnumerationNativeContinuations.Result
      (SourcePruningEnumerationRecursive.Output width Typing) (Failure width Typing) width) :
    hookOutputs (finish uv result) = foldOutputs result := by
  cases result <;> rfl
