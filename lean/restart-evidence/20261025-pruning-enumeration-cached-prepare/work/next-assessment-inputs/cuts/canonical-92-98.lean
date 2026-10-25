/-- A fresh slot with no suspended references keeps every class count. -/
theorem allocate_correct (roots : Nat → Nat) (values : List (UVarValue Symbol)) (node : Option Nat)
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) :
    Correct roots (values ++ [.unenumerated node []]) waiting := by
  unfold Correct at *
  simpa [canonicalValue] using
    EnumerationWaitingIndex.allocate_correct (values.map (canonicalValue roots)) node waiting correct
