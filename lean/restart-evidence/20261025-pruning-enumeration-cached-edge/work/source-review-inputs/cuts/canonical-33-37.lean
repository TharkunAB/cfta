
/-- Every stored count is the exact number of references to its current class. -/
def Correct (roots : Nat → Nat) (values : List (UVarValue Symbol))
    (waiting : EnumerationWaitingIndex.Waiting) : Prop :=
  EnumerationWaitingIndex.Correct (values.map (canonicalValue roots)) waiting
