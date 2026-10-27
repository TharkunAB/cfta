def Correct (roots : Nat → Nat) (values : List (UVarValue Symbol))
    (waiting : EnumerationWaitingIndex.Waiting) : Prop :=
  EnumerationWaitingIndex.Correct (values.map (canonicalValue roots)) waiting
