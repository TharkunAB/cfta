theorem run_output_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (caller : Caller width)
    (queries : Queries) (before : Cached) :
    ∀ output ∈ hookOutputs (run holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveFuel metadata caller queries before),
      OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
        metadata caller queries before (SourcePruningEnumerationRestart.decision stop order metadata before) output :=
  resume_output_history holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    metadata caller queries before _
