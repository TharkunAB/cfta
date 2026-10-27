theorem resume_output_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) :
    ∀ (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) (next : Option Next),
      ∀ output ∈ hookOutputs (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        workFuel recursiveFuel metadata caller queries before next),
        OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          recursiveFuel metadata caller queries before next output := by
