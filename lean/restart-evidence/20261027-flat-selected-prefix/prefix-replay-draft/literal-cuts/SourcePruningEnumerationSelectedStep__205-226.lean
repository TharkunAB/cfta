noncomputable def finish
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (r n p h k uv : Nat) : Result width Typing → Result width Typing
  | .narrowed checked prepared caller queries action (some after)
      (some [.ok ((false, updated), callbackCore)]) none =>
      .narrowed checked prepared caller queries action (some after)
        (some [.ok ((false, updated), callbackCore)])
        (some (SourcePruningEnumerationNativeOrdinary.run checkEmpty r n p h k uv edgesOf caller after queries))
  | observed => observed

/-- Retain the original selected-step observation with its legacy ordinary continuation. -/
noncomputable def run
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries) : Result width Typing :=
  finish checkEmpty edgesOf r n p h k uv
    (runPrefix holeKey fits admits graph templates stop order metadata readFuel checkFuel nativeFuel
      representativeFuel indexFuel callbackFuel uv caller before queries)
