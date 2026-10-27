noncomputable def runPrefix
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries) : Result width Typing :=
  let read := ExceptT.run (getValue readFuel uv before.core)
  match read with
  | [.ok (.unenumerated (some oldHandle) scs, readAfter)] =>
      let check := ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter)
      match check with
      | [.ok (true, checked)] =>
          let candidate := SourcePruningEnumerationParkedRestart.adapt
            caller.checked.native.machine.heap indexFuel uv oldHandle scs before checked
          .parked checked candidate (candidate.map fun parked =>
            ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked))
      | [.ok (false, checked)] =>
          match lookupNode caller.checked.native.machine.heap oldHandle with
          | none => .stopped read (some check)
          | some oldValue =>
              let prepared := SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel
                representativeFuel uv oldHandle scs oldValue caller.checked.native.machine.heap
              let reached := SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨prepared.state, caller.checked.operations⟩) caller.fourth caller.merge
              match prepared with
              | .failed _fault _heap => .narrowed checked prepared reached queries none none none none
              | .done (_value, none) _heap => .narrowed checked prepared reached queries none none none none
              | .done (value, some action) heap =>
                  let raw := ExceptT.run (action checked)
                  match raw with
                  | [.ok ((), observed)] =>
                      match encodeNode value with
                      | none => .narrowed checked prepared reached queries (some raw) none none none
                      | some newHandle =>
                          let candidate := SourcePruningEnumerationNarrowAdapter.adapt heap indexFuel
                            uv oldHandle newHandle scs before observed
                          match candidate with
                          | none => .narrowed checked prepared reached queries (some raw) none none none
                          | some attached =>
                              let right := ExceptT.run (SourcePruningRecordTypes.recordTypes
                                graph templates callbackFuel metadata uv (.inr newHandle) attached.core)
                              match right with
                              | [.ok ((false, _updated), callbackCore)] =>
                                  let after := EnumerationExpandableIndex.frame callbackCore attached
                                  .narrowed checked prepared reached queries (some raw) (some after) (some right)
                                    none
                              | _ => .narrowed checked prepared reached queries (some raw) (some attached) (some right) none
                  | _ => .narrowed checked prepared reached queries (some raw) none none none
      | _ => .stopped read (some check)
  | _ => .stopped read none

/-- Every prefix observation leaves the ordinary continuation unexecuted. -/
theorem prefix_no_ordinary
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries) :
