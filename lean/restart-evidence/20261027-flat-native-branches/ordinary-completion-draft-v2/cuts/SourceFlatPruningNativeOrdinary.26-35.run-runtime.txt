noncomputable def run (checkEmpty : Bool) (nativeFuel p h uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) : Raw × Option (SourceFlatPruningNativeBranches.Result width) :=
  let raw := ExceptT.run (SourceFlatPruningEntry.enter caller.checked.native.machine.heap uv before.core)
  (raw, match raw with
    | [.ok ((target, _handle, scs, parent@(.node _ _ _ _)), entered)] =>
        if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
        else some (SourceFlatPruningNativeBranches.run checkEmpty nativeFuel p h target scs
          (EnumerationFlatCached.frame entered before) (edgesOf parent) caller queries)
    | _ => none)
