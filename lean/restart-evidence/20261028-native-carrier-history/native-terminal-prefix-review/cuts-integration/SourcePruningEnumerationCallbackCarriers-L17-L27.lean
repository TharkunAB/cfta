theorem recordTypes_carriers
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (input : Sum (Fragments.Fragment Symbol) Nat)
    (before after : State Symbol Guard) (result : Bool × Metadata Typing)
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before)
    (observed : Success (recordTypes graph templates fuel metadata uv input) before result after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after ∧ ReferencesCarry after := by
  have frame := recordTypes_frame graph templates fuel metadata uv input before after result total observed
  exact ⟨frame.total total, frame.carriers, frame.references references⟩

end MicroCFTA.SourcePruningRecordTypes
