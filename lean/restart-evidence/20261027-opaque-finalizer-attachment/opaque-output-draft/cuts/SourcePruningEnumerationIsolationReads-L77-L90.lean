/-- Either successful recording side and either Boolean result retain the same isolated core slot. -/
theorem IsolatedPending.through_recordTypes {Typing : Type}
    (graph : Graph Symbol EnumGuard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragments.Fragment Symbol) Nat)
    (before after : EnumerationState.State Symbol EnumGuard)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (isolated : IsolatedPending held handle before)
    (total : UnionFind.Total before.representatives)
    (observed : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after) : IsolatedPending held handle after :=
  isolated.through_frame
    (SourcePruningRecordTypes.recordTypes_frame graph templates fuel metadata uv input
      before after result total observed)
