theorem processed (target : Nat) {flat : List (FlatReceipt width)} {earlier : List (Receipt width)}
    (related : SourceFlatPruningNativeBranches.ReceiptsRelated flat earlier)
    (admitted : ∀ receipt ∈ earlier, Admitted target receipt) :
    ∀ receipt ∈ flat, Indexed receipt := by
  revert admitted
  induction related with
  | nil =>
      intro _admitted receipt member
      cases member
  | @cons first second rest tail head _ ih =>
      intro admitted receipt member
      rcases List.mem_cons.mp member with same | member
      · subst receipt
        exact of_related target first second (admitted second (by simp)) head
      · exact ih (fun current inside => admitted current (List.mem_cons_of_mem _ inside)) receipt member
