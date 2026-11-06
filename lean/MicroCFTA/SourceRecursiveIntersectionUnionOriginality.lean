import MicroCFTA.SourceRecursiveIntersectionInputInventory
import MicroCFTA.SourceRecursiveIntersectionRequestScope

namespace MicroCFTA.SourceRecursiveIntersectionInputView

/-- For union values, input originality is equivalent to value originality. -/
theorem union_originalInput_iff_original {Symbol Guard : Type}
    {source : MicroCFTA.InternedConstructorTemplates.State Symbol Guard}
    (value : MicroCFTA.InternedConstructorTemplates.Value Symbol Guard)
    (facts : MicroCFTA.InternedNestedFacts.Facts source)
    (available : MicroCFTA.InternedProbeProvenance.Available source value) :
    match value with
    | .union _ _ _ _ => OriginalInput source (inputOf value) ↔ Original value
    | _ => True := by
  match value, available with
  | .union entry members depth free, availableUnion@(.intro _ resident _issued _children) =>
    match facts with
    | ⟨⟨valid, _edges, nodes⟩, _cached, _linked⟩ =>
      unfold MicroCFTA.InternedConstructorTemplates.Valid at valid
      obtain ⟨_validEdges, validNodes⟩ := valid
      unfold MicroCFTA.Cache.Valid at validNodes
      have stored := resident entry (by
        rw [MicroCFTA.InternedRecordCoherence.entryOf.eq_2])
      obtain ⟨_recorded, lookup, fields⟩ :=
        nodes entry.key (.union entry members depth free) stored
      rw [MicroCFTA.InternedRecordCoherence.NodeFields.eq_2] at fields
      have tableEntry : source.nodes.table entry.key = some entry := by
        have same := fields.1
        cases same
        exact lookup
      constructor
      · intro inputOriginal
        obtain ⟨other, originalOther, availableOther, codec⟩ := inputOriginal
        unfold inputOf at codec
        rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_4,
          MicroCFTA.IntersectionFlatMemoKey.input.eq_4, Option.getD_some] at codec
        have same : (.union entry members depth free :
            MicroCFTA.InternedConstructorTemplates.Value Symbol Guard) = other := by
          refine @Original.rec Symbol Guard
            (fun other _ =>
              MicroCFTA.InternedProbeProvenance.Available source other →
              MicroCFTA.IntersectionFlatMemoKey.input
                  (MicroCFTA.InternedConstructorTemplates.Value.referenceOf other) =
                some (MicroCFTA.IntersectSchedule.Input.union entry.identity) →
              (.union entry members depth free :
                MicroCFTA.InternedConstructorTemplates.Value Symbol Guard) = other)
            ?_ ?_ ?_ ?_ ?_ other originalOther availableOther codec
          · intro _available codec
            rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_1,
              MicroCFTA.IntersectionFlatMemoKey.input.eq_1] at codec
            nomatch codec
          · intro _name _available codec
            rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_2,
              MicroCFTA.IntersectionFlatMemoKey.input.eq_5] at codec
            nomatch codec
          · intro _entry _edges _depth _free _children _ih _available codec
            rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_3,
              MicroCFTA.IntersectionFlatMemoKey.input.eq_2] at codec
            nomatch codec
          · intro otherEntry otherMembers otherDepth otherFree _children _ih availableOther codec
            rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_4,
              MicroCFTA.IntersectionFlatMemoKey.input.eq_4] at codec
            have identities : otherEntry.identity = entry.identity :=
              congrArg (fun option : Option MicroCFTA.IntersectSchedule.Input =>
                match option with
                | some (.union name) => name
                | _ => 0) codec
            match availableOther with
            | .intro _ residentOther _issuedOther _childrenOther =>
              have storedOther := residentOther otherEntry (by
                rw [MicroCFTA.InternedRecordCoherence.entryOf.eq_2])
              obtain ⟨_recordedOther, lookupOther, fieldsOther⟩ := nodes otherEntry.key
                (.union otherEntry otherMembers otherDepth otherFree) storedOther
              rw [MicroCFTA.InternedRecordCoherence.NodeFields.eq_2] at fieldsOther
              have tableOther : source.nodes.table otherEntry.key = some otherEntry := by
                have same := fieldsOther.1
                cases same
                exact lookupOther
              have issued := (validNodes.2 entry.key entry tableEntry).2
              have issuedOther := (validNodes.2 otherEntry.key otherEntry tableOther).2
              rw [identities] at issuedOther
              have optionKeys : some entry.key = some otherEntry.key := issued.symm.trans issuedOther
              have keys := congrArg (fun option => Option.getD option entry.key) optionKeys
              rw [Option.getD_some, Option.getD_some] at keys
              rw [keys] at stored
              have optionValues := stored.symm.trans storedOther
              have values := congrArg (fun option => Option.getD option
                (.union entry members depth free :
                  MicroCFTA.InternedConstructorTemplates.Value Symbol Guard)) optionValues
              rw [Option.getD_some, Option.getD_some] at values
              exact values
          · intro _entry _body _depth _ordinary _original _ih _available codec
            rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_5,
              MicroCFTA.IntersectionFlatMemoKey.input.eq_3] at codec
            nomatch codec
        rw [same]
        exact originalOther
      · intro original
        refine ⟨.union entry members depth free, original, availableUnion, ?_⟩
        unfold inputOf
        rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_4,
          MicroCFTA.IntersectionFlatMemoKey.input.eq_4, Option.getD_some]
  | .empty, _ => exact True.intro
  | .reference .., _ => exact True.intro
  | .node .., _ => exact True.intro
  | .mu .., _ => exact True.intro

end MicroCFTA.SourceRecursiveIntersectionInputView
