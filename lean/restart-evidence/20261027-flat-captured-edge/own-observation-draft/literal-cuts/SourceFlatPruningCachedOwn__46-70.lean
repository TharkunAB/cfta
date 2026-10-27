/-- Relate each native child, actual bucket and optional captured action. -/
def StageRelated
    (flat : Value Symbol Constraint × List Suspended ×
      Option (EnumerationFlatState.Action Symbol Constraint (Fragments.Fragment Symbol)))
    (earlier : Value Symbol Constraint × List Suspended ×
      Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) : Prop :=
  flat.1 = earlier.1 ∧ flat.2.1 = earlier.2.1 ∧
    SourceFlatPruningShallowChild.OptionalActions flat.2.2 earlier.2.2

/-- Retain rejection, partiality and the complete ordered staged payload. -/
def PreparedRelated
    (flat : Option (List ((Symbol × List (Value Symbol Constraint × List Suspended ×
      Option (EnumerationFlatState.Action Symbol Constraint (Fragments.Fragment Symbol))) ×
        Option Constraint) × Cached Symbol Constraint)))
    (earlier : Option (List ((Symbol × List (Value Symbol Constraint × List Suspended ×
      Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) ×
        Option Constraint) × EnumerationExpandableIndex.Cached Symbol Constraint))) : Prop :=
  match flat, earlier with
  | none, none => True
  | some flat, some earlier =>
      Language.All₂ (fun left right =>
        left.1.1 = right.1.1 ∧
        Language.All₂ StageRelated left.1.2.1 right.1.2.1 ∧
        left.1.2.2 = right.1.2.2 ∧ Related left.2 right.2) flat earlier
  | _, _ => False
