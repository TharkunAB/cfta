noncomputable def project (constraint : SourceSymbolicIndex.Constraint Formula) :
    Option (List EqualityTrie.Trie × Option (SourceSymbolicIndex.Constraint Formula))
 :=
  match sourceEqualities constraint with
  | none => none
  | some classes =>
      some (EnumerationEquality.readClasses classes,
        if (positive constraint.guard).isSome then none else some constraint)
