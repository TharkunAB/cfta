from pathlib import Path
p=Path('/tmp/mcfta-derived-scalar-shape-20261024/SourceGeneratedNodeViewShape.lean');s=p.read_text()
docs={
'  | normalC':'  /-- An ordinary positional constructor retains its arity. -/\n  | normalC',
'  | recC':'  /-- A record constructor retains its field count. -/\n  | recC',
'  | infixC':'  /-- A named infix constructor has two fields. -/\n  | infixC',
'  | forallC':'  /-- Quantified or constrained constructors are rejected. -/\n  | forallC',
'  | gadtC':'  /-- A positional GADT constructor is rejected. -/\n  | gadtC',
'  | recGadtC':'  /-- A record GADT constructor is rejected. -/\n  | recGadtC',
'  | dataD':'  /-- An ordinary datatype retains context and constructor order. -/\n  | dataD',
'  | newtypeD':'  /-- A newtype retains context and its one constructor. -/\n  | newtypeD',
'  | other':'  /-- Other reified forms need a manual view. -/\n  | other',
}
for old,new in docs.items():assert s.count(old)==1;s=s.replace(old,new)
s=s.replace('structure ScalarShape where\n  name : String\n  fields : List Unit','structure ScalarShape where\n  /-- The constructor base name has the Node suffix. -/\n  name : String\n  /-- Each unit is one plain scalar field. -/\n  fields : List Unit')
s=s.replace('structure ViewShape where\n  name : String\n  constructors : List ScalarShape','structure ViewShape where\n  /-- The generated type base name has the Node suffix. -/\n  name : String\n  /-- Generated constructors retain source order. -/\n  constructors : List ScalarShape')
s=s.replace('simp [generatedName, ValidName, first, suffix, present, eq_comm]','simp [generatedName, ValidName, first, suffix, present]\n  all_goals exact eq_comm')
start=s.index('  cases first : upperName upper name',s.index('private theorem namedScalar_success'))
end=s.index('\n/-- Success derives',start)
s=s[:start]+'''  change (generatedName source upper valuesInScope name).bind
    (fun generated => .ok ⟨generated, List.replicate arity ()⟩) = .ok result ↔ _
  rw [bind_ok_iff]
  constructor
  · rintro ⟨generated, done, final⟩
    obtain ⟨valid, rfl⟩ := (generatedName_success source upper valuesInScope name generated).mp done
    exact ⟨valid, (Except.ok.inj final).symm⟩
  · rintro ⟨valid, rfl⟩
    exact ⟨name ++ "Node", (generatedName_success source upper valuesInScope name _).mpr ⟨valid, rfl⟩, rfl⟩
''' +s[end:]
s=s.replace('''  | nil => simp
  | cons first rest ih =>
      rw [List.mapM_cons, bind_ok_iff]''','''  | nil =>
      change (.ok [] : Except String (List ScalarShape)) = .ok result ↔ _
      simp [eq_comm]
  | cons first rest ih =>
      rw [List.mapM_cons]
      change (generateConstructor source upper valuesInScope first).bind
        (fun head => (rest.mapM (generateConstructor source upper valuesInScope)).bind
          (fun tail => .ok (head :: tail))) = .ok result ↔ _
      rw [bind_ok_iff]''')
s=s.replace('''  | nil => simp [List.mapM_cons, failed, Except.bind]
  | cons first rest ih =>''','''  | nil =>
      rw [List.nil_append, List.mapM_cons]
      change (generateConstructor source upper valuesInScope bad).bind _ = .error error
      rw [failed]
      rfl
  | cons first rest ih =>''')
s=s.replace('''      simpa only [List.cons_append, List.mapM_cons, firstDone, Except.bind] using ih restValid''','''      rw [List.cons_append, List.mapM_cons]
      change (generateConstructor source upper valuesInScope first).bind
        (fun head => ((rest ++ bad :: later).mapM (generateConstructor source upper valuesInScope)).bind
          (fun tail => .ok (head :: tail))) = .error error
      rw [firstDone]
      change ((rest ++ bad :: later).mapM (generateConstructor source upper valuesInScope)).bind _ = .error error
      rw [ih restValid]
      rfl''')
s=s.replace('''  change (generatedName source upper typesInScope source >>= fun name =>
    constructors.mapM (generateConstructor source upper valuesInScope) >>= fun alternatives =>
      pure (ViewShape.mk name alternatives)) = .ok result ↔ _''','''  change (generatedName source upper typesInScope source).bind (fun name =>
    (constructors.mapM (generateConstructor source upper valuesInScope)).bind (fun alternatives =>
      .ok (ViewShape.mk name alternatives))) = .ok result ↔ _''')
s=s.replace('''  simp [derive, checkedDatatype, generatedName, first, plain, present, Except.bind]''','''  change (generatedName source upper typesInScope source).bind _ = .error _
  have failed : generatedName source upper typesInScope source = .error (collision source (source ++ "Node")) := by
    simp [generatedName, first, plain, present]
  rw [failed]
  rfl''')
s=s.replace('''  simp [derive, checkedDatatype, generatedName, first, suffix, Except.bind]''','''  change (generatedName source upper typesInScope source).bind _ = .error _
  rw [generatedName_hash source upper typesInScope source first suffix]
  rfl''')
p.write_text(s)
