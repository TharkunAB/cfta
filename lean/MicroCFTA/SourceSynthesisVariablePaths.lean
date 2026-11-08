import MicroCFTA.SourceSynthesisGeneralizeSyntax

/-!
# Original variable-leaf paths

The actual occurrence reader stops at each recognized variable leaf.
Its paths are prefix-free across all names and have an original-size bound.
The raw generalization classes inherit both facts from their occurrences.
These results do not assume path preservation by equality normalization.
-/
namespace MicroCFTA.SourceSynthesisVariablePaths
open SourceSynthesisTypeSyntax (Ty variableSymbol)
open SourceSynthesisGeneralizeSyntax

private def Separated (items : List (String × List Nat)) : Prop :=
  ∀ firstName first secondName second,
    (firstName, first) ∈ items → (secondName, second) ∈ items → first <+: second → first = second

private def Properties (typ : Ty) : Prop :=
  Separated (occurrences typ) ∧
    ∀ name path, (name, path) ∈ occurrences typ → path.length < sizeOf typ

private theorem shift_member (index : Nat) (items : List (String × List Nat)) (name : String) (path : List Nat) :
    (name, path) ∈ shift index items ↔ ∃ rest, path = index :: rest ∧ (name, rest) ∈ items := by
  simp only [shift, List.mem_map]
  constructor
  · rintro ⟨⟨symbol, rest⟩, member, same⟩
    cases same
    exact ⟨rest, rfl, member⟩
  · rintro ⟨rest, rfl, member⟩
    exact ⟨(name, rest), member, rfl⟩

private theorem children_origin (index : Nat) (types : List Ty) :
    ∀ name path, (name, path) ∈ childrenOccurrences index types →
      ∃ offset typ rest, types[offset]? = some typ ∧ path = (index + offset) :: rest ∧
        (name, rest) ∈ occurrences typ := by
  induction types generalizing index with
  | nil =>
      intro name path member
      simp only [childrenOccurrences, List.not_mem_nil] at member
  | cons first rest ih =>
      intro name path member
      rw [childrenOccurrences] at member
      rcases List.mem_append.mp member with own | later
      · obtain ⟨tail, same, found⟩ := (shift_member index _ name path).mp own
        exact ⟨0, first, tail, rfl, by simpa only [Nat.add_zero] using same, found⟩
      · obtain ⟨offset, typ, tail, atIndex, same, found⟩ := ih (index + 1) name path later
        refine ⟨offset + 1, typ, tail, ?_, ?_, found⟩
        · simpa only [List.getElem?_cons_succ] using atIndex
        · have equal : index + 1 + offset = index + (offset + 1) := by omega
          simpa only [equal] using same

private theorem children_properties (index : Nat) (types : List Ty)
    (checked : ∀ typ ∈ types, Properties typ) :
    Separated (childrenOccurrences index types) ∧
      ∀ name path, (name, path) ∈ childrenOccurrences index types →
        ∃ typ ∈ types, path.length ≤ sizeOf typ := by
  constructor
  · intro firstName first secondName second firstMember secondMember pfx
    obtain ⟨firstIndex, firstType, firstTail, firstAt, firstEq, firstFound⟩ :=
      children_origin index types firstName first firstMember
    obtain ⟨secondIndex, secondType, secondTail, secondAt, secondEq, secondFound⟩ :=
      children_origin index types secondName second secondMember
    rw [firstEq, secondEq] at pfx
    obtain ⟨sameHead, tailExtends⟩ := List.cons_prefix_cons.mp pfx
    have sameIndex : firstIndex = secondIndex := by omega
    subst secondIndex
    have sameType : firstType = secondType := Option.some.inj (firstAt.symm.trans secondAt)
    subst secondType
    have sameTail := (checked firstType (List.mem_of_getElem? firstAt)).1
      firstName firstTail secondName secondTail firstFound secondFound tailExtends
    rw [firstEq, secondEq, sameTail]
  · intro name path member
    obtain ⟨offset, typ, rest, atIndex, same, found⟩ := children_origin index types name path member
    have included := List.mem_of_getElem? atIndex
    have short := (checked typ included).2 name rest found
    refine ⟨typ, included, ?_⟩
    rw [same, List.length_cons]
    omega

private theorem leaf_properties (name : String) (bound : Nat) (positive : 0 < bound) :
    Separated [(name, [])] ∧
      ∀ symbol (path : List Nat), (symbol, path) ∈ [(name, [])] → path.length < bound := by
  constructor
  · intro firstName first secondName second firstMember secondMember _
    have firstEq := congrArg Prod.snd (List.mem_singleton.mp firstMember)
    have secondEq := congrArg Prod.snd (List.mem_singleton.mp secondMember)
    exact firstEq.trans secondEq.symm
  · intro symbol path member
    have same : path = [] := congrArg Prod.snd (List.mem_singleton.mp member)
    simpa only [same, List.length_nil] using positive

private theorem lift_children (typ : Ty) (index : Nat) (types : List Ty)
    (checked : ∀ child ∈ types, Properties child)
    (smaller : ∀ child ∈ types, sizeOf child < sizeOf typ)
    (actual : occurrences typ = childrenOccurrences index types) : Properties typ := by
  obtain ⟨separated, short⟩ := children_properties index types checked
  constructor
  · simpa only [actual] using separated
  · intro name path member
    rw [actual] at member
    obtain ⟨child, included, bounded⟩ := short name path member
    exact Nat.lt_of_le_of_lt bounded (smaller child included)

private theorem occurrences_properties (typ : Ty) : Properties typ := by
  induction typ using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types, Properties typ) with
  | tVar name =>
      have positive : 0 < sizeOf (Ty.tVar name) := by simp only [Ty.tVar.sizeOf_spec]; omega
      simpa only [Properties, occurrences] using leaf_properties (variableSymbol name) _ positive
  | tFun argument result first second =>
      apply lift_children (.tFun argument result) 1 [argument, result]
      · intro child member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact first
        · exact second
      · intro child member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp only [Ty.tFun.sizeOf_spec] <;> omega
      · simp only [occurrences, childrenOccurrences, List.append_nil]
  | tCons name arguments children =>
      have smaller : ∀ child ∈ arguments, sizeOf child < sizeOf (Ty.tCons name arguments) := by
        intro child member
        have inside := List.sizeOf_lt_of_mem member
        simp only [Ty.tCons.sizeOf_spec]
        omega
      have ordinary (actual : occurrences (.tCons name arguments) = childrenOccurrences 0 arguments) :
          Properties (.tCons name arguments) := lift_children _ 0 arguments children smaller actual
      cases arguments with
      | nil =>
          by_cases recognized : isVariableSymbol name = true
          · have positive : 0 < sizeOf (Ty.tCons name []) := by simp only [Ty.tCons.sizeOf_spec]; omega
            simpa only [Properties, occurrences, recognized, ↓reduceIte] using leaf_properties name _ positive
          · constructor
            · intro firstName first secondName second firstMember _ _
              simp only [occurrences, recognized, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at firstMember
            · intro symbol path member
              simp only [occurrences, recognized, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at member
      | cons first rest =>
          cases rest with
          | nil => exact ordinary (by simp only [occurrences])
          | cons second rest =>
              cases rest with
              | nil =>
                  by_cases alias : name = "Fun"
                  · apply lift_children (.tCons name [first, second]) 1 [first, second] children smaller
                    simp only [occurrences, alias, ↓reduceIte, childrenOccurrences, List.append_nil]
                  · exact ordinary (by simp only [occurrences, alias, ↓reduceIte])
              | cons third tail => exact ordinary (by simp only [occurrences])
  | nil => rename_i typ member; cases member
  | cons first rest own later =>
      rename_i typ member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact later typ member

/-- No recognized original variable leaf lies strictly below another variable leaf. -/
theorem occurrences_prefix_free (typ : Ty) {firstName secondName : String} {first second : List Nat}
    (firstMember : (firstName, first) ∈ occurrences typ)
    (secondMember : (secondName, second) ∈ occurrences typ) (pfx : first <+: second) : first = second :=
  (occurrences_properties typ).1 firstName first secondName second firstMember secondMember pfx

/-- Every actual variable occurrence path is shorter than its original type syntax. -/
theorem occurrences_length_lt_sizeOf (typ : Ty) (name : String) (path : List Nat)
    (member : (name, path) ∈ occurrences typ) : path.length < sizeOf typ :=
  (occurrences_properties typ).2 name path member

/-- Every raw generalization-class path is an exact recognized original occurrence. -/
theorem equalityClasses_occurrence (typ : Ty) (paths : List (List Nat))
    (included : paths ∈ equalityClasses typ) (path : List Nat) (member : path ∈ paths) :
    ∃ name, (name, path) ∈ occurrences typ := by
  obtain ⟨name, _recognized, same⟩ := equalityClasses_origin typ paths included
  exact ⟨name, (mem_pathsOf name typ path).mp (same ▸ member)⟩

/-- Raw paths remain prefix-free even when they belong to different variable classes. -/
theorem equalityClasses_prefix_free (typ : Ty) (firstClass secondClass : List (List Nat))
    (firstIncluded : firstClass ∈ equalityClasses typ) (secondIncluded : secondClass ∈ equalityClasses typ)
    {first second : List Nat} (firstMember : first ∈ firstClass) (secondMember : second ∈ secondClass)
    (pfx : first <+: second) : first = second := by
  obtain ⟨firstName, firstFound⟩ := equalityClasses_occurrence typ firstClass firstIncluded first firstMember
  obtain ⟨secondName, secondFound⟩ := equalityClasses_occurrence typ secondClass secondIncluded second secondMember
  exact occurrences_prefix_free typ firstFound secondFound pfx

/-- Every path in an original raw equality class retains the original type-size bound. -/
theorem equalityClasses_length_lt_sizeOf (typ : Ty) (paths : List (List Nat))
    (included : paths ∈ equalityClasses typ) (path : List Nat) (member : path ∈ paths) :
    path.length < sizeOf typ := by
  obtain ⟨name, found⟩ := equalityClasses_occurrence typ paths included path member
  exact occurrences_length_lt_sizeOf typ name path found

end MicroCFTA.SourceSynthesisVariablePaths
