import MicroCFTA.ConstructorProbeWorklist

/-!
# Reachable declaration positions for typing labels

The source emits an algebraic row before its fields. It skips atomic types
and repeated algebraic types. Each emitted row starts its positions at zero.
The position map keeps the last occurrence of a label. An absent label gets
position zero. This model uses the existing descriptor and map interfaces.
It does not derive Generic descriptions or assert that discovery terminates.
-/
namespace MicroCFTA.SourceTypingHelperOrder

open Generic
variable {State Constructor : Type}

/-- A completed source description walk retains the original ordered rows. -/
inductive Reachable (describe : State → Description State Constructor) :
    List State → List State → List (Row State Constructor) → Prop where
  | nil : Reachable describe seen [] []
  | atomic (actual : describe state = .atomic)
      (tail : Reachable describe seen pending rows) :
      Reachable describe seen (state :: pending) rows
  | seen (actual : describe state = .algebraic alternatives) (old : state ∈ visited)
      (tail : Reachable describe visited pending rows) :
      Reachable describe visited (state :: pending) rows
  | fresh (actual : describe state = .algebraic alternatives) (new : state ∉ visited)
      (tail : Reachable describe (state :: visited) (children alternatives ++ pending) rows) :
      Reachable describe visited (state :: pending) (alternatives :: rows)

/-- Every emitted helper row is an unchanged algebraic declaration. -/
theorem Reachable.rows_exact {describe : State → Description State Constructor}
    {seen pending rows} (trace : Reachable describe seen pending rows) :
    ∀ row ∈ rows, ∃ state, describe state = .algebraic row := by
  induction trace with
  | nil => simp
  | atomic _ _ ih => exact ih
  | seen _ _ _ ih => exact ih
  | fresh actual _ _ ih =>
      intro row member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, actual⟩
      · exact ih row later

/-- The literal list comprehension resets its index for each reached type. -/
def entries (label : Constructor → String) (rows : List (Row State Constructor)) :
    List (String × Int) :=
  rows.flatMap fun row => row.zipIdx.map fun entry => (label entry.1.1, (entry.2 : Int))

/-- The existing overwrite map models the source Map.fromList. -/
def positions (label : Constructor → String) (rows : List (Row State Constructor)) :
    Cache.Table String Int := ConstructorProbeWorklist.latest (entries label rows)

/-- The source order key retains the label after its default-zero position. -/
def order (label : Constructor → String) (rows : List (Row State Constructor))
    (symbol : String) : Int × String := ((positions label rows symbol).getD 0, symbol)

private theorem latest_readback (pairs : List (String × Int)) (key : String) :
    ConstructorProbeWorklist.latest pairs key =
      (pairs.reverse.find? fun pair => decide (pair.1 = key)).map Prod.snd := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp only [ConstructorProbeWorklist.latest, List.reverse_cons, List.find?_append,
        List.find?_singleton, ih]
      cases rest.reverse.find? (fun pair => decide (pair.1 = key)) with
      | none => simp only [Option.map_none]
                by_cases same : key = pair.1 <;> simp [same, eq_comm]
      | some value => simp

/-- Lookup reads the last matching entry of the original ordered comprehension. -/
theorem positions_last (label : Constructor → String) (rows : List (Row State Constructor))
    (key : String) :
    positions label rows key =
      (((entries label rows).filter fun pair => decide (pair.1 = key)).getLast?).map Prod.snd := by
  simpa only [positions, List.getLast?_filter] using latest_readback (entries label rows) key

/-- A label has no declared position exactly when no emitted occurrence has that label. -/
theorem positions_absent (label : Constructor → String) (rows : List (Row State Constructor))
    (key : String) :
    positions label rows key = none ↔ ∀ position, (key, position) ∉ entries label rows := by
  constructor
  · intro absent position member
    obtain ⟨value, found⟩ := (ConstructorProbeWorklist.latest_present (entries label rows) key).mpr
      ⟨position, member⟩
    rw [show ConstructorProbeWorklist.latest (entries label rows) key = none from absent] at found
    cases found
  · intro absent
    cases found : positions label rows key with
    | none => rfl
    | some value => exact False.elim (absent value
        (ConstructorProbeWorklist.latest_member (entries label rows) key value found))

/-- Every successful lookup retains a concrete declaration and its local index. -/
theorem position_origin (label : Constructor → String) (rows : List (Row State Constructor))
    (key : String) (position : Int) (found : positions label rows key = some position) :
    ∃ row ∈ rows, ∃ (constructor : Constructor) (fields : List State) (index : Nat),
      row[index]? = some (constructor, fields) ∧ label constructor = key ∧
        (index : Int) = position := by
  have member := ConstructorProbeWorklist.latest_member (entries label rows) key position found
  obtain ⟨row, reached, localEntry⟩ := List.mem_flatMap.mp member
  obtain ⟨⟨⟨constructor, fields⟩, index⟩, indexed, same⟩ := List.mem_map.mp localEntry
  exact ⟨row, reached, constructor, fields, index,
    List.mem_zipIdx_iff_getElem?.mp indexed, congrArg Prod.fst same, congrArg Prod.snd same⟩

/-- A reached lookup comes from an actual original algebraic helper declaration. -/
theorem reachable_origin (label : Constructor → String)
    {describe : State → Description State Constructor} {seen pending rows}
    (trace : Reachable describe seen pending rows) (key : String) (position : Int)
    (found : positions label rows key = some position) :
    ∃ state row, ∃ (constructor : Constructor) (fields : List State) (index : Nat),
      describe state = .algebraic row ∧ row[index]? = some (constructor, fields) ∧
        label constructor = key ∧ (index : Int) = position := by
  obtain ⟨row, reached, constructor, fields, index, declared, name, offset⟩ :=
    position_origin label rows key position found
  obtain ⟨state, actual⟩ := trace.rows_exact row reached
  exact ⟨state, row, constructor, fields, index, actual, declared, name, offset⟩

/-- Absent labels use literal zero and keep their original label for tie breaking. -/
theorem order_absent (label : Constructor → String) (rows : List (Row State Constructor))
    (key : String) (absent : ∀ position, (key, position) ∉ entries label rows) :
    order label rows key = (0, key) := by
  simp only [order, (positions_absent label rows key).mpr absent, Option.getD_none]

/-- Present labels use their returned declaration position without changing the label. -/
theorem order_present (label : Constructor → String) (rows : List (Row State Constructor))
    (key : String) (position : Int) (found : positions label rows key = some position) :
    order label rows key = (position, key) := by
  simp only [order, found, Option.getD_some]

end MicroCFTA.SourceTypingHelperOrder
