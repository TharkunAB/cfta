import MicroCFTA.SourceDenotationLevels
import MicroCFTA.SymbolicBijections

/-!
# Distinctness of the ordinary level shortcut

A level can bypass set construction when each state has distinct outgoing
symbols. The first-deepest-child split is disjoint. Repeated child states do
not require an extra restriction: each coordinate chooses its own term.
-/

namespace MicroCFTA.SourceDenotationLevelDistinct

open Language LevelEnumeration SourceDenotationLevels

/-- Distinct coordinates and the first-deepest split give each child tuple once. -/
theorem children_nodup (current atMost shallower : State → List α)
    (currentDistinct : ∀ state, (current state).Nodup)
    (atMostDistinct : ∀ state, (atMost state).Nodup)
    (shallowerDistinct : ∀ state, (shallower state).Nodup)
    (separate : ∀ state value, value ∈ current state → value ∈ shallower state → False)
    (keys : List State) : (childLists current atMost shallower keys).Nodup := by
  induction keys with
  | nil => simp [childLists]
  | cons key rest ih =>
      change List.Pairwise (· ≠ ·) (_ ++ _)
      apply List.pairwise_append.mpr
      refine ⟨?_, ?_, ?_⟩
      · apply List.pairwise_flatMap.mpr
        refine ⟨?_, ?_⟩
        · intro first present
          apply List.pairwise_map.mpr
          exact (SymbolicDriver.products_nodup atMost rest (fun state _ => atMostDistinct state)).imp
            (fun different same => different (List.cons.inj same).2)
        · apply (currentDistinct key).imp
          intro first second different left leftIn right rightIn same
          obtain ⟨leftTail, _, leftEq⟩ := List.mem_map.mp leftIn
          obtain ⟨rightTail, _, rightEq⟩ := List.mem_map.mp rightIn
          exact different (List.cons.inj (leftEq.trans (same.trans rightEq.symm))).1
      · apply List.pairwise_flatMap.mpr
        refine ⟨?_, ?_⟩
        · intro tail present
          apply List.pairwise_map.mpr
          exact (shallowerDistinct key).imp (fun different same => different (List.cons.inj same).1)
        · apply ih.imp
          intro first second different left leftIn right rightIn same
          obtain ⟨leftHead, _, leftEq⟩ := List.mem_map.mp leftIn
          obtain ⟨rightHead, _, rightEq⟩ := List.mem_map.mp rightIn
          exact different (List.cons.inj (leftEq.trans (same.trans rightEq.symm))).2
      · intro left leftIn right rightIn same
        obtain ⟨first, firstIn, tail, _, leftEq⟩ :=
          (by simpa only [List.mem_flatMap, List.mem_map] using leftIn :
            ∃ first ∈ current key, ∃ tail ∈ products atMost rest, first :: tail = left)
        obtain ⟨otherTail, _, other, otherIn, rightEq⟩ :=
          (by simpa only [List.mem_flatMap, List.mem_map] using rightIn :
            ∃ tail ∈ childLists current atMost shallower rest, ∃ first ∈ shallower key, first :: tail = right)
        have sameHead := (List.cons.inj (leftEq.trans (same.trans rightEq.symm))).1
        exact separate key first firstIn (sameHead ▸ otherIn)

/-- Different outgoing symbols distinguish all terms from different alternatives. -/
theorem labelled_nodup (outgoing : List (Edge State Symbol))
    (unique : (outgoing.map Edge.label).Nodup)
    (choices : Edge State Symbol → List (List (Term Symbol)))
    (distinct : ∀ edge ∈ outgoing, (choices edge).Nodup) :
    (outgoing.flatMap fun edge => (choices edge).map (Term.node edge.label)).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro edge present
    apply List.pairwise_map.mpr
    exact (distinct edge present).imp (fun different same => different (Term.node.inj same).2)
  · apply (List.pairwise_map.mp unique).imp
    intro first second different left leftIn right rightIn same
    obtain ⟨leftChildren, _, leftEq⟩ := List.mem_map.mp leftIn
    obtain ⟨rightChildren, _, rightEq⟩ := List.mem_map.mp rightIn
    exact different (Term.node.inj (leftEq.trans (same.trans rightEq.symm))).1

/-- Distinct symbols suffice for distinct leaves before any deduplication. -/
theorem leaves_nodup (automaton : Automaton State Symbol) (state : State)
    (unique : ((automaton state).map Edge.label).Nodup) : (leaves automaton state).Nodup := by
  have same : leaves automaton state = (automaton state).flatMap
      (fun edge => ((if edge.children.isEmpty then [[]] else []) : List (List (Term Symbol))).map (Term.node edge.label)) := by
    unfold leaves
    congr 1
    funext edge
    split <;> rfl
  rw [same]
  apply labelled_nodup _ unique
  intro edge present
  split <;> simp

/-- The unambiguous shortcut is distinct when its input is; the set branch is distinct by its readback contract. -/
theorem clean_nodup (setList : List (Term Symbol) → List (Term Symbol))
    (setDistinct : ∀ terms, (setList terms).Nodup) (unambiguous : Bool) (terms : List (Term Symbol))
    (shortcut : unambiguous = true → terms.Nodup) : (clean setList unambiguous terms).Nodup := by
  cases unambiguous
  · exact setDistinct terms
  · exact shortcut rfl

/-- All three source tables contain no duplicate term. -/
def Distinct (table : Tables State Symbol) : Prop :=
  (∀ state, (table.current state).Nodup) ∧
  (∀ state, (table.atMost state).Nodup) ∧
  (∀ state, (table.shallower state).Nodup)

/-- Initial leaves satisfy the shortcut or use the actual set readback. -/
theorem initial_distinct (automaton : Automaton State Symbol)
    (setList : List (Term Symbol) → List (Term Symbol)) (setDistinct : ∀ terms, (setList terms).Nodup)
    (unambiguous : Bool) (unique : unambiguous = true → ∀ state, ((automaton state).map Edge.label).Nodup) :
    Distinct (initial automaton setList unambiguous) := by
  have leavesDistinct : ∀ state, (clean setList unambiguous (leaves automaton state)).Nodup :=
    fun state => clean_nodup setList setDistinct unambiguous _ (fun enabled => leaves_nodup automaton state (unique enabled state))
  exact ⟨leavesDistinct, leavesDistinct, fun _ => .nil⟩

/-- Exact current and shallower tables make the two child-product branches disjoint. -/
theorem deeper_nodup (automaton : Automaton State Symbol) (height : Nat) (before : Tables State Symbol)
    (semantic : Exact automaton height before) (distinct : Distinct before) (state : State)
    (unique : ((automaton state).map Edge.label).Nodup) : (SourceDenotationLevels.deeper automaton before state).Nodup := by
  apply labelled_nodup _ unique
  intro edge present
  apply children_nodup before.current before.atMost before.shallower distinct.1 distinct.2.1 distinct.2.2
  intro state term current shallow
  have first := ((semantic.1 state term).mp current).2
  have second := ((semantic.2.2 state term).mp shallow).2
  omega

/-- Adding a deeper exact level cannot duplicate a term in the older accumulated table. -/
theorem next_distinct (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms)
    (setDistinct : ∀ terms, (setList terms).Nodup) (unambiguous : Bool)
    (unique : unambiguous = true → ∀ state, ((automaton state).map Edge.label).Nodup)
    (height : Nat) (positive : 0 < height) (before : Tables State Symbol)
    (semantic : Exact automaton height before) (distinct : Distinct before) :
    Distinct (next automaton setList unambiguous before) := by
  have currentDistinct : ∀ state, (clean setList unambiguous (SourceDenotationLevels.deeper automaton before state)).Nodup :=
    fun state => clean_nodup setList setDistinct unambiguous _
      (fun enabled => deeper_nodup automaton height before semantic distinct state (unique enabled state))
  refine ⟨currentDistinct, ?_, distinct.2.1⟩
  intro state
  apply List.pairwise_append.mpr
  refine ⟨currentDistinct state, distinct.2.1 state, ?_⟩
  intro first firstIn second secondIn same
  subst second
  have earlier := ((semantic.2.1 state first).mp secondIn).2
  have later := ((next_exact automaton plain setList setExact unambiguous height positive before semantic).1 state first |>.mp firstIn).2
  omega

/-- Every iteration proves the source's dedupUnless bypass safe from its actual symbol test. -/
theorem tables_distinct (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms)
    (setDistinct : ∀ terms, (setList terms).Nodup) (unambiguous : Bool)
    (unique : unambiguous = true → ∀ state, ((automaton state).map Edge.label).Nodup) (depth : Nat) :
    Distinct (tables automaton setList unambiguous depth) := by
  induction depth with
  | zero => exact initial_distinct automaton setList setDistinct unambiguous unique
  | succ depth ih =>
      exact next_distinct automaton plain setList setExact setDistinct unambiguous unique
        (depth + 1) (by omega) _ (tables_exact automaton plain setList setExact unambiguous depth) ih

end MicroCFTA.SourceDenotationLevelDistinct
