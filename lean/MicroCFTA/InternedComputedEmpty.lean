import MicroCFTA.InternedNestedCoherentSites

/-!
# Empty records derived from actual source normalization

Every declared edge has a child that computes EmptyNode. Other children
can contain arbitrary nested constructors. A completed trace supplies all
of their actual effects before node or union normalization returns empty.
-/
namespace MicroCFTA.InternedComputedEmpty
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedSpecialization InternedNestedCoherence InternedErasedEdgeReplay

/-- Source normalization forces an empty result after all requested child computations complete. -/
inductive EmptyResult : Syntax Symbol Guard → Prop where
  | empty : EmptyResult .empty
  | node (edges : List (EdgeSyntax Symbol Guard))
      (pick : ∀ symbol constraint children, .mk symbol constraint children ∈ edges → Syntax Symbol Guard)
      (member : ∀ symbol constraint children present, pick symbol constraint children present ∈ children)
      (dead : ∀ symbol constraint children present, EmptyResult (pick symbol constraint children present)) : EmptyResult (.node edges)
  | union (members : List (Syntax Symbol Guard))
      (dead : ∀ child ∈ members, EmptyResult child) : EmptyResult (.union members)

/-- Every completed child has its actual output in the returned operand list. -/
theorem buildMany_member [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (values : List (Value Symbol Guard)) (final : State Symbol Guard) (coherent : Coherent before)
    (completed : buildMany expressions environment before = .done values final)
    (selected : Syntax Symbol Guard) (member : selected ∈ expressions) :
    ∃ start value finish, build selected environment start = .done value finish ∧ value ∈ values ∧ Coherent start := by
  cases expressions with
  | nil => cases member
  | cons first rest =>
      simp only [buildMany] at completed
      obtain ⟨head, middle, firstDone, later⟩ := bind_done _ _ _ _ completed
      obtain ⟨tail, last, tailDone, assembled⟩ := bind_done _ _ _ _ later
      simp only [Outcome.done.injEq] at assembled
      obtain ⟨rfl, rfl⟩ := assembled
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨before, head, middle, firstDone, List.mem_cons_self, coherent⟩
      · have middleCoherent : Coherent middle := by simpa only [firstDone, Outcome.state] using build_coherent first environment before coherent
        obtain ⟨start, value, finish, selectedDone, included, good⟩ :=
          buildMany_member rest environment middle tail last middleCoherent tailDone selected inRest
        exact ⟨start, value, finish, selectedDone, List.mem_cons_of_mem _ included, good⟩
termination_by expressions.length

/-- Each output operand comes from an actual source child with a coherent starting table. -/
theorem buildMany_each [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (values : List (Value Symbol Guard)) (final : State Symbol Guard) (coherent : Coherent before)
    (completed : buildMany expressions environment before = .done values final)
    (property : Value Symbol Guard → Prop)
    (children : ∀ child ∈ expressions, ∀ start value finish, Coherent start →
      build child environment start = .done value finish → property value) : ∀ value ∈ values, property value := by
  cases expressions with
  | nil => simp only [buildMany, Outcome.done.injEq] at completed; simp [← completed.1]
  | cons first rest =>
      simp only [buildMany] at completed
      obtain ⟨head, middle, firstDone, later⟩ := bind_done _ _ _ _ completed
      obtain ⟨tail, last, tailDone, assembled⟩ := bind_done _ _ _ _ later
      simp only [Outcome.done.injEq] at assembled
      obtain ⟨rfl, rfl⟩ := assembled
      have middleCoherent : Coherent middle := by simpa only [firstDone, Outcome.state] using build_coherent first environment before coherent
      intro value member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact children first List.mem_cons_self before value middle coherent firstDone
      · exact buildMany_each rest environment middle tail last middleCoherent tailDone property
          (fun child member => children child (List.mem_cons_of_mem _ member)) value inRest
termination_by expressions.length

/-- Every edge with a source-computed empty child is removed by node normalization. -/
theorem buildEdges_dead [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (values : List (EdgeValue Symbol Guard)) (final : State Symbol Guard) (coherent : Coherent before)
    (completed : buildEdges expressions environment before = .done values final)
    (dead : ∀ symbol constraint children, .mk symbol constraint children ∈ expressions →
      ∃ child ∈ children, ∀ start value finish, Coherent start → build child environment start = .done value finish → value = .empty) :
    ∀ edge ∈ values, edge.children.any (fun child => child.referenceOf == .empty) = true := by
  cases expressions with
  | nil => simp only [buildEdges, Outcome.done.injEq] at completed; simp [← completed.1]
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [buildEdges] at completed
          obtain ⟨childValues, middle, childrenDone, later⟩ := bind_done _ _ _ _ completed
          obtain ⟨edge, afterEdge, edgeDone, remaining⟩ := bind_done _ _ _ _ later
          obtain ⟨tail, last, tailDone, assembled⟩ := bind_done _ _ _ _ remaining
          simp only [Outcome.done.injEq] at assembled
          obtain ⟨rfl, rfl⟩ := assembled
          have middleCoherent : Coherent middle := by simpa only [childrenDone, Outcome.state] using buildMany_coherent children environment before coherent
          have afterCoherent : Coherent afterEdge := by
            have verified := run_coherent (makeEdge symbol constraint childValues) middle (makeEdge_safe _ _ _) middleCoherent
            change Coherent (work (makeEdge symbol constraint childValues) middle).state at verified
            simpa only [edgeDone, Outcome.state] using verified
          intro selected member
          rcases List.mem_cons.mp member with rfl | inRest
          · rename_i selected
            obtain ⟨child, included, emptyChild⟩ := dead symbol constraint children List.mem_cons_self
            obtain ⟨start, value, finish, childDone, present, good⟩ :=
              buildMany_member children environment before childValues middle coherent childrenDone child included
            have same := emptyChild start value finish good childDone
            have refs := makeEdge_references symbol constraint childValues middle middleCoherent
            simp only [work, Outcome.done.injEq] at edgeDone
            rw [edgeDone.1] at refs
            have emptyMember : InternedBinderProtocol.NodeRef.empty ∈ selected.children.map Value.referenceOf := by
              rw [refs]
              exact List.mem_map.mpr ⟨value, present, by simp [same, Value.referenceOf]⟩
            obtain ⟨value, present, emptyRef⟩ := List.mem_map.mp emptyMember
            exact List.any_eq_true.mpr ⟨value, present, by simpa only [beq_iff_eq] using emptyRef⟩
          · exact buildEdges_dead rest environment afterEdge tail last afterCoherent tailDone
              (fun symbol constraint children member => dead symbol constraint children (List.mem_cons_of_mem _ member)) selected inRest
termination_by expressions.length

/-- A declared source empty computation returns the actual EmptyNode through every canonical readback branch. -/
theorem build_empty [DecidableEq (EdgeKey Symbol Guard)] (zero : EmptyResult expression)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (value : Value Symbol Guard)
    (final : State Symbol Guard) (coherent : Coherent before)
    (completed : build expression environment before = .done value final) : value = .empty := by
  induction zero generalizing before value final with
  | empty =>
      simp only [build, Outcome.done.injEq] at completed
      exact completed.1.symm
  | node edges pick selectedMember dead ih =>
      simp only [build] at completed
      obtain ⟨values, middle, childrenDone, parentDone⟩ := bind_done _ _ _ _ completed
      have rejected := buildEdges_dead edges environment before values middle coherent childrenDone
        (fun symbol constraint children member => by
          exact ⟨pick symbol constraint children member, selectedMember symbol constraint children member,
            ih symbol constraint children member⟩)
      have none : surviving values = [] := List.filter_eq_nil_iff.mpr (by
        intro edge member
        simp [rejected edge member])
      have canonical : canonicalEdges (surviving values) = [] := by rw [none]; simp [canonicalEdges, EnumerationBuilderCaches.canonicalIds]
      simp only [work, makeNode, canonical, run, Outcome.done.injEq] at parentDone
      exact parentDone.1.symm
  | union members dead ih =>
      simp only [build] at completed
      obtain ⟨values, middle, childrenDone, parentDone⟩ := bind_done _ _ _ _ completed
      have all := buildMany_each members environment before values middle coherent childrenDone (fun value => value = .empty)
        (fun child member => ih child member)
      have flattened : values.flatMap unionMembers = [] := List.flatMap_eq_nil_iff.mpr (by
        intro value member
        simp [all value member, unionMembers])
      simp only [work, makeUnion, flattened, distinctNodes, run, Outcome.done.injEq] at parentDone
      exact parentDone.1.symm

end MicroCFTA.InternedComputedEmpty
