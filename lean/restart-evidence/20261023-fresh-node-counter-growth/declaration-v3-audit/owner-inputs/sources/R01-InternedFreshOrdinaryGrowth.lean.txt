import MicroCFTA.InternedFreshOrdinaryConstruction
import MicroCFTA.InternedNestedConstructionGrowth

/-!
# Unrestricted validity and growth for the repaired executor

The proof needs only cache validity. It includes pending outcomes and
all effects of children whose returned edges are later removed.
-/
namespace MicroCFTA.InternedFreshOrdinaryGrowth
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request bind_correct work_correct)
open InternedFreshOrdinaryConstruction

mutual
/-- Any nested construction preserves validity and every previously completed record, including on failure. -/
theorem build_correct [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid state) :
    InternedConstructorTemplates.Valid (build expression environment state).state ∧ Grows state (build expression environment state).state := by
  cases expression with
  | empty | var index => simp only [build, Outcome.state]; exact ⟨valid, grows_refl _⟩
  | node edges =>
      simp only [build]
      exact bind_correct _ _ state (buildEdges_correct edges environment state valid)
        (fun values next valid => work_correct (makeNode values) next valid)
  | union members =>
      simp only [build]
      exact bind_correct _ _ state (buildMany_correct members environment state valid)
        (fun values next valid => work_correct (makeUnion values) next valid)
  | binder smart body =>
      simp only [build, request]
      apply bind_correct _ _ state
      · exact bind_correct _ _ state (build_correct body _ state valid)
          (fun value next valid => work_correct (withoutSelfReference .depth value) next valid)
      · intro depth afterDepth depthValid
        apply bind_correct _ _ afterDepth
        · exact bind_correct _ _ afterDepth (build_correct body _ afterDepth depthValid)
            (fun value next valid => work_correct (withoutSelfReference (.uninterned (ordinaryLevel depth)) value) next valid)
        · intro ordinary afterOrdinary ordinaryValid
          split
          · split <;> exact ⟨ordinaryValid, grows_refl _⟩
          · let key := muKey depth ordinary
            let entry := Cache.intern afterOrdinary.nodes key
            let allocated := {afterOrdinary with nodes := entry.2}
            have allocatedValid : InternedConstructorTemplates.Valid allocated :=
              ⟨ordinaryValid.1, (Cache.intern_correct _ _ ordinaryValid.2).1⟩
            have allocatedGrowth : Grows afterOrdinary allocated :=
              ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
            apply bind_correct _ _ afterOrdinary
            · have executed := bind_correct
                (build body (.reference (.interned entry.1.identity) :: environment) allocated)
                (fun value next => work (withoutSelfReference (.interned entry.1.identity) value) next)
                allocated (build_correct body _ allocated allocatedValid)
                (fun value next valid => work_correct (withoutSelfReference (.interned entry.1.identity) value) next valid)
              exact ⟨executed.1, grows_trans allocatedGrowth executed.2⟩
            · intro bodyValue afterBody bodyValid
              exact ⟨bodyValid, ⟨extends_refl _, extends_refl _, extends_refl _, keepFirst_extends _ _ _⟩⟩
termination_by sizeOf expression

/-- Child evaluation retains all previous records in both successful and pending outcomes. -/
theorem buildMany_correct [DecidableEq (EdgeKey Symbol Guard)] (expression : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid state) :
    InternedConstructorTemplates.Valid (buildMany expression environment state).state ∧ Grows state (buildMany expression environment state).state := by
  cases expression with
  | nil => simp only [buildMany, Outcome.state]; exact ⟨valid, grows_refl _⟩
  | cons first rest =>
      simp only [buildMany]
      apply bind_correct _ _ state (build_correct first environment state valid)
      intro value next nextValid
      apply bind_correct _ _ next (buildMany_correct rest environment next nextValid)
      intro values final finalValid
      exact ⟨finalValid, grows_refl _⟩
termination_by sizeOf expression

/-- Separate edge construction preserves the node and edge histories across nested child evaluation. -/
theorem buildEdges_correct [DecidableEq (EdgeKey Symbol Guard)] (expression : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard) (valid : InternedConstructorTemplates.Valid state) :
    InternedConstructorTemplates.Valid (buildEdges expression environment state).state ∧ Grows state (buildEdges expression environment state).state := by
  cases expression with
  | nil => simp only [buildEdges, Outcome.state]; exact ⟨valid, grows_refl _⟩
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [buildEdges]
          apply bind_correct _ _ state (buildMany_correct children environment state valid)
          intro values next nextValid
          apply bind_correct _ _ next (work_correct (makeEdge symbol constraint values) next nextValid)
          intro edge afterEdge edgeValid
          apply bind_correct _ _ afterEdge (buildEdges_correct rest environment afterEdge edgeValid)
          intro edges final finalValid
          exact ⟨finalValid, grows_refl _⟩
termination_by sizeOf expression
end

end MicroCFTA.InternedFreshOrdinaryGrowth
