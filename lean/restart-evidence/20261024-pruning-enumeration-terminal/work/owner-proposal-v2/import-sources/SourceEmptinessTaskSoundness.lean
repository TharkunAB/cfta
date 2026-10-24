import MicroCFTA.SourceEmptinessTaskRequirements
import MicroCFTA.SourceEmptinessTaskEntryRows
import MicroCFTA.SourceEmptinessTaskTableReadback
import MicroCFTA.SourceEqualityPCSConstructors

/-!
# Soundness of completed scoped task tables

Actual exposure supplies an accepted stored row. Saved class results and
complete task reads supply smaller accepted requirements in the final heap.
These witnesses derive the finite fixed-point decomposition. No final row,
inventory, primitive-operation, or decomposition oracle is assumed.

This theorem concerns reached complete-record traces in the scoped native
model. Exact lazy row demand, checked native allocation, machine bounds, and
general exploration completion remain separate obligations.
-/
namespace MicroCFTA.SourceEmptinessTaskSoundness
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEmptinessTaskTrace SourceEmptinessTaskTableReadback
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "TaskState" => SourceEmptinessTasks.State
local notation "Value" => InternedConstructorTemplates.Value Symbol Guard
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Actual completed source task rows derive all necessary smaller-witness obligations. -/
theorem decomposes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (trace : Run (width := width) top conjoin budget [] pending before final after)
    (ready : SourceEmptinessTasks.Ready top conjoin before)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap (heap before))
    (saved : SourceEmptinessTaskLanguage.Saved (SourceEqualityPCSGuard.holds formulas solver) before) :
    ConservativeEmptiness.Decomposes (ConservativeEmptinessTable.rows (table after final))
      (fun key => meaning (SourceEqualityPCSGuard.holds formulas solver) ambient
        (valueAt after final (records trace ready) key)) Term.height := by
  have finalReady := (shared_effects trace ready).1
  have coherent := finalReady.native.semantic.ready.semantic.1.normal.facts.coherent
  have finalSaved := SourceEmptinessTaskLanguage.run_saved (SourceEqualityPCSGuard.holds formulas solver)
    (SourceEqualityPCSConstructors.conjoined GuardStructuralOrder.le formulas solver) trace ready saved
  intro key term accepted
  obtain ⟨entry, found, same⟩ := entry_value after final (records trace ready) coherent key
  have original : meaning (SourceEqualityPCSGuard.holds formulas solver) ambient entry.value term := by
    simpa only [same] using accepted
  obtain ⟨sourceRow, taskRow, member, receipt, active, satisfied, symbol, terms, shape, forest⟩ :=
    (SourceEmptinessTaskEntryRows.entry formulas solver ambient trace ready fields key.val entry found).2 term original
  subst term
  have complete : ∀ task ∈ taskRow, Complete after task := by
    intro task selected
    exact rows_complete trace ready key.val entry found task (List.mem_flatten.mpr ⟨taskRow, member, selected⟩)
  have witnesses := SourceEmptinessTaskRequirements.row_witness (SourceEqualityPCSGuard.holds formulas solver)
    ambient finalSaved receipt active symbol terms satisfied forest complete
  have tableFound : ConservativeEmptinessExplore.lookup key.val (table after final) =
      some (entry.rows.map (List.map (readItem after))) := by
    rw [lookup_table, found]
    rfl
  refine ⟨taskRow.map (fun task => ConservativeEmptinessTable.classify (table after final) (readItem after task)), ?_, ?_⟩
  · simp only [ConservativeEmptinessTable.rows, tableFound, Option.getD_some, List.map_map, Function.comp_def]
    exact List.mem_map.mpr ⟨taskRow, member, rfl⟩
  · intro requirement selected
    obtain ⟨task, member, rfl⟩ := List.mem_map.mp selected
    obtain ⟨value, part, completed, acceptedPart, smaller⟩ := witnesses task member
    obtain ⟨actual, actualRead, available, closed, encoded⟩ := readItem_complete (complete task member)
    have actualValue : actual = value := Option.some.inj (actualRead.symm.trans completed)
    subst actual
    rw [encoded]
    exact value_obligation after final (records trace ready) coherent (SourceEqualityPCSGuard.holds formulas solver)
      ambient (.node symbol terms) part value available closed acceptedPart smaller

/-- A true decision on an actual completed task table excludes every accepted input term. -/
theorem excludes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (trace : Run (width := width) top conjoin budget [] pending before final after)
    (ready : SourceEmptinessTasks.Ready top conjoin before)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap (heap before))
    (saved : SourceEmptinessTaskLanguage.Saved (SourceEqualityPCSGuard.holds formulas solver) before)
    (query : Value) (available : Available (heap before) query) (closed : query.free = [])
    (empty : ConservativeEmptinessTable.provablyEmpty (table after final) (encode query) = true) :
    ∀ term, ¬meaning (SourceEqualityPCSGuard.holds formulas solver) ambient query term := by
  have effects := shared_effects trace ready
  have coherent := effects.1.native.semantic.ready.semantic.1.normal.facts.coherent
  have finiteEmpty : ConservativeEmptiness.provablyEmpty (ConservativeEmptinessTable.states (table after final))
      (ConservativeEmptinessTable.rows (table after final))
      (ConservativeEmptinessTable.classify (table after final) (encode query)) = true := by
    rwa [← ConservativeEmptinessTable.provablyEmpty_agrees]
  have sound := ConservativeEmptiness.provablyEmpty_sound (ConservativeEmptinessTable.states (table after final))
    (ConservativeEmptinessTable.states_complete (table after final)) (ConservativeEmptinessTable.rows (table after final))
    (fun key => meaning (SourceEqualityPCSGuard.holds formulas solver) ambient
      (valueAt after final (records trace ready) key)) Term.height
    (decomposes formulas solver ambient trace ready fields saved) _ finiteEmpty
  intro term accepted
  apply sound term
  have readback := classified after final (records trace ready) coherent query (effects.2.1.available query available) closed
  cases classification : ConservativeEmptinessTable.classify (table after final) (encode query) with
  | empty =>
      have same : query = .empty := by simpa only [classification] using readback
      subst query
      simp only [meaning] at accepted
  | outside => trivial
  | inside key =>
      have same : query = valueAt after final (records trace ready) key := by simpa only [classification] using readback
      simpa only [same, ConservativeEmptiness.AcceptsRequirement] using accepted

/-- Every completed equality-stop loop gives the same sound decision on the actual task table. -/
theorem grow_excludes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (trace : Run (width := width) top conjoin budget [] pending before final after)
    (ready : SourceEmptinessTasks.Ready top conjoin before)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap (heap before))
    (saved : SourceEmptinessTaskLanguage.Saved (SourceEqualityPCSGuard.holds formulas solver) before)
    (query : Value) (available : Available (heap before) query) (closed : query.free = [])
    (fuel : Nat) (known : Int → Bool)
    (done : ConservativeEmptinessTable.grow (table after final) fuel (fun _ => false) = some known)
    (empty : (!ConservativeEmptinessTable.rawCanAccept (table after final) known (encode query)) = true) :
    ∀ term, ¬meaning (SourceEqualityPCSGuard.holds formulas solver) ambient query term := by
  have same := ConservativeEmptinessTable.grow_rounds_result (table after final) fuel 0 known done
  rw [same] at empty
  exact excludes formulas solver ambient trace ready fields saved query available closed empty

/-- A fresh task scope derives its initial saved semantics without a semantic input oracle. -/
theorem initial_excludes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : SourceEqualityNativeScoped.IdleReady top conjoin native)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap native.machine.heap)
    (trace : Run top conjoin budget [] pending (SourceEmptinessTasks.start native) final after)
    (query : Value) (available : Available native.machine.heap query) (closed : query.free = [])
    (empty : ConservativeEmptinessTable.provablyEmpty (table after final) (encode query) = true) :
    ∀ term, ¬meaning (SourceEqualityPCSGuard.holds formulas solver) ambient query term :=
  excludes formulas solver ambient trace (SourceEmptinessTasks.start_ready native ready) fields
    (SourceEmptinessTaskLanguage.start_saved (SourceEqualityPCSGuard.holds formulas solver) native)
    query available closed empty

/-- Original normalized construction derives the input domain and excludes its declared syntax language. -/
theorem source_excludes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (annotations : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ value before, InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty =
        .done value before ∧
      ∀ budget final after,
        Run top conjoin budget [] [SourceEmptinessTasks.Task.value value] (initial width before) final after →
        ConservativeEmptinessTable.provablyEmpty (table after final) (encode value) = true →
        ∀ term, ¬InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) [] expression term := by
  obtain ⟨value, before, built, ready, fields, available, closed⟩ := source width expression annotations
  refine ⟨value, before, built, ?_⟩
  intro budget final after trace empty term
  have sound := excludes formulas solver (fun _ _ => False) trace ready fields
    (SourceEmptinessTaskLanguage.start_saved (SourceEqualityPCSGuard.holds formulas solver) _)
    value available closed empty term
  simpa only [InternedGuardedExecution.closed_language expression value before built
    (SourceEqualityPCSGuard.holds formulas solver) (fun _ _ => False)] using sound

end MicroCFTA.SourceEmptinessTaskSoundness
