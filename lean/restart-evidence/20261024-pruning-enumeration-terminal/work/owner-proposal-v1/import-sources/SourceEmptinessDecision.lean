import MicroCFTA.SourceEmptinessTaskSoundness

/-!
# Demand branches of the conservative emptiness query

An empty query returns true without exploration or fixed-point work. A
missing key returns false after exploration without reading the fixed point.
A present key uses the completed equality-stop result. Native caches pass
through the fresh local task scope. Exploration still uses complete row reads.
This graph does not prove GHC demand correspondence or general completion.
-/
namespace MicroCFTA.SourceEmptinessDecision
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEmptinessTaskTrace
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Value" => InternedConstructorTemplates.Value Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- A completed query retains only the source branches it demands. -/
inductive Decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    Value → Native width Symbol Guard → Bool → Native width Symbol Guard → Prop where
  | empty : Decision .empty before true before
  | missing (nonempty : query ≠ .empty)
      (trace : Run top conjoin budget [] [SourceEmptinessTasks.Task.value query]
        (SourceEmptinessTasks.start before) entries after)
      (encoded : encode query = .resident identity closed)
      (absent : ConservativeEmptinessExplore.lookup identity (table after entries) = none) :
      Decision query before false after.native
  | known (nonempty : query ≠ .empty)
      (trace : Run top conjoin budget [] [SourceEmptinessTasks.Task.value query]
        (SourceEmptinessTasks.start before) entries after)
      (encoded : encode query = .resident identity closed)
      (present : ConservativeEmptinessExplore.lookup identity (table after entries) = some rows)
      (done : ConservativeEmptinessTable.grow (table after entries) fuel (fun _ => false) = some known)
      (answer : result = !ConservativeEmptinessTable.rawCanAccept (table after entries) known (encode query)) :
      Decision query before result after.native

/-- EmptyNode has the source's immediate true result and changes no native state. -/
theorem empty_no_work [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {before after : Native width Symbol Guard} {answer : Bool} (trace : Decision .empty before answer after) :
    answer = true ∧ after = before := by
  cases trace with
  | empty => exact ⟨rfl, rfl⟩
  | missing nonempty => exact False.elim (nonempty rfl)
  | known nonempty => exact False.elim (nonempty rfl)

/-- Completed exploration of a closed nonempty query derives a finite demanded decision branch. -/
theorem explored [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {query : Value} {before : Native width Symbol Guard}
    (nonempty : query ≠ .empty)
    (trace : Run top conjoin budget [] [SourceEmptinessTasks.Task.value query]
      (SourceEmptinessTasks.start before) entries after)
    (available : Available before.machine.heap query) (closed : query.free = []) :
    ∃ answer, Decision query before answer after.native := by
  cases encoded : encode query with
  | empty =>
      let certified : SourceEmptinessKeys.Closed before.machine.heap := ⟨query, available, closed⟩
      have impossible := (SourceEmptinessKeys.item_empty_iff certified).mp
        ((encode_closed before.machine.heap certified).symm.trans encoded)
      exact False.elim (nonempty (congrArg Subtype.val impossible))
  | resident identity flag =>
      cases found : ConservativeEmptinessExplore.lookup identity (table after entries) with
      | none => exact ⟨false, .missing nonempty trace encoded found⟩
      | some rows =>
          exact ⟨_, .known nonempty trace encoded found (grow_complete trace) rfl⟩

/-- Every demanded branch retains native readiness, physical history, and normalized fields. -/
theorem effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {query : Value} {before after : Native width Symbol Guard} {answer : Bool}
    (trace : Decision query before answer after) (ready : IdleReady top conjoin before)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap) :
    IdleReady top conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap := by
  cases trace with
  | empty => exact ⟨ready, pure_keeps _ ready.semantic.ready, fields⟩
  | missing nonempty actual encoded absent =>
      have initial := SourceEmptinessTasks.start_ready before ready
      have final := shared_effects actual initial
      exact ⟨final.1.native, final.2.1, SourceEmptinessTaskTrace.fields actual initial fields⟩
  | known nonempty actual encoded present done answer =>
      have initial := SourceEmptinessTasks.start_ready before ready
      have final := shared_effects actual initial
      exact ⟨final.1.native, final.2.1, SourceEmptinessTaskTrace.fields actual initial fields⟩

/-- A true query result excludes every term without demanding unused source branches. -/
theorem sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    {query : Value} {before after : Native width Symbol Guard}
    (trace : Decision query before true after) (ready : IdleReady top conjoin before)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap)
    (available : Available before.machine.heap query) (closed : query.free = []) :
    ∀ term, ¬meaning (SourceEqualityPCSGuard.holds formulas solver) ambient query term := by
  cases trace with
  | empty => intro term accepted; simp only [meaning] at accepted
  | known nonempty actual encoded present done answer =>
      exact SourceEmptinessTaskSoundness.grow_excludes formulas solver ambient actual
        (SourceEmptinessTasks.start_ready before ready) fields
        (SourceEmptinessTaskLanguage.start_saved (SourceEqualityPCSGuard.holds formulas solver) before)
        query available closed _ _ done answer.symm

end MicroCFTA.SourceEmptinessDecision
