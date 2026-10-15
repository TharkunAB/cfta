import MicroCFTA.SourceCurrentEqualityClassScan
import MicroCFTA.SourcePrimaryGateEffects
import MicroCFTA.SourceCurrentSecondaryQueryReady

/-!
# Sound reached current class scans with the fourth memo

Actual primary and current secondary gates derive their returned invariants.
Pure gate effects retain the separate emptiness memo's complete records.
Queried classes use actual seeded operations and completed memo hits or
misses. Satisfied accepted inputs exclude a true answer. Earlier completed
memo entries survive every reached class. No final invariant is assumed.
The three global gate memo tables and source fallback remain separate.
-/
namespace MicroCFTA.SourceCurrentEqualityClassScanSoundness
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceCurrentEqualityClassScan
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap

/-- An actual primary class advances the same native state and retains its original inputs. -/
theorem primary_advance [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : Class} {before : Native width Symbol Guard}
    {answer : Bool} {heap : State Symbol Guard}
    (trace : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.machine.heap answer heap)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap) :
    IdleReady top conjoin (advanceHeap before heap) ∧ CostHeap heap ∧ FieldHeap heap ∧
      Keeps before.machine.heap heap ∧ Values heap values := by
  have checked := SourcePrimaryGateEffects.class_effects
    (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
    unconstrained reaches trace ready.semantic costs available fields
  exact ⟨ready.advance heap checked.2.1 checked.1, checked.2.2.1, checked.2.2.2, checked.2.1,
    fun value member => checked.2.1.available value (available value member)⟩

/-- Either actual current-secondary answer derives every invariant at its returned heap. -/
theorem secondary_advance [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : Class} {before : Native width Symbol Guard}
    {answer : Bool} {heap : State Symbol Guard}
    (trace : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.machine.heap answer heap)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap) :
    IdleReady top conjoin (advanceHeap before heap) ∧ CostHeap heap ∧ FieldHeap heap ∧
      Keeps before.machine.heap heap ∧ Values heap values := by
  have checked := SourceCurrentSecondaryEffects.class_effects
    (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
    unconstrained trace ready.semantic costs available fields
  exact ⟨ready.advance heap checked.2.1 checked.1, checked.2.2.1, checked.2.2.2, checked.2.1,
    fun value member => checked.2.1.available value (available value member)⟩

/-- Accepted satisfied inputs derive all reached final invariants and exclude early rejection. -/
theorem verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {outcome : Option Class} {before after : Native width Symbol Guard}
    {memo saved : Memo}
    (trace : Scan unconstrained reaches values classes before memo outcome selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap) (active : Active classes)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)
    (satisfied : Satisfies (.node symbol terms) classes) :
    outcome = none ∧ IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  revert satisfied active correct fields costs available ready
  induction trace with
  | nil =>
      intro ready available costs fields _ correct _
      exact ⟨rfl, ready, costs, fields, pure_keeps _ ready.semantic.ready, available, correct,
        fun _ _ found => found⟩
  | selected primary rest ih =>
      intro ready available costs fields active correct satisfied
      obtain ⟨nextReady, nextCosts, nextFields, first, nextValues⟩ :=
        primary_advance unconstrained reaches primary ready available costs fields
      have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver first _ correct
      obtain ⟨none, finalReady, finalCosts, finalFields, later, finalValues, finalCorrect, extension⟩ :=
        ih nextReady nextValues nextCosts nextFields
          (fun paths member => active paths (List.mem_cons_of_mem _ member)) nextCorrect
          (fun paths member => satisfied paths (List.mem_cons_of_mem _ member))
      exact ⟨none, finalReady, finalCosts, finalFields, first.trans later, finalValues, finalCorrect, extension⟩
  | skipped primary secondary rest ih =>
      intro ready available costs fields active correct satisfied
      obtain ⟨primaryReady, primaryCosts, primaryFields, first, primaryValues⟩ :=
        primary_advance unconstrained reaches primary ready available costs fields
      obtain ⟨nextReady, nextCosts, nextFields, second, nextValues⟩ :=
        secondary_advance unconstrained secondary primaryReady primaryValues primaryCosts primaryFields
      have nextCorrect := SourceCurrentEmptinessMemo.grows formulas solver (first.trans second) _ correct
      obtain ⟨none, finalReady, finalCosts, finalFields, later, finalValues, finalCorrect, extension⟩ :=
        ih nextReady nextValues nextCosts nextFields
          (fun paths member => active paths (List.mem_cons_of_mem _ member)) nextCorrect
          (fun paths member => satisfied paths (List.mem_cons_of_mem _ member))
      exact ⟨none, finalReady, finalCosts, finalFields, first.trans (second.trans later),
        finalValues, finalCorrect, extension⟩
  | continued primary secondary seeded decision rest ih =>
      intro ready available costs fields active correct satisfied
      obtain ⟨primaryReady, primaryCosts, primaryFields, first, primaryValues⟩ :=
        primary_advance unconstrained reaches primary ready available costs fields
      have primaryCorrect := SourceCurrentEmptinessMemo.grows formulas solver first _ correct
      obtain ⟨nextReady, nextCosts, nextFields, second, nextValues, nextCorrect, firstExtends⟩ :=
        SourceCurrentSecondaryQueryReady.queried_memo_effects unconstrained _ (active _ List.mem_cons_self) values
          secondary seeded decision primaryReady primaryValues primaryCosts primaryFields formulas solver primaryCorrect
          symbol terms (satisfied _ List.mem_cons_self)
      obtain ⟨none, finalReady, finalCosts, finalFields, later, finalValues, finalCorrect, laterExtends⟩ :=
        ih nextReady nextValues nextCosts nextFields
          (fun paths member => active paths (List.mem_cons_of_mem _ member)) nextCorrect
          (fun paths member => satisfied paths (List.mem_cons_of_mem _ member))
      exact ⟨none, finalReady, finalCosts, finalFields, first.trans (second.trans later),
        finalValues, finalCorrect, fun key entry found => laterExtends key entry (firstExtends key entry found)⟩
  | stopped primary secondary seeded decision =>
      intro ready available costs fields active correct satisfied
      obtain ⟨primaryReady, primaryCosts, primaryFields, first, primaryValues⟩ :=
        primary_advance unconstrained reaches primary ready available costs fields
      have primaryCorrect := SourceCurrentEmptinessMemo.grows formulas solver first _ correct
      exact False.elim ((SourceCurrentSecondaryQueryReady.refutes_memo unconstrained _ (active _ List.mem_cons_self)
        values secondary seeded decision primaryReady primaryValues primaryCosts primaryFields
        formulas solver primaryCorrect ambient symbol terms accepted) (satisfied _ List.mem_cons_self))

/-- Every actual stopped prefix refutes the original active constraints of an accepted forest. -/
theorem stopped_refutes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {paths : Class} {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan unconstrained reaches values classes before memo (some paths) selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap) (active : Active classes)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬Satisfies (.node symbol terms) classes := by
  intro satisfied
  have impossible := (verified trace ready available costs fields active formulas solver correct
    ambient symbol terms accepted satisfied).1
  cases impossible

end MicroCFTA.SourceCurrentEqualityClassScanSoundness
