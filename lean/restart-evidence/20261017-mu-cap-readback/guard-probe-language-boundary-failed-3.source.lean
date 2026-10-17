import MicroCFTA.InternedGuardedBudgetExecution
import MicroCFTA.InternedFreshOrdinarySemanticOrigins
import MicroCFTA.SourceCurrentConstrainedCap
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

namespace MicroCFTA.GuardProbeLanguageBoundary
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open SourceCurrentConstrainedCap (Cap)

private def expression : Syntax Nat Bool := .binder false (.node [.mk 0 false [.var 0]])
private def actual := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Nat Bool := match actual with
  | .done result _ => result
  | .pending .. => .empty
private def isBadLoop : Value Nat Bool → Bool
  | .mu entry (.node _ [.mk row [.reference (.interned self)]] _ _) _ _ =>
      decide (self = entry.identity) && !row.key.constraint
  | _ => false

set_option cbv.maxSteps 100000000 in
private theorem observed : isBadLoop value = true := by cbv

set_option cbv.maxSteps 100000000 in
private theorem completed : actual = .done value actual.state := by cbv

private theorem shape (result : Value Nat Bool) (bad : isBadLoop result = true) :
    ∃ entry node row level free probe ordinary,
      result = .mu entry (.node node [.mk row [.reference (.interned entry.identity)]] level free) probe ordinary ∧
      row.key.constraint = false := by
  cases result with
  | empty | reference | node | union => simp [isBadLoop] at bad
  | mu entry body probe ordinary =>
      cases body with
      | empty | reference | union | mu => simp [isBadLoop] at bad
      | node node edges level free =>
          cases edges with
          | nil => simp [isBadLoop] at bad
          | cons first rest =>
              cases rest with
              | cons => simp [isBadLoop] at bad
              | nil =>
                  cases first with
                  | mk row children =>
                      cases children with
                      | nil => simp [isBadLoop] at bad
                      | cons child rest =>
                          cases rest with
                          | cons => simp [isBadLoop] at bad
                          | nil =>
                              cases child with
                              | empty | node | union | mu => simp [isBadLoop] at bad
                              | reference name =>
                                  cases name with
                                  | depth | uninterned | intersection | state => simp [isBadLoop] at bad
                                  | interned self =>
                                      have both := Bool.and_eq_true_iff.mp bad
                                      have same : self = entry.identity := of_decide_eq_true both.1
                                      subst self
                                      exact ⟨entry, node, row, level, free, probe, ordinary, rfl,
                                        by cases found : row.key.constraint <;> simp_all⟩

private theorem not_capped (entry : Interned NodeKey) (node : Interned NodeKey)
    (row : Interned (EdgeKey Nat Bool)) (level : Nat) (free : List Reference)
    (probe ordinary : Value Nat Bool) (bad : row.key.constraint = false) (depth : Nat) :
    ¬Cap (fun guard => guard = true) depth
      (.mu entry (.node node [.mk row [.reference (.interned entry.identity)]] level free) probe ordinary) := by
  intro bounded
  cases bounded with
  | plain _ annotated =>
      cases annotated with
      | mu _ _ _ _ body =>
          cases body with
          | node _ _ _ _ guards _ =>
              have impossible := guards (.mk row [.reference (.interned entry.identity)]) List.mem_cons_self
              change row.key.constraint = true at impossible
              rw [bad] at impossible
              cases impossible

private theorem budget_empty (entry : Interned NodeKey) (node : Interned NodeKey)
    (row : Interned (EdgeKey Nat Bool)) (level : Nat) (free : List Reference)
    (probe ordinary : Value Nat Bool) (holds : Bool → Language.Term Nat → Bool)
    (environment : InternedGuardedBudget.Env Nat) (budget : Nat) (term : Language.Term Nat) :
    ¬InternedGuardedBudget.meaning holds environment
      (.mu entry (.node node [.mk row [.reference (.interned entry.identity)]] level free) probe ordinary) budget term := by
  intro accepted
  rw [InternedGuardedBudget.meaning] at accepted
  change BinderBudgetLanguage.least _ budget term at accepted
  exact accepted (fun _ _ => False) (by intro _ _ _ _ impossible; exact impossible) (by
    rintro bound tree ⟨smaller, _less, body⟩
    simp only [InternedGuardedBudget.meaning] at body
    obtain ⟨⟨edge, member⟩, accepted⟩ := body
    have same := List.mem_singleton.mp member
    subst edge
    simp only [InternedGuardedBudget.edgeMeaning] at accepted
    obtain ⟨terms, _shape, children, _guard⟩ := accepted
    cases terms with
    | nil => simp only [InternedGuardedBudget.forest] at children
    | cons first rest =>
        simpa only [InternedGuardedBudget.forest, InternedGuardedBudget.meaning, InternedGuardedBudget.bind, ↓reduceIte] using (show _ ∧ _ from children).1)

/-- An actual closed source Mu is nonhereditary at every cap depth but has empty guarded budget language for every guard interpretation. -/
theorem source_built_language_does_not_reflect_cap :
    ∃ result after,
      InternedFreshOrdinaryConstruction.build expression [] (empty : State Nat Bool) = .done result after ∧
      Available after result ∧ SourceRecursiveIntersectionSemanticHeap.SemanticHeap after ∧
      InternedFreshOrdinarySemanticOrigins.Heap after ∧ InternedGuardedBudgetProbeHeap.Heap after ∧
      (∀ depth, ¬Cap (fun guard => guard = true) depth result) ∧
      ∀ holds environment budget term, ¬InternedGuardedBudget.meaning holds environment result budget term := by
  have done := completed
  have available := (InternedFreshOrdinaryFacts.build_verified expression [] (empty : State Nat Bool) empty_facts
    (by intro item member; cases member)).result value actual.state done
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed expression value actual.state done
  have origins := InternedFreshOrdinarySemanticOrigins.closed_origins expression
  have budgets := InternedGuardedBudgetExecution.closed_heap expression
  have originHeap : InternedFreshOrdinarySemanticOrigins.Heap actual.state := by simpa only [actual] using origins
  have budgetHeap : InternedGuardedBudgetProbeHeap.Heap actual.state := by simpa only [actual] using budgets
  obtain ⟨entry, node, row, level, free, probe, ordinary, same, bad⟩ := shape value observed
  exact ⟨value, actual.state, done, available, semantic, originHeap, budgetHeap,
    fun depth => same ▸ not_capped entry node row level free probe ordinary bad depth,
    fun holds environment budget term => same ▸ budget_empty entry node row level free probe ordinary holds environment budget term⟩

#print axioms source_built_language_does_not_reflect_cap
#check @source_built_language_does_not_reflect_cap
end MicroCFTA.GuardProbeLanguageBoundary
