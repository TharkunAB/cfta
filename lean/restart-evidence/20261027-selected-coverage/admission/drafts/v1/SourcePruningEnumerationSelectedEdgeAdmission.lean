import MicroCFTA.SourcePruningEnumerationEdgeProjectionLanguage
import MicroCFTA.SourcePruningEnumerationAnnotationHeap
import MicroCFTA.EnumerationState

/-!
# Admission from an accepted current selected edge

An accepted native guard supplies its actual successful projection.
The accepted parent term supplies the inherited arity check.
The current Context supplies normalized annotations at the selected heap.
These results do not assert operational completion or reserve word capacity.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdgeAdmission
open Language EnumerationState EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance

/-- An accepted cached guard derives the actual projection and both semantic parts. -/
theorem projected_of_accepted {Formula : Type} [DecidableEq Formula]
    (formulas : SourceGuards.Formulas Formula)
    (solver : SourceGuards.Entailment Formula)
    (constraint : SourceSymbolicIndex.Constraint Formula)
    (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (term : Term (SourceObservations.Label Formula))
    (accepted : SourceEqualityPCSGuard.holds formulas solver constraint term = true) :
    ∃ (tries : List EqualityTrie.Trie) (residual : Option (SourceSymbolicIndex.Constraint Formula)),
      SourcePruningEnumerationConstraint.project constraint = some (tries, residual) ∧
      (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      (∀ trie ∈ tries, EqualityHolds term trie) ∧
      ResidualHolds (fun guard candidate =>
        SourceEqualityPCSGuard.holds formulas solver guard candidate = true) residual term := by
  have complete := SourcePruningEnumerationConstraint.project_complete constraint cached
  cases source : SourceCompactGuards.sourceEqualities constraint with
  | none =>
      simp only [source] at complete
      exact False.elim (complete.2 formulas solver term accepted)
  | some classes =>
      simp only [source] at complete
      refine ⟨EnumerationEquality.readClasses classes,
        if (SourceCompactGuards.positive constraint.guard).isSome then none else some constraint,
        complete.1, complete.2.1, ?_⟩
      exact (complete.2.2.2 formulas solver term).mp accepted

local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)

/-- Actual edge acceptance derives the selected projection, ordered children, and inherited arity. -/
theorem selected_admission {width : Nat} [DecidableEq (EdgeKey Symbol Constraint)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended)
    (initial : Context formulas solver inventory caller memos)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (selected : edge ∈ edges)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Term Symbol) (term : Term Symbol)
    (accepted : InternedGuardedLanguage.edgeMeaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)
    (inherited : ∀ sc ∈ scs, Suspended.Holds assignment term sc) :
    ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint) (terms : List (Term Symbol)),
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      term = .node edge.entry.key.symbol terms ∧
      Language.All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
        edge.children terms ∧
      edge.children.length = terms.length ∧
      arityAllows edge.children.length scs = true ∧
      (∀ trie ∈ tries, EqualityHolds term trie) ∧
      ResidualHolds (fun guard candidate =>
        SourceEqualityPCSGuard.holds formulas solver guard candidate = true) residual term := by
  obtain ⟨terms, shape, runs, guarded⟩ :=
    (InternedGuardedLanguage.edgeMeaning_all
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge term).mp accepted
  have ready := initial.ready.semantic.ready
  have resident : InternedEdgeResidency.EdgeResident caller.checked.native.machine.heap edge :=
    InternedEdgeResidency.resident_edges caller.checked.native.machine.heap
      ready.semantic.1.normal.facts.linked (.node parentEntry edges depth free)
      parentAvailable.resident edge selected
  have cached : SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities :=
    initial.annotation_heap edge.entry.key edge resident
  obtain ⟨tries, residual, projected, valid, own, remaining⟩ :=
    projected_of_accepted formulas solver edge.entry.key.constraint cached term guarded
  have arity : arityAllows terms.length scs = true :=
    suspended_arity_necessary assignment edge.entry.key.symbol terms scs (by
      intro sc member
      simpa only [shape] using inherited sc member)
  refine ⟨tries, residual, terms, projected, valid, shape, runs, runs.length_eq, ?_, own, remaining⟩
  rw [runs.length_eq]
  exact arity

end MicroCFTA.SourcePruningEnumerationSelectedEdgeAdmission
