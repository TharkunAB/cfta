import MicroCFTA.SourcePruningEnumerationSelectedEdgeAdmission
import MicroCFTA.SourcePruningEnumerationEdgeInputs
import MicroCFTA.SourcePruningEnumerationStorageProgress
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.EnumerationSuspendedForward

/-!
# One accepted assignment for the actual own-class prefix

The original accepted parent derives the actual projection and child terms.
The actual own-class packet remains complete. One fresh assignment supplies
all original child buckets and preserves the original pending graph cost.
-/
namespace MicroCFTA.SourcePruningEnumerationOwnChildModelProgress
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation
open SourcePruningEnumerationEdgeInputs (children)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}

private theorem child_models
    (holds : Constraint → Term Symbol → Bool)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Term Symbol) (edge : EdgeValue Symbol Constraint)
    (scs : List Suspended) (ownStart : Nat) (tries : List EqualityTrie.Trie)
    (terms : List (Term Symbol))
    (accepted : All₂ (InternedGuardedLanguage.meaning holds ambient) edge.children terms)
    (combined : ∀ sc ∈ scs ++ suspendedVars ownStart tries,
      Suspended.Holds assignment (.node edge.entry.key.symbol terms) sc) :
    All₂ (fun input term =>
      InternedGuardedLanguage.meaning holds ambient input.1 term ∧
      ∀ sc ∈ input.2, Suspended.Holds assignment term sc)
      (SourcePruningEnumerationEdgeInputs.children edge scs ownStart tries) terms := by
  have descended := suspended_descent_forward assignment edge.entry.key.symbol terms
    (scs ++ suspendedVars ownStart tries) combined
  have indexed : ∀ (nodes : List Node) (values : List (Language.Term Symbol)),
      Language.All₂ (InternedGuardedLanguage.meaning (holds)
        ambient) nodes values →
      ∀ start,
        (∀ index child, values[index]? = some child →
          ∀ sc ∈ descendScs (start + index) (scs ++ suspendedVars ownStart tries),
            Suspended.Holds assignment child sc) →
        Language.All₂ (fun indexed child =>
          InternedGuardedLanguage.meaning (holds)
            ambient indexed.1 child ∧
          ∀ sc ∈ descendScs indexed.2 (scs ++ suspendedVars ownStart tries),
            Suspended.Holds assignment child sc) (nodes.zipIdx start) values := by
    intro nodes values related
    induction related with
    | nil => intro start _; exact .nil
    | cons head tail ih =>
        intro start holds
        simp only [List.zipIdx_cons]
        apply Language.All₂.cons
        · exact ⟨head, by simpa only [Nat.add_zero] using holds 0 _ rfl⟩
        · apply ih (start + 1)
          intro index child found
          have evidence := holds (index + 1) child found
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using evidence
  have indexedModels := indexed edge.children terms accepted 0 (by simpa only [Nat.zero_add] using descended)
  have inputModels : Language.All₂ (fun input term =>
      InternedGuardedLanguage.meaning (holds)
        ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds assignment term sc) (SourcePruningEnumerationEdgeInputs.children edge scs ownStart tries) terms := by
    have mapped := EnumerationSemantics.all₂_map_both
      (fun indexed : Node × Nat => (indexed.1,
        descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars ownStart tries)))
      id
      (fun indexed child =>
        InternedGuardedLanguage.meaning (holds)
          ambient indexed.1 child ∧
        ∀ sc ∈ descendScs indexed.2 (scs ++ suspendedVars ownStart tries),
          Suspended.Holds assignment child sc)
      (fun input term =>
        InternedGuardedLanguage.meaning (holds)
          ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds assignment term sc)
      (fun _ _ evidence => ⟨evidence.1, by
        simpa only [id_eq, descendScs, EqualityTrie.descendScs, List.map_append, List.filter_append]
          using evidence.2⟩)
      edge.children.zipIdx terms indexedModels
    simpa only [SourcePruningEnumerationEdgeInputs.children, List.map_id] using mapped
  exact inputModels

variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Preserve the actual own-class packet and construct its original compatible child model and cost. -/
theorem accepted_own_children
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Term Symbol) (term : Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core)
    (accepted : InternedGuardedLanguage.edgeMeaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)
    (inherited : ∀ sc ∈ scs, Suspended.Holds assignment term sc) :
    ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint) (terms : List (Term Symbol)),
      (SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      term = .node edge.entry.key.symbol terms ∧
      Language.All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
        edge.children terms ∧
      edge.children.length = terms.length ∧
      arityAllows edge.children.length scs = true ∧
      (∀ trie ∈ tries, EqualityHolds term trie) ∧
      ResidualHolds (fun guard candidate =>
        SourceEqualityPCSGuard.holds formulas solver guard candidate = true) residual term) ∧
    ∃ (action : EnumerateM Symbol Constraint
        (Symbol × List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)) × Option Constraint))
      (after : Cached),
      (SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((edge.entry.key.symbol,
          (children edge scs before.core.counter tries).map (fun input =>
            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), after)] ∧
      ExceptT.run (action before.core) =
        [.ok ((edge.entry.key.symbol,
          (children edge scs before.core.counter tries).map (fun input =>
            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), after.core)] ∧
      after.core = suspendedState tries.length before.core ∧
      after.core.counter = before.core.counter + tries.length ∧
      after.core.representatives = before.core.representatives ∧
      Safe after.core ∧ Roots after.core.representatives roots ∧ PendingRealized caller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      InputsPending after.core (scs ++ suspendedVars before.core.counter tries) ∧
      (∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
        Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
        (∀ sc ∈ bucket, sc.var < after.core.counter) ∧ InputsPending after.core bucket) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs →
        EnumerationDriver.Protected held before.core after.core ∧
          ∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
            Avoids after.core.representatives held bucket)) ∧
    ∃ extended : Nat → Term Symbol,
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
        extended before.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
        extended after.core ∧
      (∀ sc ∈ scs ++ suspendedVars before.core.counter tries, Suspended.Holds extended term sc) ∧
      All₂ (fun input child =>
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input.1 child ∧
        ∀ sc ∈ input.2, Suspended.Holds extended child sc)
        (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries) terms ∧
      EnumerationStorageProgress.pendingSize after.core extended =
        EnumerationStorageProgress.pendingSize before.core assignment := by
  obtain ⟨tries, residual, terms, projected, valid, shape, childAccepted,
    length, allowed, ownEqualities, residualHeld⟩ :=
    SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory caller memos
      parentEntry edges depth free edge scs initial parentAvailable selected ambient assignment term accepted inherited
  obtain ⟨action, after, packet⟩ :=
    SourcePruningEnumerationEdgeInputs.complete caller.checked.native.machine.heap parentEntry edges depth free
      edge scs roots initial.ready.semantic.ready parentAvailable parentClosed selected before safe realized
      paths counts flags bounded pending allowed tries residual projected
  have coreSame := packet.2.2.2.1
  obtain ⟨extended, ownSatisfied, agree, freshHeld⟩ :=
    fresh_classes_state_complete
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      before.core safe.1 assignment satisfied term tries ownEqualities
  rw [← coreSame] at ownSatisfied
  have originalSatisfied := (state_assignment_congr
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap)
    (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
    before.core safe.1 extended assignment agree).mpr satisfied
  have combined : ∀ sc ∈ scs ++ suspendedVars before.core.counter tries,
      Suspended.Holds extended term sc := by
    intro sc member
    rcases List.mem_append.mp member with old | fresh
    · exact EnumerationConstruction.holds_extension assignment extended before.core.counter
        agree sc (bounded sc old) term (inherited sc old)
    · exact freshHeld sc fresh
  have models := child_models (SourceEqualityPCSGuard.holds formulas solver) ambient extended edge
    scs before.core.counter tries terms childAccepted (by simpa only [shape] using combined)
  have observed := packet.2.1
  simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected,
    Option.map_eq_some_iff] at observed
  obtain ⟨suspended, suspension, same⟩ := observed
  have cacheSame : suspended.2 = after := by
    simpa using
      congrArg (List.map Prod.snd) same
  have cost := SourcePruningEnumerationStorageProgress.suspendMany_pendingSize
    caller.checked.native.machine.heap tries before suspended.2 suspended.1 extended suspension
  rw [cacheSame] at cost
  have oldCost : EnumerationStorageProgress.pendingSize before.core extended =
      EnumerationStorageProgress.pendingSize before.core assignment := by
    apply EnumerationStorageProgress.pendingSize_assignment_congr
    intro uv inside
    have aligned : before.core.counter = before.core.values.length := safe.1.aligned
    exact agree uv (by omega)
  refine ⟨tries, residual, terms,
    ⟨projected, valid, shape, childAccepted, length, allowed, ownEqualities, residualHeld⟩,
    action, after, packet, extended, agree, originalSatisfied, ownSatisfied, combined, models, ?_⟩
  exact cost.trans oldCost

end MicroCFTA.SourcePruningEnumerationOwnChildModelProgress
