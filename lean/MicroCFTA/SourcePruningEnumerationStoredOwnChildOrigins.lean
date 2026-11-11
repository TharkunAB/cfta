import MicroCFTA.SourcePruningEnumerationOwnChildModelProgress
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationSelectorLanguage
import MicroCFTA.SourcePruningEnumerationModelPathDomain
import MicroCFTA.EnumerationCompleteness

/-!
# An origin-aware own-class plan from a current stored model

The current slot model selects an actual ordinary row. The same constructor
plan retains its complete cache packet and one extended assignment.
The assignment bounds every stored suspended path by the original term.
-/
namespace MicroCFTA.SourcePruningEnumerationStoredOwnChildOrigins
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation SourcePruningEnumerationNodes
open SourcePruningEnumerationEdgeInputs (children)
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A stored model selects an actual row and derives its complete origin-aware own-class plan. -/
theorem stored_own_children_origins
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached)
    (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle =
      some (.node parentEntry edges depth free))
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core)
    (whole : Term Symbol)
    (old : SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment) :
    ∃ (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat),
      edge ∈ InternedEdgeResidency.nodeEdges (.node parentEntry edges depth free) ∧
      Roots before.core.representatives roots ∧
    ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint) (terms : List (Term Symbol)),
      (SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      (assignment uv) = .node edge.entry.key.symbol terms ∧
      Language.All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
        edge.children terms ∧
      edge.children.length = terms.length ∧
      arityAllows edge.children.length scs = true ∧
      (∀ trie ∈ tries, EqualityHolds (assignment uv) trie) ∧
      ResidualHolds (fun guard candidate =>
        SourceEqualityPCSGuard.holds formulas solver guard candidate = true) residual (assignment uv)) ∧
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
      (∀ sc ∈ scs ++ suspendedVars before.core.counter tries, Suspended.Holds extended (assignment uv) sc) ∧
      All₂ (fun input child =>
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input.1 child ∧
        ∀ sc ∈ input.2, Suspended.Holds extended child sc)
        (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries) terms ∧
      EnumerationStorageProgress.pendingSize after.core extended =
        EnumerationStorageProgress.pendingSize before.core assignment ∧
      SourcePruningEnumerationOrigins.AssignmentOrigins whole after.core.counter extended ∧
      (∀ child ∈ terms, SourcePruningEnumerationOrigins.Origin whole child) ∧
      ∀ (held : Nat) (node : Option Nat) (bucket : List Suspended),
        held < after.core.counter →
        after.core.values[held]? = some (.unenumerated node bucket) →
        ∀ sc ∈ bucket, ∀ path ∈ EqualityTrie.fromPathTrie sc.trie,
          path ∈ SourcePruningEnumerationModelPathDomain.relativePaths whole ∧
            (extended sc.var).height + path.length ≤ whole.height := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨value, found, available, closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free :=
    Option.some.inj (found.symm.trans decoded)
  subst value
  have model := EnumerationCompleteness.stored_satisfies
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap)
    (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
    assignment before.core satisfied uv (.unenumerated (some handle) scs) stored
  simp only [slot, Option.map_some, Fragments.slotSatisfies, List.forall_mem_map] at model
  have accepted : InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
      ambient (.node parentEntry edges depth free) (assignment uv) :=
    (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mp model.1
  obtain ⟨edge, selected, _original, _resident, edgeAccepted⟩ :=
    SourcePruningEnumerationSelectorLanguage.selected_accepting_of_perm
      caller.checked.native.machine.heap packet.context.ready.semantic.ready
      parentEntry edges edges depth free available (List.Perm.refl edges)
      (SourceEqualityPCSGuard.holds formulas solver) ambient (assignment uv) accepted
  have insideValues : uv < before.core.values.length := (List.getElem?_eq_some_iff.mp stored).1
  have inside : uv < before.core.counter := by
    have aligned : before.core.counter = before.core.values.length := packet.safe.1.aligned
    omega
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    packet.safe.1.values _ (List.mem_of_getElem? stored)
  have pending : InputsPending before.core scs :=
    EnumerationReferences.pending_inputs before.core packet.pending uv (some handle) scs stored
  obtain ⟨tries, residual, terms, projection, action, after, actualPacket, extended,
    agree, originalModel, afterModel, combined, models, cost, origins, childOrigins⟩ :=
    SourcePruningEnumerationOwnChildModelProgress.accepted_own_children_origins
      formulas solver inventory caller before parentEntry edges depth free edge scs roots memos
      packet.context available closed selected packet.safe realized paths counts flags bounded pending
      ambient assignment (assignment uv) satisfied edgeAccepted model.2 whole old (old uv inside)
  refine ⟨edge, roots, selected, paths, tries, residual, terms, projection, action, after,
    actualPacket, extended, agree, originalModel, afterModel, combined, models, cost, origins,
    childOrigins, ?_⟩
  intro held node bucket insideHeld present sc member path represented
  exact SourcePruningEnumerationModelPathDomain.stored_suspended_paths
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap)
    (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
    after.core whole extended afterModel origins insideHeld present sc member path represented

end MicroCFTA.SourcePruningEnumerationStoredOwnChildOrigins
