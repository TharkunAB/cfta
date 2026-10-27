import MicroCFTA.SourcePruningEnumerationCapturedEdgeDiagonalSoundness
import MicroCFTA.SourcePruningEnumerationCapturedEdgeCanonical
import MicroCFTA.SourcePruningEnumerationRecursivePacket

/-!
# Captured completion at the actual recursive packet

The current packet supplies the native context and cache indexes.
Completed observations determine their own arity and projected payload.
The semantic observer retains numeric admission and truncation gates.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies EnumerationValidity
open InternedConstructorTemplates SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual completed recursive head retains valid stored tries from its original packet. -/
theorem completed_head_canonical
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (metadata : Metadata Typing) (memos : Memos) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (selected : edge ∈ edges)
    (canonical : Canonical before.core)
    {r n p h k : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k uv scs edge
      caller before memos.query = some (.complete fragment afterCaller savedQueries after)) :
    Canonical after.core := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  have pending := EnumerationReferences.pending_inputs before.core packet.pending uv (some handle) scs stored
  have actual := observed
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        rw [SourcePruningEnumerationCapturedEdge.run,
          SourcePruningEnumerationSelectedEdge.unsupported checkEmpty r n p h k scs edge
            caller before memos.query allowed projected] at actual
        cases actual
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        exact SourcePruningEnumerationCapturedEdge.complete_canonical formulas solver inventory caller
          before checkEmpty uv handle scs parentEntry edges depth free edge roots memos packet.context ready
          stored decoded realized selected paths counts flags pending allowed tries residual projected canonical observed
  · have rejected : arityAllows edge.children.length scs = false := by
      cases value : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed value).elim
    rw [SourcePruningEnumerationCapturedEdge.run,
      SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty r n p h k scs edge
        caller before memos.query rejected] at actual
    cases actual

/-- Actual diagonal head completion restores the original packet language under the explicit semantic gates. -/
theorem completed_head_sound_current
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (metadata : Metadata Typing) (memos : Memos) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (selected : edge ∈ edges)
    (canonical : Canonical before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      arityAllows edge.children.length (suspendedVars before.core.counter tries) = true)
    (retained : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ incoming bucket,
        (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
        (match incoming with | .node _ _ _ _ => True | _ => False) ∨
          bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [])
    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query)
    {bound : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ extra,
      SourcePruningEnumerationCapturedEdge.run checkEmpty
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller before memos.query = some (.complete fragment afterCaller savedQueries after)) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment after.core →
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (assignment uv) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry edges depth free) (assignment uv) ∧
      (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
      Fragments.fill assignment fragment = assignment uv := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  have pending := EnumerationReferences.pending_inputs before.core packet.pending uv (some handle) scs stored
  have actual := observed 0
  simp only [Nat.add_zero] at actual
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        rw [SourcePruningEnumerationCapturedEdge.run,
          SourcePruningEnumerationSelectedEdge.unsupported checkEmpty bound bound bound bound bound scs edge
            caller before memos.query allowed projected] at actual
        cases actual
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        exact SourcePruningEnumerationCapturedEdge.diagonal_complete_sound_current formulas solver
          inventory caller before checkEmpty uv handle scs parentEntry edges depth free edge roots memos
          packet.context ready stored decoded realized selected paths counts flags pending allowed tries residual
          projected ranges canonical nonterminal (freshArity tries residual projected)
          (retained tries residual projected) observed
  · have rejected : arityAllows edge.children.length scs = false := by
      cases value : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed value).elim
    rw [SourcePruningEnumerationCapturedEdge.run,
      SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty bound bound bound bound bound scs edge
        caller before memos.query rejected] at actual
    cases actual

end MicroCFTA.SourcePruningEnumerationRecursive
