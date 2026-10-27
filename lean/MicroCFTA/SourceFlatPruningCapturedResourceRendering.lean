import MicroCFTA.SourceFlatPruningCapturedResourceMeaning
import MicroCFTA.SourceFlatPruningRenderingAssignment

/-!
# Native acceptance from actual flat captured rendering

Original resources give one bound for each actual flat captured receipt.
Discharge and actual flat rendering construct an assignment at its own heap.
The completed step restores acceptance at the original captured node.
-/
namespace MicroCFTA.SourceFlatPruningCapturedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "FlatCore" => EnumerationFlatState.State Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual flat rendering restores original captured acceptance without an assumed assignment or old render. -/
theorem render_sound_current_resources
    (seed : SourcePruningEnumerationIncomingReservation.Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits seed.2 caller.checked)
    (reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (canonical : Canonical before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : arityAllows edge.children.length (suspendedVars before.core.counter tries) = true)
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) :
    ∃ bound : Nat, ∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
      ∀ (extra : Nat) (fragment : Fragment) (reached : Caller (bits + 2))
        (saved : SourceEndpointMemo.Memos) (after : FlatCached),
      run checkEmpty (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller flat memos.query = some (.complete fragment reached saved after) →
      ∀ (level : Nat → Nat) (frontier : Nat), EnumerationOrder.Stratified before.core level frontier →
      SourceFlatPruningRendering.Discharged after.core →
      ∀ (ambient : InternedGuardedLanguage.Env Symbol) (marker : Symbol) (renderFuel : Nat)
        (term : Language.Term Symbol) (pendingResiduals : List (Constraint × Language.Term Symbol))
        (renderedAfter : FlatCore),
      Except.ok ((term, pendingResiduals), renderedAfter) ∈
        ExceptT.run (SourceFlatPruningRendering.render reached.checked.native.machine.heap
          marker renderFuel uv after.core) →
      (∀ obligation ∈ pendingResiduals,
        SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true) →
      ∃ assignment : Nat → Language.Term Symbol,
        EnumerationFlatState.Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
          assignment flat.core ∧
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient (.node parentEntry edges depth free) term ∧
        (∀ sc ∈ scs, Suspended.Holds assignment term sc) ∧
        Fragments.fill assignment fragment = term ∧ renderedAfter = after.core ∧
        EnumerationFlatState.Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient reached.checked.native.machine.heap)
          (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
          assignment after.core ∧
        EnumerationFlatState.Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient reached.checked.native.machine.heap)
          (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
          assignment renderedAfter := by
  obtain ⟨bound, completed⟩ := complete_sound_current_resources seed formulas solver inventory caller before checkEmpty
    uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized selected
    paths counts flags pending allowed tries residual projected fits reserved known canonical nonterminal freshArity retained
  refine ⟨bound, ?_⟩
  intro flat related extra fragment reached saved after observed level frontier ordered discharged
    ambient marker renderFuel term pendingResiduals renderedAfter rendered checked
  obtain ⟨earlier, caches, safe, order, sound⟩ := completed flat related extra fragment reached saved after observed
  obtain ⟨nextLevel, afterOrder⟩ := order level frontier ordered
  obtain ⟨assignment, satisfies, termSame, unchanged, renderedSatisfies⟩ :=
    SourceFlatPruningRendering.render_assignment reached.checked.native.machine.heap
      (SourceEqualityPCSGuard.holds formulas solver) ambient
      (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
      marker renderFuel uv after.core renderedAfter earlier.core term pendingResiduals
      caches.core safe nextLevel (frontier + 1) afterOrder discharged rendered checked
  obtain ⟨original, edgeAccepted, parentAccepted, suspended, filled⟩ := sound ambient assignment satisfies
  refine ⟨assignment, original, ?_, ?_, ?_, filled.trans termSame.symm, unchanged,
    satisfies, renderedSatisfies⟩
  · simpa only [← termSame] using edgeAccepted
  · simpa only [← termSame] using parentAccepted
  · simpa only [← termSame] using suspended

end MicroCFTA.SourceFlatPruningCapturedEdge
