import MicroCFTA.SourceCurrentFiniteObservationExecution

/-!
# An arbitrary reader does not support active binder induction

The execution heap comes from an actual closed source construction.
The tested binder uses both its local variable and an outer capture.
Both replacement leaves have the same depth-zero observations. The
separate reader retains valid identity caches but has one incoherent
node payload. One actual unfolding then exposes a bare reference.
This is a proof-interface boundary. It is not an execution defect.
-/
namespace MicroCFTA.SourceCurrentOpenBinderObservationBoundary
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Ordinary)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt)
open SourceCurrentReaderReplacementSlots (Paired)
open SourceCurrentFiniteObservationExecution (AlignedAt)
open SourceCurrentOpenObservations (ReferenceOrigin Same)

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def leaf (symbol : Nat) : Syntax Nat Bool := .node [.mk symbol false []]
private def expression : Syntax Nat Bool := .binder true (.node [.mk 2 false [.var 0,.var 1]])
private def outer (marker : Nat) : Syntax Nat Bool := .binder true (.union [expression,leaf marker])
private def closedMu (marker : Nat) : Syntax Nat Bool := .binder true (.node [.mk 2 false [.var 0,leaf marker]])
private def layer (marker : Nat) : Syntax Nat Bool := .node [.mk 2 false [closedMu marker,leaf marker]]
private def source : Syntax Nat Bool := .node [.mk 9 false
  [leaf 0,leaf 1,outer 10,outer 11,closedMu 0,closedMu 1,layer 0,layer 1]]
private def built := build source [] empty
private def root := value built
private def common := built.state
private def item (index : Nat) := (children root)[index]?.getD .empty
private def own : Value Nat Bool → Reference
  | .mu entry .. => .interned entry.identity
  | _ => .depth
private def firstName := own (item 2)
private def secondName := own (item 3)
private def first : Environment Nat Bool := fun name => if name = firstName then some (item 0) else none
private def second : Environment Nat Bool := fun name => if name = secondName then some (item 1) else none
private def firstRaw := value (build expression [.reference firstName] common)
private def secondRaw := value (build expression [.reference secondName] common)
private def firstResult := item 4
private def secondResult := item 5
private def key : Value Nat Bool → NodeKey
  | .node entry .. => entry.key
  | _ => .node []
private def marker : Reference := .uninterned 99
private def reader : State Nat Bool := {common with nodeRecords := fun requested =>
  if requested = key (item 6) then some (.reference marker) else common.nodeRecords requested}
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)

private theorem actual : build source [] empty = .done root common := by cbv
private theorem initial_ready : Ready common := SourceEqualityRequiredCache.constructed source root common actual
private theorem root_available : Available common root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro input member; cases member)).result root common actual
private theorem item_available (index : Nat) (bounded : index < 8) : Available common (item index) := by
  apply root_available.children (item index)
  apply List.mem_of_getElem?
  change (children root)[index]? = some (item index)
  unfold item
  exact List.getElem?_eq_getElem (by simpa only [show (children root).length = 8 by cbv] using bounded) |>.trans
    (by rw [List.getElem?_eq_getElem (by simpa only [show (children root).length = 8 by cbv] using bounded)]; rfl)
private theorem first_raw : build expression [.reference firstName] common = .done firstRaw common := by cbv
private theorem second_raw : build expression [.reference secondName] common = .done secondRaw common := by cbv
private theorem first_done : execute firstRaw first common = .done firstResult common := by cbv
private theorem second_done : execute secondRaw second common = .done secondResult common := by cbv
private theorem first_shape : firstResult = .mu (fields firstResult).1 (fields firstResult).2.1
    (fields firstResult).2.2.1 (fields firstResult).2.2.2 := by cbv
private theorem second_shape : secondResult = .mu (fields secondResult).1 (fields secondResult).2.1
    (fields secondResult).2.2.1 (fields secondResult).2.2.2 := by cbv
private theorem first_unfold : unfold firstResult reader = .done (.reference marker) reader := by cbv
private theorem second_unfold : unfold secondResult reader = .done (item 7) reader := by cbv

end MicroCFTA.SourceCurrentOpenBinderObservationBoundary
