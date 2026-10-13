import MicroCFTA.SourceSizedFiniteKeysExecution

/-!
# Structural trim under exact finite-key readback

The proofs transport each Boolean iteration. They do not require every
state of the raw state type to occur in the finite key list. Exact ordered
row readback supplies closure of all child references in the finite image.
-/
namespace MicroCFTA.SourceSizedFiniteKeysTrimTransport
open Language Productivity

/-- Injective state encoding preserves membership in each ordered state list. -/
theorem mem_map [DecidableEq Source] [DecidableEq Target]
    (encode : Source → Target) (injective : Function.Injective encode) (states : List Source) (state : Source) :
    encode state ∈ states.map encode ↔ state ∈ states := by
  simp only [List.mem_map, injective.eq_iff]
  exact ⟨fun ⟨_, member, equal⟩ => equal ▸ member, fun member => ⟨state, member, rfl⟩⟩

/-- One actual productivity round reads the same ordered child flags. -/
theorem productiveStep_readback (encode : Source → Target)
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (rows : ∀ state, target (encode state) = (source state).map (SymbolicGraphView.renameEdge encode))
    (sourceKnown : Source → Bool) (targetKnown : Target → Bool)
    (known : ∀ state, targetKnown (encode state) = sourceKnown state) (state : Source) :
    productiveStep target targetKnown (encode state) = productiveStep source sourceKnown state := by
  simp only [productiveStep, rows, List.any_map, SymbolicGraphView.renameEdge,
    List.all_map, Function.comp_def, known]

/-- Every finite productivity round agrees on the restricted keys. -/
theorem productive_round (encode : Source → Target)
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (rows : ∀ state, target (encode state) = (source state).map (SymbolicGraphView.renameEdge encode))
    (fuel : Nat) (state : Source) :
    iterate (productiveStep target) (fun _ => false) fuel (encode state) =
      iterate (productiveStep source) (fun _ => false) fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => exact productiveStep_readback encode source target rows _ _ ih state

/-- Equal finite inventory lengths give the same computed productivity result. -/
theorem productive_readback (encode : Source → Target)
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (rows : ∀ state, target (encode state) = (source state).map (SymbolicGraphView.renameEdge encode))
    (states : List Source) (state : Source) :
    productive (states.map encode) target (encode state) = productive states source state := by
  simpa only [productive, List.length_map] using productive_round encode source target rows states.length state

/-- Live-row filtering preserves exact row order and every retained guard. -/
theorem live_readback (encode : Source → Target)
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (rows : ∀ state, target (encode state) = (source state).map (SymbolicGraphView.renameEdge encode))
    (states : List Source) (state : Source) :
    GraphTrim.live (states.map encode) target (encode state) =
      (GraphTrim.live states source state).map (SymbolicGraphView.renameEdge encode) := by
  unfold GraphTrim.live
  rw [productive_readback encode source target rows states state]
  split
  · rw [rows, List.filter_map]
    simp only [Function.comp_def, SymbolicGraphView.renameEdge, List.all_map,
      productive_readback encode source target rows states]
  · rfl

/-- Live successor lists retain exact multiplicity and order. -/
theorem successors_readback (encode : Source → Target)
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (rows : ∀ state, target (encode state) = (source state).map (SymbolicGraphView.renameEdge encode))
    (states : List Source) (state : Source) :
    successors (GraphTrim.live (states.map encode) target) (encode state) =
      (successors (GraphTrim.live states source) state).map encode := by
  simp only [successors, live_readback encode source target rows states state,
    List.flatMap_map, SymbolicGraphView.renameEdge, List.map_flatMap]

/-- One reachability round preserves the actual source list scan and membership checks. -/
theorem reachStep_readback [DecidableEq Source] [DecidableEq Target]
    (encode : Source → Target) (injective : Function.Injective encode) (states : List Source)
    (source : Source → List Source) (target : Target → List Target)
    (next : ∀ state, target (encode state) = (source state).map encode)
    (sourceKnown : Source → Bool) (targetKnown : Target → Bool)
    (known : ∀ state, targetKnown (encode state) = sourceKnown state) (state : Source) :
    reachStep (states.map encode) target targetKnown (encode state) = reachStep states source sourceKnown state := by
  simp only [reachStep, known, List.any_map, Function.comp_def, next, mem_map encode injective]

/-- Every reached-state iteration transports through injective key readback. -/
theorem reach_round [DecidableEq Source] [DecidableEq Target]
    (encode : Source → Target) (injective : Function.Injective encode) (states seeds : List Source)
    (source : Source → List Source) (target : Target → List Target)
    (next : ∀ state, target (encode state) = (source state).map encode) (fuel : Nat) (state : Source) :
    iterate (reachStep (states.map encode) target) (fun target => decide (target ∈ seeds.map encode)) fuel (encode state) =
      iterate (reachStep states source) (fun source => decide (source ∈ seeds)) fuel state := by
  induction fuel generalizing state with
  | zero => simp only [iterate, mem_map encode injective]
  | succ fuel ih => exact reachStep_readback encode injective states source target next _ _ ih state

/-- The complete computed reach closure agrees without a whole-state-type completeness premise. -/
theorem reachClosure_readback [DecidableEq Source] [DecidableEq Target]
    (encode : Source → Target) (injective : Function.Injective encode) (states seeds : List Source)
    (source : Source → List Source) (target : Target → List Target)
    (next : ∀ state, target (encode state) = (source state).map encode) (state : Source) :
    reachClosure (states.map encode) target (seeds.map encode) (encode state) =
      reachClosure states source seeds state := by
  simpa only [reachClosure, List.length_map] using reach_round encode injective states seeds source target next states.length state

/-- Every final guarded trim row is the exact readback of its finite-carrier row. -/
theorem trim_readback [DecidableEq Source] [DecidableEq Target]
    (encode : Source → Target) (injective : Function.Injective encode)
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (rows : ∀ state, target (encode state) = (source state).map (SymbolicGraphView.renameEdge encode))
    (states : List Source) (root state : Source) :
    GraphTrim.trim (states.map encode) target (encode root) (encode state) =
      (GraphTrim.trim states source root state).map (SymbolicGraphView.renameEdge encode) := by
  have reached := reachClosure_readback encode injective states [root]
    (successors (GraphTrim.live states source)) (successors (GraphTrim.live (states.map encode) target))
    (successors_readback encode source target rows states) state
  simp only [List.map_cons, List.map_nil] at reached
  unfold GraphTrim.trim
  rw [reached]
  split
  · exact live_readback encode source target rows states state
  · rfl

/-- The actual root-preserving trim inventory commutes as an ordered list. -/
theorem trimKeys_readback [DecidableEq Source] [DecidableEq Target]
    (encode : Source → Target) (injective : Function.Injective encode)
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (rows : ∀ state, target (encode state) = (source state).map (SymbolicGraphView.renameEdge encode))
    (states : List Source) (root : Source) :
    SourceSizedDecidedTrim.trimKeys (states.map encode) target (encode root) =
      (SourceSizedDecidedTrim.trimKeys states source root).map encode := by
  have reached := fun state => reachClosure_readback encode injective states [root]
    (successors (GraphTrim.live states source)) (successors (GraphTrim.live (states.map encode) target))
    (successors_readback encode source target rows states) state
  simp only [List.map_cons, List.map_nil] at reached
  simp only [SourceSizedDecidedTrim.trimKeys, List.filter_map, Function.comp_def, injective.eq_iff,
    productive_readback encode source target rows states, reached]

end MicroCFTA.SourceSizedFiniteKeysTrimTransport
