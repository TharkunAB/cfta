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

private theorem actual : build source [] empty = .done root common := by
  obtain ⟨result,after,called⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete source
  change build source [] empty = .done (value (build source [] empty)) (build source [] empty).state
  rw [called]
  rfl
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
private theorem first_raw : build expression [.reference firstName] common = .done firstRaw common := by rfl
private theorem second_raw : build expression [.reference secondName] common = .done secondRaw common := by rfl
private theorem first_done : execute firstRaw first common = .done firstResult common := by rfl
private theorem second_done : execute secondRaw second common = .done secondResult common := by rfl
private theorem first_shape : firstResult = .mu (fields firstResult).1 (fields firstResult).2.1
    (fields firstResult).2.2.1 (fields firstResult).2.2.2 := by rfl
private theorem second_shape : secondResult = .mu (fields secondResult).1 (fields secondResult).2.1
    (fields secondResult).2.2.1 (fields secondResult).2.2.2 := by rfl
private theorem first_unfold : unfold firstResult reader = .done (.reference marker) reader := by rfl
private theorem second_unfold : unfold secondResult reader = .done (item 7) reader := by rfl

private theorem own_available (input : Value Nat Bool) (available : Available common input) :
    Available common (.reference (own input)) := by
  have coherent := initial_ready.semantic.1.normal.facts.coherent
  apply reference_available
  cases input with
  | empty | reference | node | union =>
      intro identity impossible
      simp only [own,Value.free,List.mem_singleton,reduceCtorEq] at impossible
  | mu entry body depth ordinary =>
      have stored := InternedFreshProbeKeys.resident_entry common coherent _ available.resident entry rfl
      intro identity member
      have same : identity = entry.identity := by simpa only [own,Value.free,List.mem_singleton,Reference.interned.injEq] using member
      subst identity
      exact ⟨entry.key,(coherent.valid.2.2 entry.key entry stored).2⟩

private theorem first_inputs : InternedNestedProvenance.Values common [.reference firstName] := by
  intro input member
  have same := List.mem_singleton.mp member
  subst input
  exact own_available (item 2) (item_available 2 (by omega))
private theorem second_inputs : InternedNestedProvenance.Values common [.reference secondName] := by
  intro input member
  have same := List.mem_singleton.mp member
  subst input
  exact own_available (item 3) (item_available 3 (by omega))
private theorem first_replacements : Replacements common first := by
  intro name output found
  unfold first at found
  split at found
  · cases found; exact item_available 0 (by omega)
  · cases found
private theorem second_replacements : Replacements common second := by
  intro name output found
  unfold second at found
  split at found
  · cases found; exact item_available 1 (by omega)
  · cases found

private theorem ordinary_reference (input : Value Nat Bool) (plain : Ordinary input) (name : Reference) :
    ¬ ReferenceOrigin reader [input] name := by
  have separate : ∀ reference, input ≠ .reference reference := by
    cases input <;> try cases plain <;> intro reference impossible <;> cases impossible
  have noNext : MergedFreshOrdinaryGraph.successors reader input = [] := by
    cases input <;> try cases plain <;> rfl
  intro present
  have later := (SourceCurrentOpenObservations.reference_expand reader input separate name).mp present
  rw [noNext] at later
  obtain ⟨_,member,_⟩ := (SourceCurrentOpenObservations.reference_seeds reader [] name).mp later
  cases member

private theorem paired_inputs : Paired (RelatedAt 0 reader) first second [.reference firstName] [.reference secondName] := by
  refine .cons ?_ .nil
  change RelatedAt 0 reader ((first firstName).getD (.reference firstName)) ((second secondName).getD (.reference secondName))
  simp only [first,second,if_pos rfl,Option.getD_some]
  constructor
  · have zero : (item 0).referenceOf ≠ .empty := by intro impossible; cases impossible
    have one : (item 1).referenceOf ≠ .empty := by intro impossible; cases impossible
    exact iff_of_false zero one
  · intro name
    exact iff_of_false (ordinary_reference (item 0) (by trivial) name) (ordinary_reference (item 1) (by trivial) name)

private theorem valid_reader : Valid reader := initial_ready.semantic.1.normal.facts.coherent.valid
private theorem incoherent_reader : ¬ Coherent reader := by
  intro coherent
  have present : reader.nodeRecords (key (item 6)) = some (.reference marker) := by
    change (if key (item 6) = key (item 6) then some (.reference marker) else _) = _
    rw [if_pos rfl]
  obtain ⟨entry,_,impossible⟩ := coherent.nodes _ _ present
  exact impossible

private theorem not_related : ¬ RelatedAt 0 reader firstResult secondResult := by
  intro related
  have left := first_unfold
  have right := second_unfold
  rw [first_shape] at left
  rw [second_shape] at right
  have firstExposure := SourceCurrentOpenObservations.unfold 0 reader _ _ _ _ _ reader left
  have secondExposure := SourceCurrentOpenObservations.unfold 0 reader _ _ _ _ _ reader right
  have present : ReferenceOrigin reader [firstResult] marker := by
    rw [first_shape]
    exact (firstExposure marker).mpr ((SourceCurrentOpenObservations.reference_exact reader marker marker).mpr rfl)
  have other := (related.2 marker).mp present
  rw [second_shape] at other
  exact ordinary_reference (item 7) (by trivial) marker ((secondExposure marker).mp other)

/-- An active open source binder can fail finite alignment at a valid but incoherent separate reader. -/
theorem arbitrary_reader :
    ∃ (execution view : State Nat Bool) (term : Syntax Nat Bool)
      (firstMap secondMap : Environment Nat Bool) (firstInputs secondInputs : List (Value Nat Bool))
      (rawFirst rawSecond left right : Value Nat Bool),
      Ready execution ∧ Valid view ∧ ¬ Coherent view ∧
      InternedNestedConstruction.Scoped 1 term ∧ ¬ InternedNestedConstruction.Scoped 0 term ∧
      Paired (RelatedAt 0 view) firstMap secondMap firstInputs secondInputs ∧
      InternedNestedProvenance.Values execution firstInputs ∧ InternedNestedProvenance.Values execution secondInputs ∧
      Replacements execution firstMap ∧ Replacements execution secondMap ∧
      build term firstInputs execution = .done rawFirst execution ∧
      build term secondInputs execution = .done rawSecond execution ∧
      execute rawFirst firstMap execution = .done left execution ∧
      execute rawSecond secondMap execution = .done right execution ∧
      ¬ RelatedAt 0 view left right ∧ ¬ AlignedAt 0 view execution term := by
  refine ⟨common,reader,expression,first,second,[.reference firstName],[.reference secondName],
    firstRaw,secondRaw,firstResult,secondResult,initial_ready,valid_reader,incoherent_reader,?_,?_,
    paired_inputs,first_inputs,second_inputs,first_replacements,second_replacements,
    first_raw,second_raw,first_done,second_done,not_related,?_⟩
  · simp [expression,InternedNestedConstruction.Scoped,InternedNestedConstruction.EdgesScoped,
      InternedNestedConstruction.ManyScoped]
  · simp [expression,InternedNestedConstruction.Scoped,InternedNestedConstruction.EdgesScoped,
      InternedNestedConstruction.ManyScoped]
  · intro aligned
    exact not_related (aligned _ _ first second paired_inputs initial_ready first_inputs second_inputs
      first_replacements second_replacements firstRaw secondRaw first_raw second_raw
      firstResult secondResult first_done second_done)

end MicroCFTA.SourceCurrentOpenBinderObservationBoundary
