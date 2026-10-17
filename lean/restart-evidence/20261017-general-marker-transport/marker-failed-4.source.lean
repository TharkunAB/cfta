import MicroCFTA.SourceCurrentConstrainedCapPairOccurrenceCallbacks
import MicroCFTA.InternedFreshOrdinaryStoredFreeSupport
import MicroCFTA.InternedRecordDepthExecution

/-!
# General marker transport through actual stored substitution

The proof uses the complete stored plan and its actual returned heap.
Ordinary and Mu records can change during smart reconstruction. Their free
names already have smaller weights. Only root unions need recursive deep
classification. Existing repaired depth readback covers nested warm winners.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMarkerTransport
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution InternedStoredSubstitutionRebind
open InternedStoredSubstitutionScope (slot_lookup)
open InternedFreshOrdinaryContext (Context)
open InternedDeepFreeDepth (deepNames deepMany_member)
open SourceCurrentConstrainedCapPairOccurrences (Classified FreeLE FreeBelow)
open SourceCurrentConstrainedCapPairOccurrenceCallbacks (mark)
open InternedDepthSemantics
open InternedRecordDepthShape (shape)
variable {Symbol Guard : Type}

private def ShapeClassified (weight : Reference → Nat) (bound : Nat) (value : Shape Reference) : Prop :=
  (∀ name ∈ value.free, weight name ≤ bound) ∧ (∀ name ∈ value.deep, weight name < bound ∨ bound = 0)

private def renamed (old marker name : Reference) : Reference := if name = old then marker else name

private theorem replacement_free (old marker original name : Reference) :
    name ∈ ((replacement old (Value.reference (Symbol := Symbol) (Guard := Guard) marker) original).getD (.reference original)).free ↔
      name = renamed old marker original := by
  by_cases same : original = old <;> simp [replacement, renamed, same, Value.free]

private theorem marked_le (weight : Reference → Nat) (bound : Nat) (old marker original : Reference)
    (within : weight original ≤ bound) (fresh : original ≠ marker) :
    mark weight marker bound (renamed old marker original) ≤ bound := by
  by_cases same : original = old <;> simp [renamed, same, mark, fresh, within]

private theorem marked_below (weight : Reference → Nat) (bound : Nat) (old marker original : Reference)
    (oldWeight : weight old = bound) (within : weight original < bound ∨ bound = 0)
    (fresh : original ≠ marker) :
    mark weight marker bound (renamed old marker original) < bound ∨ bound = 0 := by
  rcases within with smaller | zero
  · have different : original ≠ old := by intro same; subst original; omega
    simp only [renamed, ite_eq_right different, mark, ite_eq_right fresh]
    exact .inl smaller
  · exact .inr zero

private theorem context_inputs (context : List (Value Symbol Guard)) (state : State Symbol Guard)
    (available : Values state context) (old marker : Reference) (markerAvailable : Available state (.reference marker)) :
    Values state (context.map (input (replacement old (.reference marker)))) := by
  intro value member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  cases original with
  | empty | node | mu | union => exact available _ present
  | reference name =>
      by_cases same : name = old
      · simpa [input, replacement, same] using markerAvailable
      · simpa [input, replacement, same] using available _ present

private theorem encoded_free_support (context : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (inputs : Values state context)
    (leavesShape : ∀ leaf ∈ context, leaf.free = [] ∨ ∃ name, leaf = .reference name)
    (available : Available state value) (covered : ∀ leaf ∈ leaves value, leaf ∈ context)
    (old marker : Reference) (markerAvailable : Available state (.reference marker))
    (name : Reference)
    (named : name ∈ (evaluate (encode context [] value)
      ((context.map (input (replacement old (.reference marker)))).map shape)).free) :
    ∃ original, original ∈ value.free ∧ name = renamed old marker original := by
  have projected := (InternedRecordDepthSource.evaluate_free (encode context [] value)
    (context.map (input (replacement old (.reference marker)))) state coherent
      (context_inputs context state inputs old marker markerAvailable) name).mp named
  obtain ⟨index, used, selected⟩ := InternedFreeNameIndexedOrigins.evaluate_indexed _ _ _ name projected
  cases found : context[index]? with
  | none => simp [List.getElem?_map, found] at selected
  | some leaf =>
      have leafMember := List.mem_of_getElem? found
      have member : name ∈ (input (replacement old (.reference marker)) leaf).free := by
        simpa only [List.getElem?_map, found, Option.map_some, Option.getD_some] using selected
      rcases leavesShape leaf leafMember with closed | ⟨original, rfl⟩
      · rw [InternedStoredSubstitutionScope.input_closed leaf _ closed, closed] at member
        cases member
      · have origin := InternedStoredPlanFreeSupport.encode_free context [] value state coherent inputs available covered
          index (.reference original) found original (by simp [Value.free])
          (by simpa only [List.length_nil, Nat.zero_add] using used)
        exact ⟨original, origin.1, (replacement_free old marker original name).mp member⟩

private theorem shape_from_free (weight : Reference → Nat) (bound : Nat) (value : Shape Reference)
    (free : ∀ name ∈ value.free, weight name ≤ bound ∧ (weight name < bound ∨ bound = 0)) :
    ShapeClassified weight bound value :=
  ⟨fun name member => (free name member).1,
    fun name member => (free name (List.mem_append_right value.roots member)).2⟩

private theorem source_member (state : State Symbol Guard) (coherent : Coherent state)
    (entry) (members : List (Value Symbol Guard)) (level free)
    (available : Available state (.union entry members level free)) (child : Value Symbol Guard) (member : child ∈ members)
    (name : Reference) (named : name ∈ child.free) : name ∈ (Value.union entry members level free).free := by
  rw [Value.free, InternedNormalizationFree.union_free state coherent entry members level free available.resident,
    childFree_member]
  exact ⟨child, member, named⟩

private theorem combine_classified (weight : Reference → Nat) (bound : Nat) (values : List (Shape Reference))
    (classified : ∀ value ∈ values, ShapeClassified weight bound value) : ShapeClassified weight bound (combineMany values) := by
  induction values with
  | nil => constructor <;> simp [combineMany, Shape.free]
  | cons first rest ih =>
      have one := classified first List.mem_cons_self
      have tail := ih (fun value member => classified value (List.mem_cons_of_mem _ member))
      constructor
      · intro name member
        have member' : name ∈ first.free ∨ name ∈ (combineMany rest).free := by
          simpa [combineMany, combine, Shape.free, List.mem_append, or_assoc, or_left_comm, or_comm] using member
        exact member'.elim (one.1 name) (tail.1 name)
      · intro name member
        rcases (by simpa only [combineMany, combine, List.mem_append] using member :
          name ∈ first.deep ∨ name ∈ (combineMany rest).deep) with left | right
        · exact one.2 name left
        · exact tail.2 name right

mutual
private theorem encoded_classified (context : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (inputs : Values state context)
    (leavesShape : ∀ leaf ∈ context, leaf.free = [] ∨ ∃ name, leaf = .reference name)
    (available : Available state value) (covered : ∀ leaf ∈ leaves value, leaf ∈ context)
    (old marker : Reference) (markerAvailable : Available state (.reference marker))
    (weight : Reference → Nat) (bound : Nat) (oldWeight : weight old = bound)
    (classified : Classified weight bound value) (fresh : marker ∉ value.free) :
    ShapeClassified (mark weight marker bound) bound
      (evaluate (encode context [] value) ((context.map (input (replacement old (.reference marker)))).map shape)) := by
  have allFree := fun name named => encoded_free_support context value state coherent inputs leavesShape
    available covered old marker markerAvailable name named
  have free : ∀ name ∈ (evaluate (encode context [] value)
      ((context.map (input (replacement old (.reference marker)))).map shape)).free,
      mark weight marker bound name ≤ bound := by
    intro name named
    obtain ⟨original, source, rfl⟩ := allFree name named
    exact marked_le weight bound old marker original (classified.free original source) (fun same => fresh (same ▸ source))
  by_cases closed : value.free = []
  · apply shape_from_free
    intro name named
    obtain ⟨original, member, _⟩ := allFree name named
    rw [closed] at member
    cases member
  · cases value with
    | empty => exact False.elim (closed rfl)
    | reference name =>
        refine ⟨free, ?_⟩
        have lookup := slot_lookup context (.reference name) state coherent inputs (covered _ (by simp [leaves, Value.free]))
        simp only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.findIdx?_nil,
          List.length_nil, Nat.zero_add, evaluate, List.getElem?_map, lookup, Option.map_some, Option.getD_some,
          input, replacement]
        split <;> simp [shape]
    | node entry edges level sourceFree | mu entry body depth ordinary =>
        apply shape_from_free
        intro name named
        obtain ⟨original, source, rfl⟩ := allFree name named
        exact ⟨marked_le weight bound old marker original (classified.free original source) (fun same => fresh (same ▸ source)),
          marked_below weight bound old marker original oldWeight (classified.deep original (by simpa only [deepNames] using source))
            (fun same => fresh (same ▸ source))⟩
    | union entry members level sourceFree =>
        have opened : sourceFree.isEmpty = false := by
          cases sourceFree with
          | nil => exact False.elim (closed rfl)
          | cons => rfl
        have coveredMany : ∀ leaf ∈ manyLeaves members, leaf ∈ context := by
          simpa only [leaves, Value.free, opened, Bool.false_eq_true, ↓reduceIte] using covered
        have each : ∀ child ∈ members, Classified weight bound child := by
          intro child member
          exact ⟨fun name named => classified.free name (source_member state coherent entry members level sourceFree available child member name named),
            fun name named => classified.deep name (by
              simpa only [deepNames] using (deepMany_member members name).mpr ⟨child, member, named⟩)⟩
        have result := encodedMany_classified context members state coherent inputs leavesShape
          (fun child member => available.children child member) coveredMany old marker markerAvailable weight bound oldWeight each
          (fun child member named => fresh (source_member state coherent entry members level sourceFree available child member marker named))
        simpa only [encode, Value.free, opened, Bool.false_eq_true, ↓reduceIte, evaluate] using
          combine_classified (mark weight marker bound) bound _ result
termination_by sizeOf value

private theorem encodedMany_classified (context : List (Value Symbol Guard)) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (inputs : Values state context)
    (leavesShape : ∀ leaf ∈ context, leaf.free = [] ∨ ∃ name, leaf = .reference name)
    (available : Values state values) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (old marker : Reference) (markerAvailable : Available state (.reference marker))
    (weight : Reference → Nat) (bound : Nat) (oldWeight : weight old = bound)
    (classified : ∀ value ∈ values, Classified weight bound value) (fresh : ∀ value ∈ values, marker ∉ value.free) :
    ∀ result ∈ evaluateMany (encodeMany context [] values) ((context.map (input (replacement old (.reference marker)))).map shape),
      ShapeClassified (mark weight marker bound) bound result := by
  cases values with
  | nil => simp [encodeMany, evaluateMany]
  | cons first rest =>
      intro result member
      simp only [encodeMany, evaluateMany, List.mem_cons] at member
      rcases member with rfl | member
      · exact encoded_classified context first state coherent inputs leavesShape (available first List.mem_cons_self)
          (fun leaf member => covered leaf (by simp [manyLeaves, member])) old marker markerAvailable weight bound oldWeight
          (classified first List.mem_cons_self) (fresh first List.mem_cons_self)
      · exact encodedMany_classified context rest state coherent inputs leavesShape
          (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun leaf member => covered leaf (by simp [manyLeaves, member])) old marker markerAvailable weight bound oldWeight
          (fun value member => classified value (List.mem_cons_of_mem _ member))
          (fun value member => fresh value (List.mem_cons_of_mem _ member)) result member
termination_by sizeOf values
end

/-- General actual stored substitution transports both free and deep occurrence bounds to its exact return. -/
theorem transport [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state captures) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (available : Available state body) (old marker : Reference) (markerAvailable : Available state (.reference marker))
    (weight : Reference → Nat) (bound : Nat) (oldWeight : weight old = bound)
    (classified : Classified weight bound body) (fresh : marker ∉ body.free)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference marker)) state = .done value after) :
    Classified (mark weight marker bound) bound value := by
  have leafInputs := leaves_available body state available
  have inputAvailable := context_inputs (leaves body) state leafInputs old marker markerAvailable
  have inputs : Context state ((leaves body).map (input (replacement old (.reference marker)))) :=
    ⟨context.normal, inputAvailable, context.profiles, context.freeNames⟩
  have checked := InternedRecordDepthExecution.build_depth (encode (leaves body) [] body) _ state inputs depthHeap
  have observed := checked.result value after actual
  have pure := encoded_classified (leaves body) body state context.normal.facts.coherent leafInputs
    (fun leaf member => InternedStoredLeafShape.leaves_shape body leaf member) available (fun _ member => member)
    old marker markerAvailable weight bound oldWeight classified fresh
  constructor
  · intro name member
    exact pure.1 name ((InternedRecordDepthSource.source_free (encode (leaves body) [] body) _ state inputs
      value after actual name).mp member)
  · intro name member
    exact pure.2 name ((observed.deep name).mp member)

/-- The actual normalized source callback retains the marked classification at its exact return. -/
theorem callback [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state captures) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (available : Available state body) (old marker : Reference) (markerAvailable : Available state (.reference marker))
    (weight : Reference → Nat) (bound : Nat) (oldWeight : weight old = bound)
    (classified : Classified weight bound body) (fresh : marker ∉ body.free)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.callback old body marker state = .done value after) :
    Classified (mark weight marker bound) bound value := by
  have leafInputs := leaves_available body state available
  have inputAvailable := context_inputs (leaves body) state leafInputs old marker markerAvailable
  have inputs : Context state ((leaves body).map (input (replacement old (.reference marker)))) :=
    ⟨context.normal, inputAvailable, context.profiles, context.freeNames⟩
  have verified := InternedFreshOrdinaryFacts.build_verified (encode (leaves body) [] body) _ state
    context.normal.facts inputAvailable
  have normal := InternedFreshOrdinaryNormal.build_normal (encode (leaves body) [] body) _ state context.normal inputAvailable
  unfold SourceRecursiveIntersectionMaybeMu.callback at actual
  cases computed : InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference marker)) state with
  | pending key stopped => simp only [computed, InternedNestedConstruction.Outcome.bind] at actual; cases actual
  | done raw middle =>
      have rawClassified := transport body state context depthHeap available old marker markerAvailable weight bound oldWeight classified fresh
        raw middle computed
      have middleNormal : InternedStoredMuOrigins.Normal middle := by
        simpa only [InternedFreshOrdinaryStoredSubstitution.execute, computed, InternedNestedConstruction.Outcome.state] using normal
      have rawAvailable := verified.result raw middle computed
      simp only [computed, InternedNestedConstruction.Outcome.bind, InternedNestedConstruction.work] at actual
      obtain ⟨rfl, rfl⟩ := InternedNestedConstruction.Outcome.done.inj actual
      exact SourceCurrentConstrainedCapPairOccurrences.filter (mark weight marker bound) bound marker raw middle middleNormal rawAvailable rawClassified

end MicroCFTA.SourceCurrentConstrainedCapMarkerTransport
