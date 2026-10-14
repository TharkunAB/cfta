import MicroCFTA.InternedStoredCostInputs

/-!
# Positive occurrence retention in prepared stored plans

Each original free occurrence retains every supplied replacement occurrence.
Its cost increases by at most the original number of Mu frames. Live
siblings remain nonempty. The induction includes arbitrary open nested Mu
records and root unions with Mu members.
-/
namespace MicroCFTA.InternedStoredCostRetention
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution InternedStoredCostInputs
open InternedFreeOccurrenceRank
open InternedDepthSemantics (Shape)
open InternedBinderProtocol (Reference)

/-- Each supplied occurrence survives with at most its original enclosing Mu cost. -/
def Retains (original : List (Reference × Nat)) (actual : List (Atom × Nat))
    (meanings : Meanings Atom) : Prop :=
  ∀ name count, (name, count) ∈ original → ∀ atom base, (atom, base) ∈ meanings name →
    ∃ after, after ≤ count + base ∧ (atom, after) ∈ actual

/-- Prepared ordered child shapes are the shapes of the same original children. -/
theorem evaluateMany_encode (context : List (Value Symbol Guard)) (locals : List Reference)
    (values : List (Value Symbol Guard)) (shapes : List (Shape Atom)) :
    InternedDepthSemantics.evaluateMany (encodeMany context locals values) shapes =
      values.map (fun value => InternedDepthSemantics.evaluate (encode context locals value) shapes) := by
  induction values with
  | nil => simp [encodeMany, InternedDepthSemantics.evaluateMany]
  | cons first rest ih => simp only [encodeMany, InternedDepthSemantics.evaluateMany, List.map_cons, ih]

/-- A positive retained occurrence makes an original open record's prepared shape nonempty. -/
theorem open_nonempty (context : List (Value Symbol Guard)) (locals : List Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal state) (available : Available state value)
    (shapes : List (Shape Atom)) (occurrences : List (List (Atom × Nat))) (meanings : Meanings Atom)
    (inputs : Inputs context locals shapes occurrences meanings) (opened : value.free ≠ [])
    (retained : Retains (costs value)
      (InternedOccurrenceCostSemantics.evaluate (encode context locals value) shapes occurrences) meanings) :
    (InternedDepthSemantics.evaluate (encode context locals value) shapes).isEmpty = false := by
  cases freeFound : value.free with
  | nil => exact False.elim (opened freeFound)
  | cons name rest =>
      obtain ⟨count, present⟩ := (costs_free value state normal.facts.coherent available name).mpr (by simp [freeFound])
      cases meaningFound : meanings name with
      | nil => exact False.elim (inputs.positive name meaningFound)
      | cons first rest =>
          obtain ⟨after, _, member⟩ := retained name count present first.1 first.2 (by simp [meaningFound])
          exact InternedOccurrenceCostSupport.evaluate_nonempty _ _ _ inputs.coherent inputs.support first.1 after member

mutual
/-- Prepared reconstruction retains original occurrence bounds and every original nonempty result. -/
theorem encode_retains (context : List (Value Symbol Guard)) (locals : List Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal state) (available : Available state value)
    (covered : ∀ leaf ∈ leaves value, leaf ∈ context)
    (shapes : List (Shape Atom)) (occurrences : List (List (Atom × Nat))) (meanings : Meanings Atom)
    (inputs : Inputs context locals shapes occurrences meanings) :
    Retains (costs value) (InternedOccurrenceCostSemantics.evaluate (encode context locals value) shapes occurrences) meanings ∧
      (value.referenceOf ≠ .empty → (InternedDepthSemantics.evaluate (encode context locals value) shapes).isEmpty = false) := by
  by_cases closed : value.free = []
  · have isClosed : value.free.isEmpty = true := by simp [closed]
    have member : value ∈ context := covered value (by rw [leaves.eq_def]; simp [isClosed])
    constructor
    · intro name count present atom base supplied
      have named := (costs_free value state normal.facts.coherent available name).mp ⟨count, present⟩
      simp [closed] at named
    · intro live
      rw [encode.eq_def]
      simp only [isClosed, ↓reduceIte, InternedDepthSemantics.evaluate]
      rw [inputs.closed value member closed]
      exact beq_eq_false_iff_ne.mpr live
  · have isOpen : value.free.isEmpty = false := List.isEmpty_eq_false_iff.mpr closed
    have innerCovered := covered
    rw [leaves.eq_def] at innerCovered
    simp only [isOpen, Bool.false_eq_true, ↓reduceIte] at innerCovered
    have retained : Retains (costs value)
        (InternedOccurrenceCostSemantics.evaluate (encode context locals value) shapes occurrences) meanings := by
      rw [encode.eq_def]
      simp only [isOpen, Bool.false_eq_true, ↓reduceIte]
      cases value with
      | empty => simp [Value.free] at closed
      | reference name =>
          have read := inputs.reference name (innerCovered _ (by simp))
          simp only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at read
          rw [read]
          intro original count present atom base supplied
          have equal : original = name ∧ count = 0 := by simpa [costs] using present
          rcases equal with ⟨rfl, rfl⟩
          exact ⟨base, by omega, supplied⟩
      | node entry edges depth free =>
          have live := InternedLiveEdges.resident_live state normal.live _ available.resident
          simpa only [costs, InternedOccurrenceCostSemantics.evaluate] using
            encodeEdges_retains context locals edges state normal
              (fun child member => available.children child member) innerCovered live shapes occurrences meanings inputs
      | union entry members depth free =>
          simpa only [costs, InternedOccurrenceCostSemantics.evaluate] using
            (encodeMany_retains context locals members state normal
              (fun child member => available.children child member) innerCovered shapes occurrences meanings inputs).1
      | mu entry body depth ordinary =>
          intro name count present atom base supplied
          obtain ⟨prior, ⟨original, different⟩, equal⟩ :=
            (InternedFreshOrdinaryCostHeap.mu_cost_iff entry body depth ordinary name count).mp present
          have renamed : (Sum.inr atom, base) ∈ bindMeanings (.interned entry.identity) meanings name := by
            simp only [bindMeanings, different, ↓reduceIte]
            exact List.mem_map.mpr ⟨(atom, base), supplied, rfl⟩
          obtain ⟨after, bound, member⟩ :=
            (encode_retains context (.interned entry.identity :: locals) body state normal
              (available.children body (by simp [children])) innerCovered _ _ _
              (local_inputs context locals shapes occurrences meanings inputs (.interned entry.identity))).1
              name prior original (.inr atom) base renamed
          let shift := InternedOccurrenceCostSemantics.binderShift true
            (InternedDepthSemantics.evaluate (encode context (.interned entry.identity :: locals) body)
              (⟨[Sum.inl ()], [], false, 0⟩ :: shapes.map (Shape.map Sum.inr)))
          have shiftBound : shift ≤ 1 := by
            dsimp only [shift, InternedOccurrenceCostSemantics.binderShift]
            split <;> omega
          refine ⟨after + shift, by omega, ?_⟩
          rw [InternedOccurrenceCostSemantics.evaluate, InternedOccurrenceCostSemantics.lower_member]
          exact ⟨after, member, rfl⟩
    exact ⟨retained, fun _ => open_nonempty context locals value state normal available shapes occurrences meanings inputs closed retained⟩
termination_by sizeOf value

/-- Ordered original children retain their costs and their individual nonempty shapes. -/
theorem encodeMany_retains (context : List (Value Symbol Guard)) (locals : List Reference)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal state) (available : ∀ value ∈ values, Available state value)
    (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (shapes : List (Shape Atom)) (occurrences : List (List (Atom × Nat))) (meanings : Meanings Atom)
    (inputs : Inputs context locals shapes occurrences meanings) :
    Retains (manyCosts values) (InternedOccurrenceCostSemantics.evaluateMany (encodeMany context locals values) shapes occurrences) meanings ∧
      ∀ value ∈ values, value.referenceOf ≠ .empty →
        (InternedDepthSemantics.evaluate (encode context locals value) shapes).isEmpty = false := by
  cases values with
  | nil => constructor <;> simp [Retains, manyCosts]
  | cons first rest =>
      have head := encode_retains context locals first state normal (available first List.mem_cons_self)
        (fun leaf member => covered leaf (by simp [manyLeaves, member])) shapes occurrences meanings inputs
      have tail := encodeMany_retains context locals rest state normal
        (fun value member => available value (List.mem_cons_of_mem first member))
        (fun leaf member => covered leaf (by simp [manyLeaves, member])) shapes occurrences meanings inputs
      constructor
      · intro name count present atom base supplied
        rw [encodeMany, InternedOccurrenceCostSemantics.evaluateMany]
        rw [manyCosts] at present
        rcases List.mem_append.mp present with left | right
        · obtain ⟨after, bound, member⟩ := head.1 name count left atom base supplied
          exact ⟨after, bound, List.mem_append_left _ member⟩
        · obtain ⟨after, bound, member⟩ := tail.1 name count right atom base supplied
          exact ⟨after, bound, List.mem_append_right _ member⟩
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact head.2
        · exact tail.2 value member
termination_by sizeOf values

/-- Every original live edge survives, so each original child occurrence retains its bound. -/
theorem encodeEdges_retains (context : List (Value Symbol Guard)) (locals : List Reference)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal state)
    (available : ∀ child ∈ edges.flatMap EdgeValue.children, Available state child)
    (covered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ context)
    (live : ∀ edge ∈ edges, edge.children.any (fun child => child.referenceOf == .empty) = false)
    (shapes : List (Shape Atom)) (occurrences : List (List (Atom × Nat))) (meanings : Meanings Atom)
    (inputs : Inputs context locals shapes occurrences meanings) :
    Retains (edgeCosts edges) (InternedOccurrenceCostSemantics.evaluateEdges (encodeEdges context locals edges) shapes occurrences) meanings := by
  cases edges with
  | nil => simp [Retains, edgeCosts]
  | cons first rest =>
      cases first with
      | mk entry children =>
          have head := encodeMany_retains context locals children state normal
            (fun child member => available child (by simp [EdgeValue.children, member]))
            (fun leaf member => covered leaf (by simp [edgeLeaves, member])) shapes occurrences meanings inputs
          have survives : (InternedDepthSemantics.evaluateMany (encodeMany context locals children) shapes).any Shape.isEmpty = false := by
            rw [evaluateMany_encode]
            apply List.any_eq_false.mpr
            intro shape member
            obtain ⟨child, selected, rfl⟩ := List.mem_map.mp member
            have original := List.any_eq_false.mp (live (.mk entry children) List.mem_cons_self) child selected
            have nonempty := head.2 child selected (fun equal => original (by simp [equal]))
            simp only [nonempty, Bool.false_eq_true, not_false_eq_true]
          have tail := encodeEdges_retains context locals rest state normal
            (fun child member => available child (by simp [member]))
            (fun leaf member => covered leaf (by simp [edgeLeaves, member]))
            (fun edge member => live edge (List.mem_cons_of_mem _ member)) shapes occurrences meanings inputs
          intro name count present atom base supplied
          rw [encodeEdges, InternedOccurrenceCostSemantics.evaluateEdges]
          simp only [survives, Bool.false_eq_true, ↓reduceIte]
          rw [edgeCosts] at present
          rcases List.mem_append.mp present with left | right
          · obtain ⟨after, bound, member⟩ := head.1 name count left atom base supplied
            exact ⟨after, bound, List.mem_append_left _ member⟩
          · obtain ⟨after, bound, member⟩ := tail name count right atom base supplied
            exact ⟨after, bound, List.mem_append_right _ member⟩
termination_by sizeOf edges
end

end MicroCFTA.InternedStoredCostRetention
