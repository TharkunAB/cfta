import MicroCFTA.InternedStoredClosedMuCompletion
import MicroCFTA.InternedStoredSubstitutionScope
import MicroCFTA.InternedMarkedCompletion

/-!
# Actual unfolding of stored open binders with distinct root symbols

Original stored edges supply each open binder's root symbol and nullary
edge. Preparation retains these fields exactly. Distinct enclosing root
symbols then exclude pending readback during actual nested reconstruction.
-/
namespace MicroCFTA.InternedStoredMarkedCompletion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedStoredSubstitution InternedStoredSubstitutionScope InternedStoredUnfoldingRank
open InternedNestedRootLabels InternedMarkedConstruction
open InternedUnionNormalForm InternedStoredSelfFilter InternedUnionHeadGuard InternedGateRank
open InternedBinderProtocol (Reference NodeKey)

/-- Stored complete edge signatures contain a nullary root marker and no other root symbol. -/
def StoredMarked (marker : Symbol) (edges : List (EdgeValue Symbol Guard)) : Prop :=
  (marker, 0) ∈ edges.map signature ∧ ∀ shape ∈ edges.map signature, shape.1 = marker

/-- Each open stored binder has its own root marker, distinct from enclosing markers. -/
inductive PreparedMarked {Symbol Guard : Type} : List Symbol → Value Symbol Guard → Prop where
  | closed (forbidden) (value : Value Symbol Guard) (free : value.free = []) : PreparedMarked forbidden value
  | empty (forbidden) : PreparedMarked forbidden .empty
  | reference (forbidden name) : PreparedMarked forbidden (.reference name)
  | node (forbidden entry) (edges : List (EdgeValue Symbol Guard)) (depth free)
      (children : ∀ child ∈ edges.flatMap EdgeValue.children, PreparedMarked forbidden child) :
      PreparedMarked forbidden (.node entry edges depth free)
  | union (forbidden entry) (members : List (Value Symbol Guard)) (depth free)
      (children : ∀ child ∈ members, PreparedMarked forbidden child) :
      PreparedMarked forbidden (.union entry members depth free)
  | mu (forbidden marker entry nodeEntry) (edges : List (EdgeValue Symbol Guard)) (level free)
      (depth ordinary : Value Symbol Guard) (fresh : marker ∉ forbidden) (marked : StoredMarked marker edges)
      (children : ∀ child ∈ edges.flatMap EdgeValue.children, PreparedMarked (marker :: forbidden) child) :
      PreparedMarked forbidden (.mu entry (.node nodeEntry edges level free) depth ordinary)

/-- Preparation retains the exact original edge symbols and child counts. -/
theorem encoded_signatures (context : List (Value Symbol Guard)) (locals : List Reference)
    (edges : List (EdgeValue Symbol Guard)) :
    (encodeEdges context locals edges).map declared = edges.map signature := by
  induction edges with
  | nil => simp [encodeEdges]
  | cons first rest ih =>
      cases first with
      | mk entry children => simp [encodeEdges, declared, signature, EdgeValue.children, EdgeValue.entry, encodeMany_length, ih]

/-- Original complete marker metadata establishes the static source marker condition. -/
theorem encoded_marked (context : List (Value Symbol Guard)) (locals : List Reference)
    (marker : Symbol) (edges : List (EdgeValue Symbol Guard)) (marked : StoredMarked marker edges) :
    Marked marker (encodeEdges context locals edges) := by
  simpa only [Marked, StoredMarked, encoded_signatures] using marked

mutual
/-- Stored edge metadata derives the full source marker discipline for every prepared binder. -/
theorem encode_tagged (context : List (Value Symbol Guard)) (locals : List Reference)
    (forbidden : List Symbol) (value : Value Symbol Guard) (prepared : PreparedMarked forbidden value) :
    Tagged forbidden (encode context locals value) := by
  rw [encode.eq_def]
  split
  · simp [Tagged]
  · rename_i opened
    cases prepared with
    | closed forbidden value free => simp [free] at opened
    | empty => simp [Tagged]
    | reference forbidden name => cases found : locals.findIdx? (· == name) <;> simp [found, Tagged]
    | node forbidden entry edges depth free children =>
        simpa only [Tagged] using encodeEdges_tagged context locals forbidden edges children
    | union forbidden entry members depth free children =>
        simpa only [Tagged] using encodeMany_tagged context locals forbidden members children
    | mu forbidden marker entry nodeEntry edges level free depth ordinary fresh marked children =>
        have bodyOpen : free.isEmpty = false := by
          cases free with
          | nil => simp [Value.free] at opened
          | cons => rfl
        dsimp only
        rw [encode.eq_def]
        simp only [Value.free, bodyOpen, Bool.false_eq_true, ↓reduceIte]
        simp only [Tagged]
        exact ⟨marker, fresh, encoded_marked context _ marker edges marked,
          encodeEdges_tagged context _ (marker :: forbidden) edges children⟩
termination_by sizeOf value

/-- Ordered stored members retain each enclosing root-symbol restriction. -/
theorem encodeMany_tagged (context : List (Value Symbol Guard)) (locals : List Reference)
    (forbidden : List Symbol) (values : List (Value Symbol Guard))
    (prepared : ∀ value ∈ values, PreparedMarked forbidden value) :
    ManyTagged forbidden (encodeMany context locals values) := by
  cases values with
  | nil => simp [encodeMany, ManyTagged]
  | cons first rest =>
      simp only [encodeMany, ManyTagged]
      exact ⟨encode_tagged context locals forbidden first (prepared first (by simp)),
        encodeMany_tagged context locals forbidden rest (fun value member => prepared value (by simp [member]))⟩
termination_by sizeOf values

/-- Original ordered edge children carry the marker restrictions into the prepared program. -/
theorem encodeEdges_tagged (context : List (Value Symbol Guard)) (locals : List Reference)
    (forbidden : List Symbol) (edges : List (EdgeValue Symbol Guard))
    (prepared : ∀ value ∈ edges.flatMap EdgeValue.children, PreparedMarked forbidden value) :
    EdgesTagged forbidden (encodeEdges context locals edges) := by
  cases edges with
  | nil => simp [encodeEdges, EdgesTagged]
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [encodeEdges, EdgesTagged]
          exact ⟨encodeMany_tagged context locals forbidden children
              (fun value member => prepared value (by simp [EdgeValue.children, member])),
            encodeEdges_tagged context locals forbidden rest
              (fun value member => prepared value (by simp [EdgeValue.children, member]))⟩
termination_by sizeOf edges
end

/-- Actual open nested reconstruction completes from a complete source cache.
The source record metadata supplies all binder separation conditions. -/
theorem execute_complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (covered : Covered [] state) (available : Available state value)
    (replacements : Replacements state environment) (prepared : PreparedMarked [] value) :
    ∃ result final, execute value environment state = .done result final := by
  apply build_completes _ [] (encode_tagged (leaves value) [] [] value prepared) []
    (by intro frame member; cases member)
  exact ⟨facts, inputs_available value environment state available replacements, covered,
    by intro frame member; cases member⟩

/-- Source-normalized guarded unfolding needs no depth bound or successful-result premise,
even when its stored body contains open nested binders. -/
theorem unfold_complete_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (covered : Covered [] state) (flat : Flat state) (clean : Clean state)
    (available : Available state (.mu entry body depth ordinary))
    (prepared : PreparedMarked [] body) (safe : HeadSafe body)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value final, InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done value final ∧
      headRank value < headRank (.mu entry body depth ordinary) := by
  have bodyAvailable : Available state body := available.children body (by simp [InternedProbeProvenance.children])
  have replacements : Replacements state (fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none) := by
    intro name replacement found
    simp only [] at found
    split at found
    · cases found; exact available
    · contradiction
  obtain ⟨value, final, completed⟩ := execute_complete body _ state facts covered bodyAvailable replacements prepared
  exact ⟨value, final, completed, stored_unfold_decreases entry body depth ordinary state facts flat clean
    available safe opened value final completed⟩

end MicroCFTA.InternedStoredMarkedCompletion
