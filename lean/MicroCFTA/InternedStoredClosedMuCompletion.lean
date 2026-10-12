import MicroCFTA.InternedStoredShallowCompletion

/-!
# Actual unfolding with arbitrarily deep closed nested binders

Source preparation retains each closed record as one input leaf. A stored
body can therefore contain closed Mu records at any depth without a new
binder request. Completion follows from the original records, without a
numeric depth bound or an assumed successful execution.
-/
namespace MicroCFTA.InternedStoredClosedMuCompletion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedStoredSubstitution
open InternedStoredShallowCompletion InternedStoredUnfoldingRank
open InternedUnionNormalForm InternedStoredSelfFilter InternedUnionHeadGuard InternedGateRank
open InternedBinderProtocol (Reference NodeKey)

/-- Preparation reaches no open Mu. Closed records remain source input leaves. -/
inductive PreparedWithoutMu {Symbol Guard : Type} : Value Symbol Guard → Prop where
  | closed (value : Value Symbol Guard) (free : value.free = []) : PreparedWithoutMu value
  | empty : PreparedWithoutMu .empty
  | reference (name) : PreparedWithoutMu (.reference name)
  | node (entry) (edges : List (EdgeValue Symbol Guard)) (depth free)
      (children : ∀ child ∈ edges.flatMap EdgeValue.children, PreparedWithoutMu child) :
      PreparedWithoutMu (.node entry edges depth free)
  | union (entry) (members : List (Value Symbol Guard)) (depth free)
      (children : ∀ child ∈ members, PreparedWithoutMu child) :
      PreparedWithoutMu (.union entry members depth free)

mutual
/-- Closed nested records do not prepare a dynamic source binder request. -/
theorem encode_withoutMu (context : List (Value Symbol Guard)) (locals : List Reference)
    (value : Value Symbol Guard) (prepared : PreparedWithoutMu value) :
    BinderFree (encode context locals value) := by
  rw [encode.eq_def]
  split
  · simp [BinderFree]
  · rename_i opened
    cases prepared with
    | closed value free => simp [free] at opened
    | empty => simp [BinderFree]
    | reference name => cases found : locals.findIdx? (· == name) <;> simp [found, BinderFree]
    | node entry edges depth free children =>
        simpa only [BinderFree] using encodeEdges_withoutMu context locals edges children
    | union entry members depth free children =>
        simpa only [BinderFree] using encodeMany_withoutMu context locals members children
termination_by sizeOf value

/-- Ordered source members each retain their original closed leaves. -/
theorem encodeMany_withoutMu (context : List (Value Symbol Guard)) (locals : List Reference)
    (values : List (Value Symbol Guard)) (prepared : ∀ value ∈ values, PreparedWithoutMu value) :
    ManyBinderFree (encodeMany context locals values) := by
  cases values with
  | nil => simp [encodeMany, ManyBinderFree]
  | cons first rest =>
      simp only [encodeMany, ManyBinderFree]
      exact ⟨encode_withoutMu context locals first (prepared first (by simp)),
        encodeMany_withoutMu context locals rest (fun value member => prepared value (by simp [member]))⟩
termination_by sizeOf values

/-- Edge preparation stops at every original closed child record. -/
theorem encodeEdges_withoutMu (context : List (Value Symbol Guard)) (locals : List Reference)
    (edges : List (EdgeValue Symbol Guard))
    (prepared : ∀ value ∈ edges.flatMap EdgeValue.children, PreparedWithoutMu value) :
    EdgesBinderFree (encodeEdges context locals edges) := by
  cases edges with
  | nil => simp [encodeEdges, EdgesBinderFree]
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [encodeEdges, EdgesBinderFree]
          exact ⟨encodeMany_withoutMu context locals children
              (fun value member => prepared value (by simp [EdgeValue.children, member])),
            encodeEdges_withoutMu context locals rest
              (fun value member => prepared value (by simp [EdgeValue.children, member]))⟩
termination_by sizeOf edges
end

/-- Stored source substitution completes without a bound on cached Mu depth. -/
theorem execute_complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard)
    (prepared : PreparedWithoutMu value) :
    ∃ result final, execute value environment state = .done result final :=
  InternedStoredShallowCompletion.build_complete _ _ state (encode_withoutMu (leaves value) [] value prepared)

/-- Actual guarded unfolding completes and decreases head rank even when
closed nested Mu records have arbitrary cached depth. -/
theorem unfold_complete_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (flat : Flat state) (clean : Clean state)
    (available : Available state (.mu entry body depth ordinary))
    (prepared : PreparedWithoutMu body) (safe : HeadSafe body)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value final, InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done value final ∧
      headRank value < headRank (.mu entry body depth ordinary) := by
  obtain ⟨value, final, completed⟩ := execute_complete body _ state prepared
  exact ⟨value, final, completed, stored_unfold_decreases entry body depth ordinary state facts flat clean
    available safe opened value final completed⟩

/-- Every coherent depth-zero body belongs to this larger source fragment. -/
theorem zero_prepared (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) (zero : value.depth = 0) :
    PreparedWithoutMu value := by
  cases value with
  | empty => exact .empty
  | reference name => exact .reference name
  | mu => simp [Value.depth] at zero
  | node entry edges depth free =>
      apply PreparedWithoutMu.node
      intro child member
      exact zero_prepared child state coherent (available.children child member)
        (Nat.eq_zero_of_le_zero (zero ▸ InternedUnionSeparation.child_depth state coherent _ child available member))
  | union entry members depth free =>
      apply PreparedWithoutMu.union
      intro child member
      exact zero_prepared child state coherent (available.children child member)
        (Nat.eq_zero_of_le_zero (zero ▸ InternedUnionSeparation.child_depth state coherent _ child available member))
termination_by sizeOf value
decreasing_by
  · obtain ⟨edge, included, inner⟩ := List.mem_flatMap.mp member
    have outerSize := List.sizeOf_lt_of_mem included
    have innerSize := List.sizeOf_lt_of_mem inner
    cases edge
    simp_all only [EdgeValue.children]
    simp_wf
    simp_all only [EdgeValue.mk.sizeOf_spec]
    omega
  · have smaller := List.sizeOf_lt_of_mem member
    simp_wf
    simp_all only [Value.union.sizeOf_spec]
    omega

end MicroCFTA.InternedStoredClosedMuCompletion
