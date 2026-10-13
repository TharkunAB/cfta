import MicroCFTA.EqualityRawLeafProduct

/-!
# Strict progress for actual raw leaf identities

Each physical Cartesian output retains finite original atom support. Its
source requests therefore have a raw row certificate without changing the
request sequence. Exact physical identity then derives strict progress.
-/
namespace MicroCFTA.EqualityRawLeafProgress
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedFreshProbeKeys InternedEdgeResidency GuardConjunction
open EqualityRawLeafConstruction EqualityRawLeafIdentity EqualityRawLeafProduct

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Every declared residual draws its outer atoms from the original finite inventory. -/
def Supported (initial : List (Guard Formula)) (rows : List (Fin symbols × Guard Formula)) : Prop :=
  ∀ row ∈ rows, ∀ atom ∈ atoms row.2, atom ∈ SourceLeafRowProgress.basis initial

/-- Attach the derived support proof without changing any raw source row. -/
def certify (rows : List (Fin symbols × Guard Formula)) (supported : Supported initial rows) :
    List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial) :=
  match rows with
  | [] => []
  | first :: rest => (first.1, ⟨first.2, supported first (by simp)⟩) ::
      certify rest (fun row member => supported row (by simp [member]))

/-- Certification leaves the exact ordered declaration list unchanged. -/
theorem certify_exact (rows : List (Fin symbols × Guard Formula)) (supported : Supported initial rows) :
    declarations (certify rows supported) = rows := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
      simp only [certify, declarations, List.map_cons]
      exact congrArg (first :: ·) (ih _)

/-- Every actual physical input declaration retains its original support proof. -/
theorem physical_supported (rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (state : State (Fin symbols) ConstraintKey) (coherent : Coherent state) (linked : Linked state) :
    Supported initial ((nodeEdges (run (build (declarations rows)) state).1).map declaration) := by
  intro row member atom present
  obtain ⟨member, _⟩ := (physical_declarations _ state coherent linked row).mp member
  obtain ⟨⟨symbol, raw⟩, _, rfl⟩ := List.mem_map.mp member
  exact raw.property atom present

/-- The actual hash join retains support because source conjunction only unions outer atoms. -/
theorem cross_supported (first second : List (Fin symbols × Guard Formula))
    (left : Supported initial first) (right : Supported initial second) : Supported initial (cross first second) := by
  intro row member atom present
  obtain ⟨a, aMember, b, bMember, _, rfl⟩ := (cross_member first second row).mp member
  exact ((merge_mem _ _ _ _).mp present).elim (left a aMember atom) (right b bMember atom)

/-- Actual physical Cartesian requests admit finite raw certificates in exactly their source order. -/
theorem product_certified (first second : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (leftState rightState : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState) :
    ∃ rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial),
      product (run (build (declarations first)) leftState).1
        (run (build (declarations second)) rightState).1 = build (declarations rows) := by
  let left := (nodeEdges (run (build (declarations first)) leftState).1).map declaration
  let right := (nodeEdges (run (build (declarations second)) rightState).1).map declaration
  have supported : Supported initial (cross left right) := cross_supported left right
    (physical_supported first leftState leftCoherent leftLinked)
    (physical_supported second rightState rightCoherent rightLinked)
  exact ⟨certify (cross left right) supported, congrArg build (certify_exact (cross left right) supported).symm⟩

/-- Identity-oriented Cartesian requests retain exact ordered raw certificates. -/
theorem orderedProduct_certified (first second : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (leftState rightState : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState) :
    ∃ rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial),
      orderedProduct (run (build (declarations first)) leftState).1
        (run (build (declarations second)) rightState).1 = build (declarations rows) := by
  unfold orderedProduct
  split
  · exact product_certified second first rightState leftState rightCoherent leftCoherent rightLinked leftLinked
  · exact product_certified first second leftState rightState leftCoherent rightCoherent leftLinked rightLinked

/-- A changed physical source identity strictly decreases the derived raw leaf rank. -/
theorem intersect_strict (first second : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (leftState rightState state : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState) (coherent : Coherent state)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState) (linked : Linked state)
    (leftGrowth : Grows (run (build (declarations first)) leftState).2 state)
    (rightGrowth : Grows (run (build (declarations second)) rightState).2 state)
    (changed : (run (intersect (run (build (declarations first)) leftState).1
      (run (build (declarations second)) rightState).1) state).1.referenceOf ≠
        (run (build (declarations first)) leftState).1.referenceOf) :
    SourceNoncanonicalLeafProgress.rank (read (initial := initial) (run (intersect (run (build (declarations first)) leftState).1
      (run (build (declarations second)) rightState).1) state).1) <
        SourceNoncanonicalLeafProgress.rank (denote first) := by
  have decoded := intersect_read first second leftState rightState state leftCoherent rightCoherent coherent
    leftLinked rightLinked linked leftGrowth rightGrowth
  rw [decoded]
  apply SourceNoncanonicalLeafProgress.intersect_strict
  intro same
  by_cases identity : (run (build (declarations first)) leftState).1.referenceOf =
      (run (build (declarations second)) rightState).1.referenceOf
  · exact changed (by simp only [intersect, identity, ↓reduceIte, run])
  · obtain ⟨rows, sourceRows⟩ := orderedProduct_certified first second leftState rightState
      leftCoherent rightCoherent leftLinked rightLinked
    have exactWork : intersect (run (build (declarations first)) leftState).1
        (run (build (declarations second)) rightState).1 = build (declarations rows) := by
      simpa only [intersect, identity, ↓reduceIte] using sourceRows
    let output := run (build (declarations rows)) state
    have after : Coherent output.2 := InternedErasedEdgeReplay.run_coherent _ state (build_safe _) coherent
    have growth : Grows state output.2 := (InternedConstructorTemplates.run_correct _ state coherent.valid).2
    have equalRows : denote rows = denote first := by
      rw [exactWork, build_read rows state coherent linked] at decoded
      exact decoded.trans same
    have equalValues := (raw_identity_iff rows first state leftState output.2 coherent leftCoherent after
      linked leftLinked (grows_refl output.2) (grows_trans leftGrowth growth)).mpr equalRows
    apply changed
    rw [exactWork]
    exact equalValues

end MicroCFTA.EqualityRawLeafProgress
