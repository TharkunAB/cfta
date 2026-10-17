import MicroCFTA.SourceCurrentConstrainedCapCheckedJointCode

/-!
# Exact source weights through actual constructor growth

Only earlier successful payload reads retain their weights. An absent old
identity can acquire a new payload, so no global weight equality is claimed.
Pair scopes restrict transported free and deep occurrences to earlier reads.
Conditional request laws also require concrete old input and binding witnesses.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSourceWeightTransport
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedNestedFacts
open SourceRecursiveIntersectionThunks
open SourceCurrentConstrainedCapPairOccurrences (identityWeight sourceWeight FreeLE FreeBelow Classified)
open SourceRecursiveIntersectionResultScope (Scope EdgeScope)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs EdgeInputs)
open SourceCurrentConstrainedCapCheckedJointCode (NodeLaw EdgeLaw)
variable {Symbol Guard : Type}

/-- Every named pair has two complete payload reads in the original source. -/
def Supported (source : State Symbol Guard) (pairs : List (Nat × Nat)) : Prop :=
  ∀ pair ∈ pairs, ∃ left right,
    SourcePreparedSharedRows.read source pair.1 = some left ∧
      SourcePreparedSharedRows.read source pair.2 = some right

/-- The empty pair set requires no payload. -/
theorem supported_empty (source : State Symbol Guard) : Supported source [] := by
  intro pair absent
  cases absent

/-- A subset of earlier represented pairs retains its exact payload witnesses. -/
theorem Supported.mono {source : State Symbol Guard} {first last : List (Nat × Nat)}
    (supported : Supported source last) (included : ∀ pair ∈ first, pair ∈ last) : Supported source first :=
  fun pair member => supported pair (included pair member)

/-- Adding an actual represented pair retains every earlier payload witness. -/
theorem Supported.cons {source : State Symbol Guard} {pairs : List (Nat × Nat)}
    (supported : Supported source pairs) (pair : Nat × Nat) (left right : Value Symbol Guard)
    (firstRead : SourcePreparedSharedRows.read source pair.1 = some left)
    (secondRead : SourcePreparedSharedRows.read source pair.2 = some right) : Supported source (pair :: pairs) := by
  intro actual member
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨left, right, firstRead, secondRead⟩
  · exact supported actual old

/-- Actual immutable record and issued-key growth retain each earlier successful payload read. -/
theorem read_grows (before after : State Symbol Guard) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (number : Nat) (value : Value Symbol Guard)
    (found : SourcePreparedSharedRows.read before number = some value) :
    SourcePreparedSharedRows.read after number = some value := by
  obtain ⟨key, issued, stored⟩ := Option.bind_eq_some_iff.mp found
  simp only [SourcePreparedSharedRows.read, history number key issued, Option.bind_some]
  exact growth.nodeRecords key value stored

/-- Exact successful old reads retain their source rank at the same numeric identity. -/
theorem identity_weight (annotation : Guard → Prop) (before after : State Symbol Guard)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (number : Nat) (value : Value Symbol Guard) (found : SourcePreparedSharedRows.read before number = some value) :
    identityWeight annotation after number = identityWeight annotation before number := by
  simp only [identityWeight, found, read_grows before after growth history number value found]

/-- Each represented pair retains its exact source weight after actual heap growth. -/
theorem pair_weight (annotation : Guard → Prop) (before after : State Symbol Guard)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (pairs : List (Nat × Nat)) (supported : Supported before pairs) (pair : Nat × Nat) (member : pair ∈ pairs) :
    sourceWeight annotation after (.intersection pair.1 pair.2) =
      sourceWeight annotation before (.intersection pair.1 pair.2) := by
  obtain ⟨left, right, firstRead, secondRead⟩ := supported pair member
  simp only [sourceWeight, identity_weight annotation before after growth history pair.1 left firstRead,
    identity_weight annotation before after growth history pair.2 right secondRead]

/-- Earlier pair support itself survives the same literal source extension. -/
theorem Supported.grows {before after : State Symbol Guard} {pairs : List (Nat × Nat)}
    (supported : Supported before pairs) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) : Supported after pairs := by
  intro pair member
  obtain ⟨left, right, firstRead, secondRead⟩ := supported pair member
  exact ⟨left, right, read_grows before after growth history _ _ firstRead,
    read_grows before after growth history _ _ secondRead⟩

/-- Every free occurrence in an honest old pair scope retains its exact weight. -/
theorem free_weight (annotation : Guard → Prop) (before after : State Symbol Guard)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (pairs : List (Nat × Nat)) (supported : Supported before pairs) (value : Value Symbol Guard)
    (scope : Scope pairs value) (name : InternedBinderProtocol.Reference) (member : name ∈ value.free) :
    sourceWeight annotation after name = sourceWeight annotation before name := by
  obtain ⟨pair, present, rfl⟩ := scope name member
  exact pair_weight annotation before after growth history pairs supported pair present

/-- Inclusive free-name bounds transfer only on their earlier represented pair scope. -/
theorem free_le (annotation : Guard → Prop) (before after : State Symbol Guard)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (pairs : List (Nat × Nat)) (supported : Supported before pairs) (value : Value Symbol Guard)
    (scope : Scope pairs value) (bound : Nat) (known : FreeLE (sourceWeight annotation before) bound value) :
    FreeLE (sourceWeight annotation after) bound value := by
  intro name member
  rw [free_weight annotation before after growth history pairs supported value scope name member]
  exact known name member

/-- Strict free-name bounds transfer on the same earlier represented pair scope. -/
theorem free_below (annotation : Guard → Prop) (before after : State Symbol Guard)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (pairs : List (Nat × Nat)) (supported : Supported before pairs) (value : Value Symbol Guard)
    (scope : Scope pairs value) (bound : Nat) (known : FreeBelow (sourceWeight annotation before) bound value) :
    FreeBelow (sourceWeight annotation after) bound value := by
  intro name member
  rw [free_weight annotation before after growth history pairs supported value scope name member]
  exact known name member

/-- Coherent actual deep names are free names, so their earlier scoped weights transfer too. -/
theorem classified (annotation : Guard → Prop) (before after : State Symbol Guard)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (pairs : List (Nat × Nat)) (supported : Supported before pairs) (value : Value Symbol Guard)
    (coherent : Coherent after) (available : Available after value) (scope : Scope pairs value)
    (bound : Nat) (known : Classified (sourceWeight annotation before) bound value) :
    Classified (sourceWeight annotation after) bound value := by
  refine ⟨free_le annotation before after growth history pairs supported value scope bound known.free, ?_⟩
  intro name member
  have free := InternedDeepFreeNormalization.deep_free value after coherent available name member
  rw [free_weight annotation before after growth history pairs supported value scope name free]
  exact known.deep name member

/-- A node law rebases only after its old binding and input witnesses are supplied. -/
theorem node_law (annotation : Guard → Prop) (before after : State Symbol Guard)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (supported : Supported before request.domain.key.seen) (coherent : Coherent after) (available : Available after result)
    (oldBindings : OriginalBindings annotation before request.domain.key) (oldInputs : NodeInputs before request)
    (known : NodeLaw annotation before request result) : NodeLaw annotation after request result := by
  intro depth _bindings _inputs left right
  have old := known depth oldBindings oldInputs left right
  exact ⟨old.1, classified annotation before after growth history _ supported result coherent available old.2.2 _ old.2.1, old.2.2⟩

/-- A row law rebases only after its old binding and literal child-input witnesses are supplied. -/
theorem edge_law (annotation : Guard → Prop) (before after : State Symbol Guard)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard)
    (supported : Supported before request.domain.key.seen)
    (oldBindings : OriginalBindings annotation before request.domain.key) (oldInputs : EdgeInputs before request)
    (known : EdgeLaw annotation before request result) : EdgeLaw annotation after request result := by
  intro depth _bindings _inputs left right
  have old := known depth oldBindings oldInputs left right
  refine ⟨old.1, ?_, old.2.2⟩
  intro child member
  exact free_le annotation before after growth history _ supported child (old.2.2 child member) _ (old.2.1 child member)

end MicroCFTA.SourceCurrentConstrainedCapSourceWeightTransport
