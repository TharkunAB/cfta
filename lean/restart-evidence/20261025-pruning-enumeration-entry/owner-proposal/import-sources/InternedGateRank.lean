import MicroCFTA.LexicalGateRank
import MicroCFTA.InternedRecordCoherence

/-!
# Gate ranks at actual smart-constructor branches

The ordinary-node reconstruction branch always returns an ordinary node or
EmptyNode. A union can expose a binder only when its normalized member list
has one element. These statements include empty-child removal, canonical
edge identities, cache hits, union flattening, and duplicate removal.
-/
namespace MicroCFTA.InternedGateRank
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedBinderProtocol (NodeKey NodeRef Reference)

/-- Count only consecutive stored Mu bodies at the root. -/
def headRank : Value Symbol Guard → Nat
  | .mu _ body _ _ => headRank body + 1
  | _ => 0

/-- An ordinary cache key cannot retrieve a binder record in a coherent table. -/
theorem node_fields_rank (identities : List Nat) (entry : Interned NodeKey)
    (value : Value Symbol Guard) (fields : NodeFields (.node identities) entry value) :
    headRank value = 0 := by
  cases value <;> simp_all [NodeFields, headRank, muKey]

/-- A union cache key cannot retrieve a binder record in a coherent table. -/
theorem union_fields_rank (members : List NodeRef) (entry : Interned NodeKey)
    (value : Value Symbol Guard) (fields : NodeFields (.union members) entry value) :
    headRank value = 0 := by
  cases value <;> simp_all [NodeFields, headRank, muKey]

/-- A completed coherent request returns the fields for its requested key. -/
theorem requested_fields (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (fields : ∀ entry, entry.key = key → NodeFields key entry (identify entry)) :
    ∃ entry, NodeFields key entry (nodeStep key identify state).1 := by
  have later := nodeStep_coherent key identify state coherent fields
  have stored := (nodeStep_correct key identify state coherent.valid).2.2
  obtain ⟨entry, _, result⟩ := later.nodes key _ stored
  exact ⟨entry, result⟩

/-- Source mkNode never returns a binder, including the complete cache-hit case. -/
theorem makeNode_rank [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) : headRank (run (makeNode edges) state).1 = 0 := by
  unfold makeNode
  dsimp only
  split
  · rfl
  · rename_i first rest _
    simp only [run]
    obtain ⟨entry, fields⟩ := requested_fields
      (.node ((first :: rest).map (fun edge => edge.entry.identity)))
      (identifyNode (first :: rest)) state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
    exact node_fields_rank _ entry _ fields

/-- The exact source union rank is nonzero only at the singleton branch. -/
theorem makeUnion_rank [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) :
    headRank (run (makeUnion values) state).1 =
      match distinctNodes (values.flatMap unionMembers) with
      | [value] => headRank value
      | _ => 0 := by
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, normalized, run, headRank]
  | cons first rest =>
      cases rest with
      | nil => simp [makeUnion, normalized, run]
      | cons second tail =>
          simp only [makeUnion, normalized]
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges => simpa only [ordinary] using makeNode_rank edges state coherent
          | none =>
              simp only [run]
              obtain ⟨entry, fields⟩ := requested_fields
                (.union ((first :: second :: tail).map Value.referenceOf))
                (fun entry => .union entry (first :: second :: tail)
                  (maximumDepth (first :: second :: tail)) (childFree (first :: second :: tail)))
                state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              exact union_fields_rank _ entry _ fields

/-- Reapplying an ordinary body template derives rank zero after every child
effect. The caller does not supply a rank property for those child results. -/
theorem compile_node_rank [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeTemplate Symbol Guard)) (argument : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (covered : Covered pending state) :
    headRank (run (compile (.node edges) argument) state).1 = 0 := by
  have after := InternedRecordCoherence.run_correct (compileEdges edges argument) state
    (compileEdges_safe edges argument) coherent covered
  simpa only [compile, run_bind] using makeNode_rank
    (run (compileEdges edges argument) state).1 _ after.1

/-- The actual ordinary-body substitution branch strictly decreases a Mu
head. Rebuilt children can contain arbitrary open or closed binders. -/
theorem ordinary_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depthShape ordinaryShape : Value Symbol Guard)
    (rebuiltEdges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) :
    headRank (run (makeNode rebuiltEdges) state).1 < headRank (.mu entry body depthShape ordinaryShape) := by
  rw [makeNode_rank rebuiltEdges state coherent]
  simp [headRank]

/-- A multi-member root union remains a rank-zero gate result after source
normalization. The singleton test uses the actual flattened identity list. -/
theorem union_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depthShape ordinaryShape : Value Symbol Guard)
    (rebuiltMembers : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state)
    (notSingleton : ∀ value, distinctNodes (rebuiltMembers.flatMap unionMembers) ≠ [value]) :
    headRank (run (makeUnion rebuiltMembers) state).1 < headRank (.mu entry body depthShape ordinaryShape) := by
  rw [makeUnion_rank rebuiltMembers state coherent]
  cases members : distinctNodes (rebuiltMembers.flatMap unionMembers) with
  | nil => simp [headRank]
  | cons first rest =>
      cases rest with
      | nil => exact False.elim (notSingleton first members)
      | cons second tail => simp [headRank]

/-- Construct a closed recursive operand, then remove the other root union
operand. The source singleton branch exposes the existing binder. -/
def filterFixture : Nat × Nat :=
  let recursive := createMu (Symbol := Nat) (Guard := Unit)
    (.node [.mk 0 () [.argument]]) empty
  let joined := run (makeUnion [.reference (.uninterned 999), recursive.1]) recursive.2
  let filtered := run (withoutSelfReference (.uninterned 999) joined.1) joined.2
  (headRank joined.1, headRank filtered.1)

/-- The source root filter can increase head rank. Its lexical list-preserving
lemma cannot be used for source union normalization without another invariant. -/
theorem filter_can_expose_binder : filterFixture = (0, 1) := by decide +kernel

end MicroCFTA.InternedGateRank
