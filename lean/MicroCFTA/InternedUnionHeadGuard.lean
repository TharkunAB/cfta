import MicroCFTA.InternedNormalizationFree

/-!
# Source union normalization preserves constructor guards

A constructor stops the gate's current path. Root unions can expose a
member, but cannot remove a constructor inside that member. The proofs
include canonical readback and every source union normalization branch.
-/
namespace MicroCFTA.InternedUnionHeadGuard
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedTemplateProvenance InternedNormalizationFree InternedGateRank
open InternedBinderProtocol (NodeKey)

/-- No root union path reaches Mu before a constructor or a reference. -/
inductive HeadSafe : Value Symbol Guard → Prop where
  | empty : HeadSafe .empty
  | reference (name) : HeadSafe (.reference name)
  | node (entry edges depth free) : HeadSafe (.node entry edges depth free)
  | union (entry members depth free) (safe : ∀ value ∈ members, HeadSafe value) :
      HeadSafe (.union entry members depth free)

/-- Constructor guards imply rank zero at the current source gate position. -/
theorem HeadSafe.rank (safe : HeadSafe value) : headRank value = 0 := by
  cases safe <;> rfl

/-- Root flattening cannot cross a constructor guard. -/
theorem HeadSafe.flatten {value : Value Symbol Guard} (safe : HeadSafe value) : ∀ member ∈ unionMembers value, HeadSafe member := by
  cases safe with
  | empty => simp [unionMembers]
  | reference name => simpa [unionMembers] using HeadSafe.reference (Symbol := Symbol) (Guard := Guard) name
  | node entry edges depth free => simpa [unionMembers] using HeadSafe.node entry edges depth free
  | union entry members depth free children => exact children

/-- A coherent ordinary request returns an ordinary record or EmptyNode. -/
theorem makeNode_safeHead [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) : HeadSafe (run (makeNode edges) state).1 := by
  unfold makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest _
    simp only [run]
    obtain ⟨entry, fields⟩ := requested_fields
      (.node ((first :: rest).map (fun edge => edge.entry.identity)))
      (identifyNode (first :: rest)) state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
    generalize found : (nodeStep _ _ state).1 = value at fields ⊢
    cases value <;> simp [NodeFields, muKey] at fields <;> try contradiction
    exact .node _ _ _ _

/-- Complete cached union readback contains the requested immutable member records. -/
theorem union_readback_safeHead (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (value : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry value)
    (output : Available state value) (inputs : ∀ member ∈ members, Available state member)
    (guarded : ∀ member ∈ members, HeadSafe member) : HeadSafe value := by
  cases value with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual actualMembers depth free =>
      have equal := value_lists_equal state coherent members actualMembers
        (fun value member => (inputs value member).resident)
        (fun value member => (output.children value member).resident)
        (NodeKey.union.inj fields.2.1)
      exact .union _ _ _ _ (equal ▸ guarded)

/-- Every source union branch preserves the input constructor guards,
including singleton collapse and canonical cache hits. -/
theorem makeUnion_safeHead [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (available : ∀ value ∈ values, Available state value)
    (guarded : ∀ value ∈ values, HeadSafe value) : HeadSafe (run (makeUnion values) state).1 := by
  have allAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available original (available original included) value selected
  have allGuarded : ∀ value ∈ distinctNodes (values.flatMap unionMembers), HeadSafe value := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact (guarded original included).flatten value selected
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simpa [makeUnion, normalized, run] using HeadSafe.empty (Symbol := Symbol) (Guard := Guard)
  | cons first rest =>
      cases rest with
      | nil => simpa [makeUnion, normalized, run] using allGuarded first (by simp [normalized])
      | cons second tail =>
          have membersAvailable : ∀ value ∈ first :: second :: tail, Available state value := by simpa [normalized] using allAvailable
          have membersGuarded : ∀ value ∈ first :: second :: tail, HeadSafe value := by simpa [normalized] using allGuarded
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges => simpa only [makeUnion, normalized, ordinary] using makeNode_safeHead edges state coherent
          | none =>
              let members := first :: second :: tail
              let key := NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let after := (nodeStep key identify state).2
              let result := (nodeStep key identify state).1
              have built := makeUnion_available values state coherent cached available
              have output : Available after result := by simpa only [makeUnion, normalized, ordinary, run] using built.2.2
              have later : Coherent after := by simpa only [makeUnion, normalized, ordinary, run] using built.1
              have inputs : ∀ value ∈ members, Available after value := by
                intro value member
                simpa only [makeUnion, normalized, ordinary, run] using
                  available_after_run (makeUnion values) state coherent.valid (membersAvailable value member)
              obtain ⟨actual, fields⟩ := requested_fields key identify state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              simpa only [makeUnion, normalized, ordinary, run] using
                union_readback_safeHead after later members actual result fields output inputs membersGuarded

/-- Every argument occurrence at a root union path lies below an ordinary constructor. -/
inductive Guarded : Template Symbol Guard → Prop where
  | captured (value) (safe : HeadSafe value) : Guarded (.captured value)
  | node (edges) : Guarded (.node edges)
  | union (members) (safe : ∀ template ∈ members, Guarded template) : Guarded (.union members)

mutual
/-- Rebuilding guarded source templates cannot expose any inserted Mu at the
current gate position. The replacement itself can contain arbitrary binders. -/
theorem compile_safeHead [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (argument : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (argumentAvailable : Available state argument)
    (captured : ∀ value ∈ captures template, Available state value) (guarded : Guarded template) :
    HeadSafe (run (compile template argument) state).1 := by
  cases guarded with
  | captured value safe => simpa only [compile, run] using safe
  | node edges =>
      simp only [captures] at captured
      have checked := compileEdges_available edges argument state coherent cached argumentAvailable captured
      simpa only [compile, run_bind] using makeNode_safeHead (run (compileEdges edges argument) state).1 _ checked.1
  | union members safe =>
      simp only [captures] at captured
      have checked := compileMany_available members argument state coherent cached argumentAvailable captured
      have headSafe := compileMany_safeHead members argument state coherent cached argumentAvailable captured safe
      simpa only [compile, run_bind] using makeUnion_safeHead (run (compileMany members argument) state).1 _
        checked.1 checked.2.1 checked.2.2 headSafe
termination_by sizeOf template

/-- Ordered child effects preserve each guarded root member. -/
theorem compileMany_safeHead [DecidableEq (EdgeKey Symbol Guard)] (templates : List (Template Symbol Guard))
    (argument : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (argumentAvailable : Available state argument)
    (captured : ∀ value ∈ manyCaptures templates, Available state value)
    (guarded : ∀ template ∈ templates, Guarded template) :
    ∀ value ∈ (run (compileMany templates argument) state).1, HeadSafe value := by
  cases templates with
  | nil => simp [compileMany, run]
  | cons first rest =>
      have headCaptured : ∀ value ∈ captures first, Available state value :=
        fun value member => captured value (by simpa only [manyCaptures] using List.mem_append_left (manyCaptures rest) member)
      have tailCaptured : ∀ value ∈ manyCaptures rest, Available state value :=
        fun value member => captured value (by simpa only [manyCaptures] using List.mem_append_right (captures first) member)
      have checked := compile_available first argument state coherent cached argumentAvailable headCaptured
      have head := compile_safeHead first argument state coherent cached argumentAvailable headCaptured (guarded first (by simp))
      have tail := compileMany_safeHead rest argument _ checked.1 checked.2.1
        (available_after_run (compile first argument) state coherent.valid argumentAvailable)
        (fun value member => available_after_run (compile first argument) state coherent.valid (tailCaptured value member))
        (fun template member => guarded template (by simp [member]))
      simpa only [compileMany, run_bind, run, List.mem_cons] using
        (show ∀ value, value = (run (compile first argument) state).1 ∨
          value ∈ (run (compileMany rest argument) (run (compile first argument) state).2).1 → HeadSafe value from
          fun value member => member.elim (fun same => same ▸ head) (tail value))
termination_by sizeOf templates
end

/-- The guarded fragment supplies a strict actual source head-rank decrease. -/
theorem guarded_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state)
    (available : Available state (.mu entry body depth ordinary))
    (captured : ∀ value ∈ captures template, Available state value) (guarded : Guarded template) :
    headRank (run (compile template (.mu entry body depth ordinary)) state).1 <
      headRank (.mu entry body depth ordinary) := by
  rw [(compile_safeHead template _ state coherent cached available captured guarded).rank]
  simp [headRank]

end MicroCFTA.InternedUnionHeadGuard
