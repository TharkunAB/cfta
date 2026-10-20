import MicroCFTA.InternedStoredBodyInvariant
import MicroCFTA.InternedNestedConstructionReplay
import MicroCFTA.InternedGateReconstructionExamples

/-!
# Open nested substitution prepared from actual stored records

Closed source records become captured lexical inputs. Free references use
the replacement environment. Each open stored Mu becomes a smart nested
binder, with its original reference mapped to the nearest local slot.
Execution reuses the complete source constructor and cache protocol.
-/
namespace MicroCFTA.InternedStoredSubstitution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedUnionNormalForm InternedStoredSelfFilter InternedStoredBodyInvariant
open InternedBinderProtocol (Reference NodeKey)

/-- Source substitution maps recursive names to actual complete replacement records. -/
abbrev Environment (Symbol Guard : Type) := Reference → Option (Value Symbol Guard)

mutual
/-- Collect closed constants and reference leaves from the prepared source traversal. -/
def leaves (value : Value Symbol Guard) : List (Value Symbol Guard) :=
  if value.free.isEmpty then [value] else
  match value with
  | .empty | .reference _ => [value]
  | .node _ edges _ _ => edgeLeaves edges
  | .union _ members _ _ => manyLeaves members
  | .mu _ body _ _ => leaves body
termination_by sizeOf value

/-- Ordered source children contribute their original prepared leaves. -/
def manyLeaves : List (Value Symbol Guard) → List (Value Symbol Guard)
  | [] => []
  | first :: rest => leaves first ++ manyLeaves rest
termination_by values => sizeOf values

/-- Original edge metadata adds no substitution variable. -/
def edgeLeaves : List (EdgeValue Symbol Guard) → List (Value Symbol Guard)
  | [] => []
  | .mk _ children :: rest => manyLeaves children ++ edgeLeaves rest
termination_by edges => sizeOf edges
end

/-- Locate an immutable source record by the same identity used in canonical keys. -/
def slot (context : List (Value Symbol Guard)) (value : Value Symbol Guard) : Nat :=
  context.findIdx (fun candidate => candidate.referenceOf == value.referenceOf)

/-- Replace a free reference leaf while retaining a closed constant exactly. -/
def input (environment : Environment Symbol Guard) (value : Value Symbol Guard) : Value Symbol Guard :=
  match value with
  | .reference name => (environment name).getD value
  | _ => value

mutual
/-- Translate the prepared record traversal to the existing complete lexical executor. -/
def encode (context : List (Value Symbol Guard)) (locals : List Reference) (value : Value Symbol Guard) : Syntax Symbol Guard :=
  if value.free.isEmpty then .var (locals.length + slot context value) else
  match value with
  | .empty => .empty
  | .reference name =>
      match locals.findIdx? (· == name) with
      | some index => .var index
      | none => .var (locals.length + slot context value)
  | .node _ edges _ _ => .node (encodeEdges context locals edges)
  | .union _ members _ _ => .union (encodeMany context locals members)
  | .mu entry body _ _ => .binder true (encode context (.interned entry.identity :: locals) body)
termination_by sizeOf value

/-- Retain the source ordering of prepared child plans. -/
def encodeMany (context : List (Value Symbol Guard)) (locals : List Reference) : List (Value Symbol Guard) → List (Syntax Symbol Guard)
  | [] => []
  | first :: rest => encode context locals first :: encodeMany context locals rest
termination_by values => sizeOf values

/-- Rebuild each source edge with its actual symbol and original constraint. -/
def encodeEdges (context : List (Value Symbol Guard)) (locals : List Reference) : List (EdgeValue Symbol Guard) → List (EdgeSyntax Symbol Guard)
  | [] => []
  | .mk entry children :: rest => .mk entry.key.symbol entry.key.constraint (encodeMany context locals children) :: encodeEdges context locals rest
termination_by edges => sizeOf edges
end

/-- Execute prepared substitution, including every open nested binder branch. -/
def execute [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  build (encode (leaves value) [] value) ((leaves value).map (input environment)) state

/-- Unfold the outer stored Mu with its actual complete record as replacement. -/
def unfold [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  match value with
  | .mu entry body _ _ => execute body (fun name => if name = .interned entry.identity then some value else none) state
  | _ => .done value state

mutual
/-- Every prepared leaf is an actual available source descendant or closed input. -/
theorem leaves_available (value : Value Symbol Guard) (state : State Symbol Guard) (available : Available state value) :
    Values state (leaves value) := by
  rw [leaves.eq_def]
  split
  · intro leaf member
    have same : leaf = value := by simpa using member
    exact same ▸ available
  · cases value with
    | empty | reference =>
        intro leaf member
        simp only [List.mem_singleton] at member
        subst leaf
        exact available
    | node entry edges depth free => exact edgeLeaves_available edges state (fun child member => available.children child member)
    | union entry members depth free => exact manyLeaves_available members state (fun child member => available.children child member)
    | mu entry body depth ordinary => exact leaves_available body state (available.children body (by simp [InternedProbeProvenance.children]))
termination_by sizeOf value

/-- Prepared children retain their original source availability. -/
theorem manyLeaves_available (values : List (Value Symbol Guard)) (state : State Symbol Guard) (available : Values state values) :
    Values state (manyLeaves values) := by
  cases values with
  | nil => simp [Values, manyLeaves]
  | cons first rest =>
      intro leaf member
      simp only [manyLeaves] at member
      rcases List.mem_append.mp member with head | tail
      · exact leaves_available first state (available first (by simp)) leaf head
      · exact manyLeaves_available rest state (fun value member => available value (by simp [member])) leaf tail
termination_by sizeOf values

/-- Edge payloads provide the available records used by every prepared child plan. -/
theorem edgeLeaves_available (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value) : Values state (edgeLeaves edges) := by
  cases edges with
  | nil => simp [Values, edgeLeaves]
  | cons first rest =>
      cases first with
      | mk entry children =>
          intro leaf member
          simp only [edgeLeaves] at member
          rcases List.mem_append.mp member with head | tail
          · exact manyLeaves_available children state (fun value member => available value (by simp [EdgeValue.children, member])) leaf head
          · exact edgeLeaves_available rest state (fun value member => available value (by simp [EdgeValue.children, member])) leaf tail
termination_by sizeOf edges
end

/-- The actual substitution environment supplies only available replacements. -/
def Replacements (state : State Symbol Guard) (environment : Environment Symbol Guard) : Prop :=
  ∀ name value, environment name = some value → Available state value

/-- Preparing the lexical inputs establishes their complete record provenance. -/
theorem inputs_available (value : Value Symbol Guard) (environment : Environment Symbol Guard) (state : State Symbol Guard)
    (available : Available state value) (replacements : Replacements state environment) :
    Values state ((leaves value).map (input environment)) := by
  intro selected member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  have source := leaves_available value state available original present
  cases original with
  | empty | node | union | mu => exact source
  | reference name =>
      cases found : environment name with
      | none => simpa [input, found] using source
      | some replacement => simpa [input, found] using replacements name replacement found

/-- Full stored-plan execution derives both cache histories and complete result provenance. -/
theorem execute_verified [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (available : Available state value) (replacements : Replacements state environment) :
    Verified state (execute value environment state) Available :=
  build_verified _ _ state facts (inputs_available value environment state available replacements)

/-- Full prepared execution preserves source flat unions and every stored Mu's self filter. -/
theorem execute_normalized [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (flat : Flat state) (clean : Clean state) (available : Available state value) (replacements : Replacements state environment) :
    Flat (execute value environment state).state ∧ Clean (execute value environment state).state :=
  ⟨build_flat _ _ state facts (inputs_available value environment state available replacements) flat,
    build_clean _ _ state facts (inputs_available value environment state available replacements) flat clean⟩

/-- Repeating one completed prepared binding returns the same record without further allocation. -/
theorem execute_replay [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before after : State Symbol Guard) (result : Value Symbol Guard)
    (final : State Symbol Guard) (valid : Valid before)
    (completed : execute value environment before = .done result final) (growth : Grows final after) :
    execute value environment after = .done result after :=
  build_replay _ _ before after result final valid completed growth

/-- A reported pending outcome still names an actual incomplete canonical cache slot. -/
theorem execute_pending [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (key : NodeKey) (later : State Symbol Guard)
    (pending : execute value environment state = .pending key later) : IsPending key later :=
  build_pending _ _ state key later pending

/-- The single outer-reference replacement inherits provenance from its source Mu record. -/
theorem unfold_verified [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state value) :
    Verified state (unfold value state) Available := by
  cases value with
  | empty | reference | node | union => exact pure_verified state facts _ Available available
  | mu entry body depth ordinary =>
      apply execute_verified body _ state facts (available.children body (by simp [InternedProbeProvenance.children]))
      intro name replacement found
      simp only [] at found
      split at found
      · cases found; exact available
      · contradiction

/-- Read the actual stored body after each open nested reconstruction. -/
def firstStoredUnfold : Outcome Nat Unit (Value Nat Unit) :=
  InternedGateReconstructionExamples.original.bind unfold

/-- The second step prepares the newly reconstructed body's actual complete record. -/
def secondStoredUnfold : Outcome Nat Unit (Value Nat Unit) := firstStoredUnfold.bind unfold

/-- Actual stored-plan reconstruction has the same strict head ranks and increasing cached depth. -/
theorem stored_rank_trace :
    InternedGateReconstructionExamples.ranks firstStoredUnfold = some (1, 3) ∧
    InternedGateReconstructionExamples.ranks secondStoredUnfold = some (0, 3) := by cbv

end MicroCFTA.InternedStoredSubstitution
