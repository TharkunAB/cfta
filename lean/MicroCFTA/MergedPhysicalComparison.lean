import MicroCFTA.MergedPhysicalWarmup
import MicroCFTA.MergedComparisonSource
import MicroCFTA.EpsilonUnion

/-!
# A physical comparison inventory after actual source warmup

The inventory contains complete cache records, their immediate children,
the original roots, and the actual warmup results. Every recursive step
replays in the prepared cache. Ordinary edges retain their stored children.
The resulting finite closure supplies the coverage checker's pair bound.
-/
namespace MicroCFTA.MergedPhysicalComparison
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open InternedBinderProtocol (NodeKey)
open MergedPhysicalWarmup

/-- Include the exact source records and the finite primitive leaves that their reads can return. -/
def inventory (state : State Symbol Guard) (roots outputs : List (Value Symbol Guard)) : List (Value Symbol Guard) :=
  .empty :: (roots ++ outputs ++ nodeInventory state ++ (nodeInventory state).flatMap children)

/-- Coherent source reference identity agrees with complete record equality on available values. -/
theorem same_record (state : State Symbol Guard) (facts : Facts state) (first second : Value Symbol Guard)
    (firstAvailable : Available state first) (secondAvailable : Available state second) :
    first.referenceOf = second.referenceOf ↔ first = second :=
  ⟨resident_reference_injective state facts.coherent first second firstAvailable.resident secondAvailable.resident,
    congrArg Value.referenceOf⟩

/-- Every inventory element retains actual source availability in the prepared cache. -/
theorem inventory_available (state : State Symbol Guard) (facts : Facts state)
    (roots outputs : List (Value Symbol Guard)) (inputs : Values state roots) (results : Values state outputs) :
    Values state (inventory state roots outputs) := by
  intro value member
  simp only [inventory, List.mem_cons, List.mem_append, List.mem_flatMap] at member
  rcases member with same | ((root | output) | record) | ⟨parent, record, child⟩
  · rw [same]; exact empty_available state
  · exact inputs value root
  · exact results value output
  · exact MergedPhysicalWarmup.inventory_available state facts.cached value record
  · exact (MergedPhysicalWarmup.inventory_available state facts.cached parent record).children value child

/-- Every immediate child of a complete available record is explicitly listed. -/
theorem child_member (state : State Symbol Guard) (facts : Facts state) (roots outputs : List (Value Symbol Guard))
    (value child : Value Symbol Guard) (available : Available state value) (member : child ∈ children value) :
    child ∈ inventory state roots outputs := by
  have stored : ∃ entry : Interned NodeKey, state.nodeRecords entry.key = some value := by
    cases value with
    | empty | reference => simp [children] at member
    | node entry | union entry | mu entry => exact ⟨entry, available.resident entry rfl⟩
  obtain ⟨entry, stored⟩ := stored
  have parent := inventory_complete state facts.coherent entry.key value stored
  simp only [inventory, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨value, parent, member⟩))

/-- The epsilon reader follows a union member or the actual completed stored-body unfolding. -/
def successors [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) :
    Value Symbol Guard → List (Value Symbol Guard)
  | .union _ members _ _ => members
  | value@(.mu ..) =>
      match InternedStoredSubstitution.unfold value state with
      | .done result _ => [result]
      | .pending .. => []
  | _ => []

/-- Read one constructor's exact source label, ordered children, and guard. -/
def constructorRows (meaning : Guard → Language.Term Symbol → Bool) :
    Value Symbol Guard → List (Language.Edge (Value Symbol Guard) Symbol)
  | .node _ edges _ _ => edges.map fun edge =>
      ⟨edge.entry.key.symbol, edge.children, meaning edge.entry.key.constraint⟩
  | _ => []

/-- Each physical epsilon successor stays in the derived inventory. -/
theorem successors_closed [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state)
    (roots outputs : List (Value Symbol Guard)) (inputs : Values state roots) (results : Values state outputs)
    (ready : Ready state outputs) (value : Value Symbol Guard) (included : value ∈ inventory state roots outputs)
    (next : Value Symbol Guard) (member : next ∈ successors state value) : next ∈ inventory state roots outputs := by
  have available := inventory_available state facts roots outputs inputs results value included
  cases value with
  | empty | reference | node => simp [successors] at member
  | union entry members depth free =>
      exact child_member state facts roots outputs _ next available member
  | mu entry body depth ordinary =>
      obtain ⟨result, retained, done⟩ := ready entry body depth ordinary available
      have same : next = result := by simpa only [successors, done, List.mem_singleton] using member
      rw [same]
      simp [inventory, retained]

/-- The exact constructor rows retain children already listed in the physical inventory. -/
theorem constructor_children (state : State Symbol Guard) (facts : Facts state)
    (roots outputs : List (Value Symbol Guard)) (value : Value Symbol Guard) (available : Available state value)
    (meaning : Guard → Language.Term Symbol → Bool) (edge : Language.Edge (Value Symbol Guard) Symbol)
    (member : edge ∈ constructorRows meaning value) (child : Value Symbol Guard) (included : child ∈ edge.children) :
    child ∈ inventory state roots outputs := by
  cases value with
  | empty | reference | union | mu => simp [constructorRows] at member
  | node entry edges depth free =>
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact child_member state facts roots outputs _ child available (List.mem_flatMap.mpr ⟨original, present, included⟩)

noncomputable section
local instance : DecidableEq (Value Symbol Guard) := Classical.typeDecidableEq _

/-- Traverse the physical epsilon closure with one visit per listed record. -/
def visited [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (roots outputs : List (Value Symbol Guard)) (root : Value Symbol Guard) : List (Value Symbol Guard) :=
  EpsilonUnion.visit (successors state) (inventory state roots outputs).eraseDups [root]

/-- The finite traversal contains precisely the actual reachable epsilon records. -/
theorem visited_exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state)
    (roots outputs : List (Value Symbol Guard)) (inputs : Values state roots) (results : Values state outputs)
    (ready : Ready state outputs) (root : Value Symbol Guard) (rootIn : root ∈ inventory state roots outputs)
    (value : Value Symbol Guard) :
    value ∈ visited state roots outputs root ↔ Productivity.Reachable (successors state) [root] value := by
  have spec := EpsilonUnion.visit_spec (successors state) (inventory state roots outputs).eraseDups [root]
    (SymbolicDriver.eraseDups_nodup _)
  have covered : ∀ value, Productivity.Reachable (successors state) [root] value →
      value ∈ (inventory state roots outputs).eraseDups := by
    intro value reached
    apply List.mem_eraseDups.mpr
    induction reached with
    | seed member => simpa only [List.mem_singleton.mp member] using rootIn
    | step prior member ih => exact successors_closed state facts roots outputs inputs results ready _ ih _ member
  constructor
  · exact spec.reachable value
  · intro reached
    induction reached with
    | seed member => exact (spec.requested _ member).resolve_left (fun missing => missing (covered _ (.seed member)))
    | step prior member ih => exact (spec.closed _ ih _ member).resolve_left (fun missing => missing (covered _ (.step prior member)))

/-- Expose all original constructor rows at the visited physical records. -/
def rows [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (roots outputs : List (Value Symbol Guard)) (meaning : Guard → Language.Term Symbol → Bool) :
    Language.Automaton (Value Symbol Guard) Symbol :=
  fun root => (visited state roots outputs root).flatMap (constructorRows meaning)

/-- Literal EmptyNode exposes no source row in the derived physical graph. -/
theorem rows_empty [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (roots outputs : List (Value Symbol Guard)) (meaning : Guard → Language.Term Symbol → Bool) :
    rows state roots outputs meaning .empty = [] := by
  have included : (Value.empty : Value Symbol Guard) ∈ (inventory state roots outputs).eraseDups := by
    simp [inventory]
  simp only [rows, visited, EpsilonUnion.visit, included, ↓reduceDIte, successors, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, constructorRows, List.nil_append]

/-- Every recursive comparison child stays in the same derived finite physical inventory. -/
theorem rows_closed [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state)
    (roots outputs : List (Value Symbol Guard)) (inputs : Values state roots) (results : Values state outputs)
    (meaning : Guard → Language.Term Symbol → Bool) :
    MergedComparisonInventory.Closed (rows state roots outputs meaning) (· ∈ inventory state roots outputs) := by
  intro root _ edge member child included
  obtain ⟨value, visitedMember, rowMember⟩ := List.mem_flatMap.mp member
  have spec := EpsilonUnion.visit_spec (successors state) (inventory state roots outputs).eraseDups [root]
    (SymbolicDriver.eraseDups_nodup _)
  have present := List.mem_eraseDups.mp (spec.allocated value visitedMember)
  exact constructor_children state facts roots outputs value
    (inventory_available state facts roots outputs inputs results value present) meaning edge rowMember child included

/-- Prepared source records derive a finite later physical comparison graph and its explicit pair bound. -/
theorem prepared_comparison [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (roots : List (Value Symbol Guard)) (inputs : Values before roots)
    (meaning : Guard → Language.Term Symbol → Bool) :
    ∃ outputs after, warmup (nodeInventory before) before = .done outputs after ∧
      Grows before after ∧ Facts after ∧ Values after roots ∧ Values after outputs ∧ Ready after outputs ∧
      (∀ root ∈ roots, ∀ value, value ∈ visited after roots outputs root ↔
        Productivity.Reachable (successors after) [root] value) ∧
      ∀ unconstrained, ∀ wide ∈ roots, ∀ narrow ∈ roots, ∀ extra,
        MergedComparisonSource.check (rows after roots outputs meaning) (fun value => value.referenceOf == .empty) unconstrained
            ((inventory after roots outputs).length * (inventory after roots outputs).length + extra) [] wide narrow =
          MergedComparisonSource.check (rows after roots outputs meaning) (fun value => value.referenceOf == .empty) unconstrained
            ((inventory after roots outputs).length * (inventory after roots outputs).length) [] wide narrow := by
  obtain ⟨outputs, after, done, afterFacts, growth, history, _, results, ready⟩ := prepare before facts prepared
  have afterInputs : Values after roots := fun value member => (inputs value member).grows before after growth history
  refine ⟨outputs, after, done, growth, afterFacts, afterInputs, results, ready, ?_, ?_⟩
  · intro root member value
    exact visited_exact after afterFacts roots outputs afterInputs results ready root (by simp [inventory, member]) value
  · intro unconstrained wide wideIn narrow narrowIn extra
    exact MergedComparisonSource.check_saturated (rows after roots outputs meaning) (fun value => value.referenceOf == .empty) unconstrained
      (inventory after roots outputs) (rows_closed after afterFacts roots outputs afterInputs results meaning)
      wide narrow (by simp [inventory, wideIn]) (by simp [inventory, narrowIn]) extra

end
end MicroCFTA.MergedPhysicalComparison
