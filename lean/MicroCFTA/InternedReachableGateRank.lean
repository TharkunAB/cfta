import MicroCFTA.InternedShallowExecution

/-!
# A concrete source gate rank for reachable shallow Mu values

Certified nodes retain their actual cache state and a property of the
queried value. Only Mu records reachable through its children and union
members must have depth-zero bodies. Unrelated cached records can be deeper.
Actual unfolding completes and preserves the reachable property.
-/
namespace MicroCFTA.InternedReachableGateRank
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedUnionNormalForm InternedStoredSelfFilter InternedStoredSubstitution
open InternedStoredShallowCompletion InternedShallowValues InternedShallowExecution InternedGateRank
open InternedBinderProtocol (NodeKey)

/-- An actual source value has shallow reachable Mu records in an unrestricted cache. -/
structure Node (Symbol Guard : Type) where
  state : State Symbol Guard
  value : Value Symbol Guard
  facts : Facts state
  flat : Flat state
  clean : Clean state
  shallow : ShallowValue value
  available : Available state value

/-- A stored child shares the parent's actual canonical cache state. -/
def child (node : Node Symbol Guard) (value : Value Symbol Guard) (available : Available node.state value)
    (shallow : ShallowValue value) : Node Symbol Guard :=
  { node with value := value, available := available, shallow := shallow }

/-- The concrete gate view retains every original ordered source child row. -/
def view (node : Node Symbol Guard) : RecursiveReductionBarrier.View (Node Symbol Guard) :=
  match original : node.value with
  | .empty => .empty
  | .reference _ => .reference
  | .union .. => .union
  | .mu .. => .binder
  | .node entry edges depth free => .branches (edges.attach.map fun edge =>
      edge.val.children.attach.map fun value => child node value.val (by
        apply node.available.children value.val
        rw [original]
        exact List.mem_flatMap.mpr ⟨edge.val, edge.property, value.property⟩) (by
        have parent : ShallowValue (.node entry edges depth free) := original ▸ node.shallow
        cases parent with
        | node _ _ _ _ children =>
            exact children value.val (List.mem_flatMap.mpr ⟨edge.val, edge.property, value.property⟩)))

/-- The concrete view identifies exactly the stored Mu constructor. -/
theorem view_binder (node : Node Symbol Guard) : view node = .binder ↔
    ∃ entry body depth ordinary, node.value = .mu entry body depth ordinary := by
  unfold view
  split <;> simp_all

/-- A total source unfolding result includes its exact executable trace equation. -/
structure Step [DecidableEq (EdgeKey Symbol Guard)] (before : Node Symbol Guard) where
  result : Node Symbol Guard
  actual : InternedStoredSubstitution.unfold before.value before.state = .done result.value result.state

/-- Actual stored-value unfolding completes and remains inside the same representation fragment. -/
def step [DecidableEq (EdgeKey Symbol Guard)] (node : Node Symbol Guard) : Step node := by
  cases original : node.value with
  | empty | reference | node | union =>
      exact ⟨node, by simp only [original, InternedStoredSubstitution.unfold]⟩
  | mu entry body depth ordinary =>
      have available : Available node.state (.mu entry body depth ordinary) := original ▸ node.available
      have bodyAvailable : Available node.state body := available.children body (by simp [InternedProbeProvenance.children])
      have zero := mu_zero entry body depth ordinary (original ▸ node.shallow)
      let environment : Environment Symbol Guard := fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none
      have replacements : Replacements node.state environment := by
        intro name value found
        dsimp only [environment] at found
        split at found
        · cases found; exact available
        · contradiction
      have complete := execute_complete body environment node.state node.facts.coherent bodyAvailable zero
      have verified := execute_verified body environment node.state node.facts bodyAvailable replacements
      have normalized := execute_normalized body environment node.state node.facts node.flat node.clean bodyAvailable replacements
      cases computed : execute body environment node.state with
      | pending key after =>
          exfalso
          obtain ⟨value, final, completed⟩ := complete
          simp [computed] at completed
      | done value after =>
          have afterFacts : Facts after := by simpa only [computed, Outcome.state] using verified.facts
          have afterFlat : Flat after := by simpa only [computed, Outcome.state] using normalized.1
          have afterClean : Clean after := by simpa only [computed, Outcome.state] using normalized.2
          have afterShallow : ShallowValue value :=
            unfold_shallow (.mu entry body depth ordinary) node.state node.facts available (original ▸ node.shallow) value after computed
          exact ⟨⟨after, value, afterFacts, afterFlat, afterClean, afterShallow, verified.result value after computed⟩,
            by simpa only [original, InternedStoredSubstitution.unfold, environment] using computed⟩

/-- Gate dispatch observes exact cached depth and free-set emptiness. Free
name payloads are erased because this gate only tests whether the set is empty. -/
def read [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    ConstrainedRecursionGate.Read (Node Symbol Guard) where
  view := view
  nested := fun node => node.value.depth
  free := fun node => node.value.free.map (fun _ => 0)
  unconstrained := fun node => unconstrained node.value
  unfold := fun node => (step node).result

/-- Actual cached free metadata has exactly the emptiness observed by the gate. -/
theorem read_free_empty [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) (node : Node Symbol Guard) :
    ((read unconstrained).free node).isEmpty = node.value.free.isEmpty := by simp [read]

/-- The source reachable fragment derives a rank for every constrained-gate
unfolding, independently of which binders its constraint test permits. -/
def ranking [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    ConstrainedRecursionGate.UnfoldingRank (read unconstrained) where
  rank := fun node => headRank node.value
  decreases := by
    intro node binder _ opened
    rw [read_free_empty] at opened
    obtain ⟨entry, body, depth, ordinary, original⟩ := (view_binder node).mp binder
    have available : Available node.state (.mu entry body depth ordinary) := original ▸ node.available
    have zero := mu_zero entry body depth ordinary (original ▸ node.shallow)
    have openBody : (Value.mu entry body depth ordinary).free ≠ [] := by
      intro closed
      simp [original, closed] at opened
    have guarded := InternedStoredBodyInvariant.stored_guarded entry body depth ordinary node.state node.facts.coherent
      node.flat node.clean available zero openBody
    have actual := (step node).actual
    rw [original] at actual
    simpa only [read, original] using InternedStoredUnfoldingRank.stored_unfold_decreases entry body depth ordinary node.state
      node.facts node.flat node.clean available guarded.headSafe openBody _ _ actual

/-- A particular source Mu enters the fragment using its own body bound.
No condition is imposed on other Mu payloads in the cache. -/
def fromMu (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (flat : Flat state) (clean : Clean state)
    (available : Available state (.mu entry body depth ordinary)) (zero : body.depth = 0) : Node Symbol Guard :=
  ⟨state, .mu entry body depth ordinary, facts, flat, clean, .mu entry body depth ordinary zero, available⟩

/-- The unbounded source gate is total on this actual representation fragment. -/
def total [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : EqualityNormalize.Path) (node : Node Symbol Guard) : Bool :=
  ConstrainedRecursionGate.total (read unconstrained) (ranking unconstrained) path node

/-- Fuel is only an instrument: sufficiently large fuel always gives the
same actual ranked source decision for every finite path. -/
theorem eventually_exact [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : EqualityNormalize.Path) (node : Node Symbol Guard) :
    ∃ bound, ∀ extra, ConstrainedRecursionGate.nodeMeets (read unconstrained) (bound + extra) path node =
      some (total unconstrained path node) :=
  RankedGateCompletion.eventually_exact (read unconstrained) (ranking unconstrained) path node

end MicroCFTA.InternedReachableGateRank
