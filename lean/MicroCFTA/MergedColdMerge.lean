import MicroCFTA.MergedSourceSelection
import MicroCFTA.MergedAdaptiveMerge

/-!
# Ordered merge with actual cold comparison effects

The worker preserves source row groups, guards, and the four-row threshold.
Each column completes the actual ordered comparison filter before retained
union construction. Ordinary recursion and comparison use separate bounds.
-/
namespace MicroCFTA.MergedColdMerge
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open InternedEdgeResidency InternedShallowHeap MergedPhysicalWarmup MergedSourceComparison
open MergedPhysicalGroupColumns MergedOrdinaryHeight

/-- Every cold merge action retains the last actual cache on success or failure. -/
abbrev Action (Symbol Guard Output : Type) := State Symbol Guard → Result Symbol Guard Output

/-- Return an existing value without cache effects. -/
def pure (value : Output) : Action Symbol Guard Output := fun state => .done value state

/-- Sequence actions at the exact cache returned by the preceding action. -/
def bind (first : Action Symbol Guard First) (next : First → Action Symbol Guard Output) : Action Symbol Guard Output :=
  fun state => (first state).bind next

/-- Execute an actual finite constructor computation. -/
def work [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Output) : Action Symbol Guard Output :=
  fun state => let result := run computation state; .done result.1 result.2

/-- Execute requests in source order and retain their positional results. -/
def map (call : Request → Action Symbol Guard Output) : List Request → Action Symbol Guard (List Output)
  | [] => pure []
  | first :: rest => bind (call first) fun value => bind (map call rest) fun values => pure (value :: values)

/-- Preserve the singleton, recursive-union, and ordinary-union source branches. -/
def retainedColumn [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (retained : List (Value Symbol Guard)) : Action Symbol Guard (Value Symbol Guard) :=
  match retained with
  | [single] => pure single
  | others => if others.any recursiveBoundary then work (makeUnion others)
    else bind (work (ordinaryUnion others)) recurse

/-- Complete actual stateful filtering before retained-column normalization. -/
def column [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (comparisonFuel : Nat) (inputs : List (Value Symbol Guard)) : Action Symbol Guard (Value Symbol Guard) :=
  bind (MergedSourceSelection.select clear comparisonFuel inputs) (retainedColumn recurse)

/-- A small source edge retains its original guard and processes its children in order. -/
def small [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (edge : EdgeValue Symbol Guard) : Action Symbol Guard (EdgeValue Symbol Guard) :=
  bind (map recurse edge.children) fun children => work (makeEdge edge.entry.key.symbol edge.entry.key.constraint children)

/-- A large source group processes columns in order and builds the Top-guard edge. -/
def large [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (comparisonFuel : Nat) (top : Guard)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) : Action Symbol Guard (EdgeValue Symbol Guard) :=
  bind (map (column recurse clear comparisonFuel)
    (MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length))
    fun children => work (makeEdge first.entry.key.symbol top children)

/-- Apply the exact four-row source threshold to each structural group. -/
def group [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (comparisonFuel : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard)) :
    Action Symbol Guard (List (EdgeValue Symbol Guard)) :=
  if edges.length ≤ 4 then map (small recurse) edges
  else match edges with
  | [] => pure []
  | first :: rest => bind (large recurse clear comparisonFuel top first rest) (fun edge => pure [edge])

/-- Complete all groups before interning the final ordinary node. -/
def root [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (comparisonFuel : Nat) (top : Guard) (groups : List (List (EdgeValue Symbol Guard))) :
    Action Symbol Guard (Value Symbol Guard) :=
  bind (map (group recurse clear comparisonFuel top) groups) fun rows => work (makeNode rows.flatten)

/-- Traverse only closed ordinary roots and use the actual cold source filter in every column. -/
def worker [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (clear : Guard → Bool) (top : Guard) : Nat → Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)
  | ordinaryFuel, comparisonFuel, value => match value with
    | .node _ edges _ free =>
        if free = [] then match ordinaryFuel with
          | 0 => fun state => .failed .exhausted state
          | remaining + 1 => root (worker grouping clear top remaining comparisonFuel) clear comparisonFuel top (grouping edges)
        else pure value
    | _ => pure value

/-- Use the original ordinary height as the derived recursive bound. -/
def execute [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (clear : Guard → Bool) (top : Guard) (comparisonFuel : Nat) (value : Value Symbol Guard) : Action Symbol Guard (Value Symbol Guard) :=
  worker grouping clear top (height value) comparisonFuel value

/-- Completed cold effects retain facts, preparation, both cache families, and issued references. -/
structure Extension (before after : State Symbol Guard) : Prop where
  facts : Facts after
  prepared : Prepared after
  growth : Grows before after
  history : Cache.Extends before.nodes.issued after.nodes.issued

/-- An unchanged cache preserves all cold-effect invariants. -/
theorem Extension.refl (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) : Extension state state :=
  ⟨facts, prepared, grows_refl _, Cache.extends_refl _⟩

/-- Adjacent cold actions compose their exact constructor and reference histories. -/
theorem Extension.trans {before middle after : State Symbol Guard}
    (first : Extension before middle) (second : Extension middle after) : Extension before after :=
  ⟨second.facts, second.prepared, grows_trans first.growth second.growth, Cache.extends_trans first.history second.history⟩

/-- Every earlier available source record remains available after completed cold effects. -/
theorem Extension.available {before after : State Symbol Guard} (extension : Extension before after)
    (value : Value Symbol Guard) (available : Available before value) : Available after value :=
  available.grows before after extension.growth extension.history

/-- A uniform comparison bound stabilizes the complete returned value and cache. -/
def Complete (action : Nat → Action Symbol Guard Output) (state : State Symbol Guard)
    (post : State Symbol Guard → Output → Prop) : Prop :=
  ∃ bound value after, (∀ fuel, bound ≤ fuel → action fuel state = .done value after) ∧ Extension state after ∧ post after value

/-- A no-effect result has a stable comparison bound of zero. -/
theorem pure_complete (value : Output) (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (post : State Symbol Guard → Output → Prop) (holds : post state value) : Complete (fun _ => pure value) state post :=
  ⟨0, value, state, fun _ _ => rfl, .refl state facts prepared, holds⟩

/-- Sequential cold actions combine their stable bounds while preserving the actual intermediate cache. -/
theorem bind_complete (first : Nat → Action Symbol Guard First) (next : Nat → First → Action Symbol Guard Output)
    (state : State Symbol Guard) (pre : State Symbol Guard → First → Prop) (post : State Symbol Guard → Output → Prop)
    (complete : Complete first state pre)
    (continues : ∀ value after, Extension state after → pre after value → Complete (fun fuel => next fuel value) after post) :
    Complete (fun fuel => bind (first fuel) (next fuel)) state post := by
  obtain ⟨bound, value, middle, done, firstExtension, valid⟩ := complete
  obtain ⟨later, output, after, nextDone, nextExtension, checked⟩ := continues value middle firstExtension valid
  refine ⟨max bound later, output, after, ?_, firstExtension.trans nextExtension, checked⟩
  intro fuel enough
  simp only [bind, done fuel (Nat.le_trans (Nat.le_max_left _ _) enough), Result.bind,
    nextDone fuel (Nat.le_trans (Nat.le_max_right _ _) enough)]

/-- An actual constructor supplies a stable cold effect from its source facts and unchanged Mu records. -/
theorem work_complete [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Output)
    (state : State Symbol Guard) (prepared : Prepared state)
    (post : State Symbol Guard → Output → Prop)
    (verified : InternedNestedFacts.Verified state (InternedNestedConstruction.work computation state) post)
    (unchanged : NoNewMu state (run computation state).2) : Complete (fun _ => work computation) state post :=
  ⟨0, (run computation state).1, (run computation state).2, fun _ _ => rfl,
    ⟨verified.facts, prepared.preserve unchanged, verified.growth, verified.history⟩,
    verified.result _ _ rfl⟩

end MicroCFTA.MergedColdMerge
