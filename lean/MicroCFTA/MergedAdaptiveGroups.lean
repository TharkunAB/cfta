import MicroCFTA.MergedAdaptiveEdges

/-!
# Adaptive grouping and ordinary-root construction

Every child and column comparison uses the state returned by the previous
request. The group threshold and final parent constructor match the finite
physical group worker, with no fixed child computation across states.
-/
namespace MicroCFTA.MergedAdaptiveGroups
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalLanguage MergedPhysicalMergeContext MergedPhysicalUnion
open MergedPhysicalGroupCalls MergedPhysicalGroupEdges MergedOrdinaryHeight
open MergedAdaptiveEffects MergedAdaptiveEdges Language

/-- Completed row processing retains actual records and covers every original row. -/
structure RowsResult [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (inputs values : List (EdgeValue Symbol Guard)) : Prop where
  extension : Extension before after outputs
  resident : Edges after values
  covers : ∀ original ∈ inputs, ∀ term, EdgeAccepts before meaning original term →
    ∃ edge ∈ values, EdgeAccepts after meaning edge term

/-- Return a completed source edge as the single row of its branch. -/
def singleton (action : Action Symbol Guard (EdgeValue Symbol Guard)) : Action Symbol Guard (List (EdgeValue Symbol Guard)) :=
  MergedAdaptiveEffects.bind action (fun edge => pure [edge])

/-- Sequence row-producing requests and concatenate their actual returned rows. -/
def sequence (call : Request → Action Symbol Guard (List (EdgeValue Symbol Guard))) :
    List Request → Action Symbol Guard (List (EdgeValue Symbol Guard))
  | [] => pure []
  | first :: rest => MergedAdaptiveEffects.bind (call first) fun edges =>
      MergedAdaptiveEffects.bind (sequence call rest) fun later => pure (edges ++ later)

/-- Adjacent adaptive row actions compose with language transport through their actual caches. -/
theorem sequence_complete [DecidableEq (EdgeKey Symbol Guard)]
    (call : Request → Action Symbol Guard (List (EdgeValue Symbol Guard)))
    (operands : Request → List (EdgeValue Symbol Guard)) (requests : List Request)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (complete : ∀ request ∈ requests, ∀ state, Context state outputs → Edges state (operands request) →
      ∃ values after, call request state = some (values, after) ∧ RowsResult state after outputs meaning (operands request) values)
    (state : State Symbol Guard) (context : Context state outputs) (resident : Edges state (requests.flatMap operands)) :
    ∃ values after, sequence call requests state = some (values, after) ∧
      RowsResult state after outputs meaning (requests.flatMap operands) values := by
  induction requests generalizing state with
  | nil => exact ⟨[], state, rfl, ⟨.refl state outputs context, by simp [Edges], by simp⟩⟩
  | cons first rest ih =>
      obtain ⟨head, middle, firstDone, firstChecked⟩ := complete first List.mem_cons_self state context
        (fun edge member => resident edge (by simp [member]))
      obtain ⟨tail, after, restDone, restChecked⟩ := ih
        (fun request member => complete request (List.mem_cons_of_mem _ member)) middle firstChecked.extension.context
        (fun edge member => edge_grows state middle firstChecked.extension.growth edge (resident edge (by simp [member])))
      refine ⟨head ++ tail, after, ?_, ⟨firstChecked.extension.trans restChecked.extension, ?_, ?_⟩⟩
      · simp only [sequence, MergedAdaptiveEffects.bind, firstDone, restDone, Option.bind_some, MergedAdaptiveEffects.pure]
      · intro edge member
        rcases List.mem_append.mp member with member | member
        · exact edge_grows middle after restChecked.extension.growth edge (firstChecked.resident edge member)
        · exact restChecked.resident edge member
      · intro original member term accepted
        rcases List.mem_append.mp member with member | member
        · obtain ⟨edge, included, accepted⟩ := firstChecked.covers original member term accepted
          exact ⟨edge, List.mem_append_left _ included,
            edge_grow middle after outputs firstChecked.extension.context restChecked.extension.growth meaning edge
              (firstChecked.resident edge included) term accepted⟩
        · obtain ⟨edge, included, accepted⟩ := restChecked.covers original member term
            (edge_grow state middle outputs context firstChecked.extension.growth meaning original
              (resident original (List.mem_append_right _ member)) term accepted)
          exact ⟨edge, List.mem_append_right _ included, accepted⟩

/-- The one-row action has the same completion and coverage as its actual edge computation. -/
theorem singleton_complete [DecidableEq (EdgeKey Symbol Guard)]
    (action : Action Symbol Guard (EdgeValue Symbol Guard)) (state after : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (inputs : List (EdgeValue Symbol Guard)) (edge : EdgeValue Symbol Guard)
    (done : action state = some (edge, after)) (checked : EdgeResult state after outputs meaning inputs edge) :
    singleton action state = some ([edge], after) ∧ RowsResult state after outputs meaning inputs [edge] := by
  refine ⟨by simp only [singleton, MergedAdaptiveEffects.bind, done, Option.bind_some, MergedAdaptiveEffects.pure],
    ⟨checked.extension, ?_, ?_⟩⟩
  · intro value member
    rw [List.mem_singleton.mp member]
    exact checked.resident
  · intro original member term accepted
    exact ⟨edge, List.mem_cons_self, checked.covers original member term accepted⟩

noncomputable section
local instance : DecidableEq (Value Symbol Guard) := Classical.typeDecidableEq _

/-- Execute the current source's four-row threshold at the actual group-call state. -/
def group [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) : Action Symbol Guard (List (EdgeValue Symbol Guard)) :=
  if edges.length ≤ 4 then sequence (fun edge => singleton (small recurse edge)) edges
  else match edges with
  | [] => pure []
  | first :: rest => singleton (large recurse outputs meaning unconstrained top first rest)

/-- Both adaptive threshold branches complete using only smaller recursive merge calls. -/
theorem group_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Context state outputs → Available state value →
      ∃ result after, recurse value state = some (result, after) ∧ Result state after outputs meaning [value] result)
    (edges : List (EdgeValue Symbol Guard))
    (closed : ∀ edge ∈ edges, ∀ value ∈ edge.children, value.free = [])
    (bounded : ∀ edge ∈ edges, ∀ value ∈ edge.children, height value ≤ limit)
    (keys : SameKey edges) (state : State Symbol Guard) (context : Context state outputs) (resident : Edges state edges) :
    ∃ result after, group recurse outputs meaning unconstrained top edges state = some (result, after) ∧
      RowsResult state after outputs meaning edges result := by
  by_cases smallGroup : edges.length ≤ 4
  · have complete : ∀ edge ∈ edges, ∀ state, Context state outputs → Edges state [edge] →
        ∃ values after, singleton (small recurse edge) state = some (values, after) ∧ RowsResult state after outputs meaning [edge] values := by
      intro edge member state context resident
      obtain ⟨value, after, done, checked⟩ := small_complete recurse limit outputs meaning smaller edge (bounded edge member)
        state context (resident edge List.mem_cons_self)
      exact ⟨[value], after, singleton_complete _ state after outputs meaning [edge] value done checked⟩
    obtain ⟨values, after, done, checked⟩ := sequence_complete (fun edge => singleton (small recurse edge)) (fun edge => [edge]) edges
      outputs meaning complete state context (by simpa using resident)
    refine ⟨values, after, ?_, ?_⟩
    · simpa only [group, smallGroup, ↓reduceIte] using done
    · simpa using checked
  · cases edges with
    | nil => simp at smallGroup
    | cons first rest =>
        obtain ⟨value, after, done, checked⟩ := large_complete recurse limit outputs meaning unconstrained clear top topTrue smaller
          first rest closed bounded keys state context resident
        have single := singleton_complete _ state after outputs meaning (first :: rest) value done checked
        exact ⟨[value], after, by simpa only [group, smallGroup, ↓reduceIte] using single.1, single.2⟩

/-- Complete every group before interning the final ordinary source root. -/
def root [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool) (top : Guard)
    (groups : List (List (EdgeValue Symbol Guard))) : Action Symbol Guard (Value Symbol Guard) :=
  MergedAdaptiveEffects.bind (sequence (group recurse outputs meaning unconstrained top) groups) fun edges => work (makeNode edges)

/-- An adaptive root completes and covers the original node, assuming only smaller recursive calls. -/
theorem root_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Context state outputs → Available state value →
      ∃ result after, recurse value state = some (result, after) ∧ Result state after outputs meaning [value] result)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat)
    (groups : List (List (EdgeValue Symbol Guard))) (grouping : MergedPhysicalGroupRoot.Grouping edges groups)
    (heightBound : height (.node entry edges depth []) ≤ limit + 1)
    (state : State Symbol Guard) (context : Context state outputs) (available : Available state (.node entry edges depth [])) :
    ∃ result after, root recurse outputs meaning unconstrained top groups state = some (result, after) ∧
      Result state after outputs meaning [.node entry edges depth []] result := by
  have original : ∀ group ∈ groups, ∀ edge ∈ group, edge ∈ edges := by
    intro group member edge included
    exact grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  have resident : Edges state (groups.flatMap id) := fun edge member =>
    resident_edges state context.facts.linked _ available.resident edge (grouping.partition.mem_iff.mp (by simpa using member))
  have closedOriginal := fun edge included value inner =>
    closed_child state context.facts.coherent entry edges depth [] available.resident rfl edge included value inner
  obtain ⟨merged, middle, groupsDone, checked⟩ := sequence_complete (group recurse outputs meaning unconstrained top) id groups outputs meaning
    (fun group member state context resident => group_complete recurse limit outputs meaning unconstrained clear top topTrue smaller group
      (fun edge included value inner => closedOriginal edge (original group member edge included) value inner)
      (fun edge included value inner => by
        have less := child_lt entry edges depth [] edge (original group member edge included) value inner
        omega)
      (grouping.keys edges groups group member) state context resident)
    state context resident
  let result := run (makeNode merged) middle
  have built := checked.extension.context.makeNode middle outputs merged checked.resident
  have extension := Extension.work (makeNode merged) middle outputs checked.extension.context built.1
  refine ⟨result.1, result.2, ?_, ⟨checked.extension.trans extension, built.2, ?_⟩⟩
  · simp only [root, MergedAdaptiveEffects.bind, groupsDone, Option.bind_some, work]; rfl
  · intro source member term accepted
    rw [List.mem_singleton.mp member] at accepted
    obtain ⟨original, included, accepted⟩ := (node_exact state meaning entry edges depth [] term).mp accepted
    obtain ⟨edge, included, accepted⟩ := checked.covers original (by simpa using grouping.partition.mem_iff.mpr included) term accepted
    exact (makeNode_exact middle result.2 checked.extension.context.facts merged checked.resident meaning term).mpr
      ⟨edge, included, edge_grow middle result.2 outputs checked.extension.context extension.growth meaning edge (checked.resident edge included) term accepted⟩

end
end MicroCFTA.MergedAdaptiveGroups
