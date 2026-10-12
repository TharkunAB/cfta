import MicroCFTA.EnumerationBinderExposure
import MicroCFTA.EpsilonUnion
import MicroCFTA.SymbolicSelection

/-!
# Finite closure from lexical binder syntax

Each non-reference lexical occurrence has one instance under its closed
ancestor environment. A reference returns an existing ancestor instance.
The inventory is finite because its construction descends only into the
original syntax. Self-unfolding introduces no new inventory member.
-/
namespace MicroCFTA.LexicalBinderClosure
open Binding BinderLanguage EnumerationBinderExposure

/-- Every stored substitution value is closed. -/
def ClosedEnvironment (environment : Environment Item) : Prop :=
  ∀ name value, environment name = some value → free value = []

/-- Every free reference of the current lexical shape has an ancestor binding. -/
def Resolved (environment : Environment Item) (shape : Shape Item) : Prop :=
  ∀ name ∈ free shape, ∃ value, environment name = some value

/-- Close one binder reference with its already constructed finite instance. -/
def extend (environment : Environment Item) (name : Nat) (value : Shape Item) : Environment Item :=
  fun other => if other = name then some value else environment other

/-- Masking a binder does not change the closedness of stored values. -/
theorem mask_closed (environment : Environment Item) (name : Nat) (closed : ClosedEnvironment environment) :
    ClosedEnvironment (mask environment name) := by
  intro other value found
  by_cases same : other = name
  · simp [mask, same] at found
  · exact closed other value (by simpa [mask, same] using found)

/-- The shape instance is closed once every free name has a closed binding. -/
theorem instance_closed (environment : Environment Item) (shape : Shape Item)
    (closed : ClosedEnvironment environment) (resolved : Resolved environment shape) :
    free (substitute environment shape) = [] := by
  apply substitute_closed
  intro name member
  obtain ⟨value, found⟩ := resolved name member
  exact ⟨value, found, closed name value found⟩

/-- A later substitution leaves all previously inserted closed values unchanged. -/
theorem substitute_compose (shape : Shape Item) (first later : Environment Item)
    (closed : ClosedEnvironment first) :
    substitute later (substitute first shape) =
      substitute (fun name => (first name).or (later name)) shape := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ first later : Environment Item, ClosedEnvironment first →
      substituteList later (substituteList first shapes) =
        substituteList (fun name => (first name).or (later name)) shapes)
    generalizing first later with
  | empty => rfl
  | ref name =>
      cases found : first name with
      | none => simp [substitute, found]
      | some value => simp [substitute, found, closed_unchanged value (closed name value found)]
  | branch payload children ih => simp only [substitute, ih first later closed]
  | alternatives parts ih => simp only [substitute, ih first later closed]
  | binder name body ih =>
      simp only [substitute, ih _ _ (mask_closed first name closed)]
      have same : (fun other => (mask first name other).or (mask later name other)) =
          mask (fun other => (first other).or (later other)) name := by
        funext other
        by_cases hit : other = name <;> simp [mask, hit]
      rw [same]
  | nil => rfl
  | cons firstShape rest ih ir =>
      rename_i first later closed
      simp only [substituteList, ih first later closed, ir first later closed]

/-- Self-substitution of the closed lexical binder enters its body under the extended environment. -/
theorem unfold_instance (environment : Environment (Payload Symbol)) (name : Nat)
    (body : Shape (Payload Symbol)) (closed : ClosedEnvironment environment) :
    unfold name (substitute (mask environment name) body) =
      substitute (extend environment name (substitute environment (.binder name body))) body := by
  rw [unfold, prepare_correct, substitute_compose body _ _ (mask_closed environment name closed)]
  congr 1
  funext other
  by_cases hit : other = name
  · simp [mask, single, extend, hit, substitute]
  · cases found : environment other <;> simp [mask, single, extend, hit, found]

mutual
/-- Construct one instance of every non-reference lexical occurrence. -/
def inventory (environment : Environment Item) : Shape Item → List (Shape Item)
  | .ref _ => []
  | .empty => [.empty]
  | .branch payload children => substitute environment (.branch payload children) :: forest environment children
  | .alternatives parts => substitute environment (.alternatives parts) :: forest environment parts
  | .binder name body =>
      let closedBinder := substitute environment (.binder name body)
      closedBinder :: inventory (extend environment name closedBinder) body

/-- Concatenate the inventories of the original ordered lexical children. -/
def forest (environment : Environment Item) : List (Shape Item) → List (Shape Item)
  | [] => []
  | first :: rest => inventory environment first ++ forest environment rest
end

/-- Inventory size depends only on the finite lexical syntax, never on substituted ancestor sizes. -/
theorem inventory_length (shape : Shape Item) (left right : Environment Item) :
    (inventory left shape).length = (inventory right shape).length := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ left right : Environment Item,
      (forest left shapes).length = (forest right shapes).length)
    generalizing left right with
  | empty | ref => rfl
  | branch payload children ih => simp only [inventory, List.length_cons, ih left right]
  | alternatives parts ih => simp only [inventory, List.length_cons, ih left right]
  | binder name body ih =>
      simp only [inventory, List.length_cons]
      exact congrArg (· + 1) (ih _ _)
  | nil => rfl
  | cons first rest ih ir =>
      rename_i left right
      simp only [forest, List.length_append, ih left right, ir left right]

/-- A lexical root is in its local inventory or equals one previously bound ancestor. -/
theorem root_covered (environment : Environment Item) (shape : Shape Item)
    (resolved : Resolved environment shape) :
    substitute environment shape ∈ inventory environment shape ∨
      ∃ name, environment name = some (substitute environment shape) := by
  cases shape with
  | ref name =>
      obtain ⟨value, found⟩ := resolved name (by simp [free])
      right
      exact ⟨name, by simp [substitute, found]⟩
  | empty | branch | alternatives | binder => left; simp [inventory, substitute]

/-- Every forest inventory entry belongs to a lexical child inventory. -/
theorem forest_member (environment : Environment Item) (shapes : List (Shape Item)) (value : Shape Item) :
    value ∈ forest environment shapes ↔ ∃ shape ∈ shapes, value ∈ inventory environment shape := by
  induction shapes with
  | nil => simp [forest]
  | cons first rest ih =>
      simp only [forest, List.mem_append, ih, List.mem_cons]
      constructor
      · rintro (member | ⟨shape, member, present⟩)
        · exact ⟨first, Or.inl rfl, member⟩
        · exact ⟨shape, Or.inr member, present⟩
      · rintro ⟨shape, (same | member), present⟩
        · subst shape; exact Or.inl present
        · exact Or.inr ⟨shape, member, present⟩

/-- Extend a closed ancestor environment by the current closed binder. -/
theorem extend_closed (environment : Environment Item) (name : Nat) (value : Shape Item)
    (closed : ClosedEnvironment environment) (valueClosed : free value = []) :
    ClosedEnvironment (extend environment name value) := by
  intro other target found
  by_cases hit : other = name
  · have same : target = value := by simpa [extend, hit] using found.symm
    simpa [same] using valueClosed
  · exact closed other target (by simpa [extend, hit] using found)

/-- A closed outer binder resolves all references in its body after extension. -/
theorem body_resolved (environment : Environment Item) (name : Nat) (body : Shape Item)
    (resolved : Resolved environment (.binder name body)) :
    Resolved (extend environment name value) body := by
  intro other member
  by_cases hit : other = name
  · exact ⟨value, by simp [extend, hit]⟩
  · obtain ⟨replacement, found⟩ := resolved other (by simp [free, member, hit])
    exact ⟨replacement, by simp [extend, hit, found]⟩

/-- A reference obtained from the extended environment returns the current binder or an older ancestor. -/
theorem extend_range (environment : Environment Item) (name : Nat) (value target : Shape Item)
    (member : ∃ reference, extend environment name value reference = some target) :
    target = value ∨ ∃ reference, environment reference = some target := by
  obtain ⟨reference, found⟩ := member
  by_cases hit : reference = name
  · left; simpa [extend, hit] using found.symm
  · exact Or.inr ⟨reference, by simpa [extend, hit] using found⟩

/-- Resolving a forest resolves every selected lexical child. -/
theorem resolved_member (environment : Environment Item) (shapes : List (Shape Item))
    (resolved : ∀ name ∈ freeList shapes, ∃ value, environment name = some value)
    (shape : Shape Item) (member : shape ∈ shapes) : Resolved environment shape := by
  intro name present
  exact resolved name (freeList_member shapes shape member name present)

/-- Every primitive request from an inventory member returns a local instance or an older ancestor. -/
theorem inventory_step (environment : Environment (Payload Symbol)) (shape : Shape (Payload Symbol))
    (closed : ClosedEnvironment environment) (resolved : Resolved environment shape)
    (before : Shape (Payload Symbol)) (member : before ∈ inventory environment shape)
    (after : Shape (Payload Symbol)) (step : RequestStep before after) :
    after ∈ inventory environment shape ∨ ∃ name, environment name = some after := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ environment : Environment (Payload Symbol), ClosedEnvironment environment →
      (∀ shape ∈ shapes, Resolved environment shape) →
      ∀ before, before ∈ forest environment shapes → ∀ after, RequestStep before after →
        after ∈ forest environment shapes ∨ ∃ name, environment name = some after)
    generalizing environment before after with
  | ref => simp [inventory] at member
  | empty =>
      have same : before = .empty := by simpa [inventory] using member
      subst before
      cases step
  | branch payload children ih =>
      rcases List.mem_cons.mp member with same | member
      · subst before
        cases step with
        | child _ _ selected childMember =>
            have mapped : after ∈ children.map (substitute environment) := by
              simpa [substituteList_map] using childMember
            obtain ⟨original, present, equal⟩ := List.mem_map.mp mapped
            rw [← equal]
            rcases root_covered environment original (resolved_member environment children resolved original present) with here | older
            · left
              exact List.mem_cons_of_mem _ ((forest_member environment children _).mpr ⟨original, present, here⟩)
            · exact Or.inr older
      · rcases ih environment closed (resolved_member environment children resolved) before member after step with here | older
        · exact Or.inl (List.mem_cons_of_mem _ here)
        · exact Or.inr older
  | alternatives parts ih =>
      rcases List.mem_cons.mp member with same | member
      · subst before
        cases step with
        | alternative _ selected childMember =>
            have mapped : after ∈ parts.map (substitute environment) := by
              simpa [substituteList_map] using childMember
            obtain ⟨original, present, equal⟩ := List.mem_map.mp mapped
            rw [← equal]
            rcases root_covered environment original (resolved_member environment parts resolved original present) with here | older
            · left
              exact List.mem_cons_of_mem _ ((forest_member environment parts _).mpr ⟨original, present, here⟩)
            · exact Or.inr older
      · rcases ih environment closed (resolved_member environment parts resolved) before member after step with here | older
        · exact Or.inl (List.mem_cons_of_mem _ here)
        · exact Or.inr older
  | binder name body ih =>
      let value := substitute environment (.binder name body)
      have bodyResolved : Resolved (extend environment name value) body := body_resolved environment name body resolved
      have move : ∀ target,
          (target ∈ inventory (extend environment name value) body ∨
            ∃ reference, extend environment name value reference = some target) →
          target ∈ inventory environment (.binder name body) ∨ ∃ reference, environment reference = some target := by
        intro target member
        rcases member with here | older
        · exact Or.inl (List.mem_cons_of_mem _ here)
        · rcases extend_range environment name value target older with same | old
          · exact Or.inl (List.mem_cons.mpr (Or.inl same))
          · exact Or.inr old
      rcases List.mem_cons.mp member with same | member
      · subst before
        cases step with
        | unfold _ _ =>
            rw [unfold_instance environment name body closed]
            exact move _ (root_covered _ body bodyResolved)
      · exact move _ (ih _ (extend_closed environment name value closed
          (instance_closed environment (.binder name body) closed resolved)) bodyResolved before member after step)
  | nil =>
      rename_i environment closed resolved before member after step
      simp [forest] at member
  | cons first rest ih ir =>
      rename_i environment closed resolved before member after step
      rcases List.mem_append.mp member with here | there
      · rcases ih environment closed (resolved first (by simp)) before here after step with localMember | older
        · exact Or.inl (List.mem_append_left _ localMember)
        · exact Or.inr older
      · rcases ir environment closed (fun child present => resolved child (by simp [present])) before there after step with localMember | older
        · exact Or.inl (List.mem_append_right _ localMember)
        · exact Or.inr older

/-- A closed lexical root has a concrete finite list containing every primitive reachable shape. -/
theorem reachable_inventory (root : Shape (Payload Symbol)) (closed : free root = [])
    (target : Shape (Payload Symbol)) (reached : Reachable root target) :
    target ∈ inventory (fun _ => none) root := by
  have environmentClosed : ClosedEnvironment (fun _ => none : Environment (Payload Symbol)) := by
    intro name value found
    cases found
  have resolved : Resolved (fun _ => none : Environment (Payload Symbol)) root := by
    intro name member
    simp [closed] at member
  induction reached with
  | root =>
      have covered := root_covered (fun _ => none) root resolved
      simpa [substitute_empty] using covered
  | step _ step ih =>
      have covered := inventory_step (fun _ => none) root environmentClosed resolved _ ih _ step
      simpa using covered

/-- Finiteness of the request domain is derived from lexical syntax, not supplied as a premise. -/
theorem finite_request_domain (root : Shape (Payload Symbol)) (closed : free root = []) :
    ∃ states : List (Shape (Payload Symbol)), root ∈ states ∧
      (∀ state ∈ states, ∀ target, RequestStep state target → target ∈ states) ∧
      ∀ target, Reachable root target → target ∈ states := by
  refine ⟨inventory (fun _ => none) root, reachable_inventory root closed root .root, ?_,
    reachable_inventory root closed⟩
  intro state member target step
  have environmentClosed : ClosedEnvironment (fun _ => none : Environment (Payload Symbol)) := by
    intro name value found
    cases found
  have resolved : Resolved (fun _ => none : Environment (Payload Symbol)) root := by
    intro name member
    simp [closed] at member
  simpa using inventory_step (fun _ => none) root environmentClosed resolved state member target step

/-- Constructor exposure follows only binders and union alternatives. -/
def epsilonSuccessors : Shape (Payload Symbol) → List (Shape (Payload Symbol))
  | .binder name body => [unfold name body]
  | .alternatives parts => parts
  | _ => []

/-- Every epsilon successor is one of the source's primitive requests. -/
theorem epsilon_request (before after : Shape (Payload Symbol))
    (member : after ∈ epsilonSuccessors before) : RequestStep before after := by
  cases before with
  | empty | ref | branch => simp [epsilonSuccessors] at member
  | alternatives parts => exact .alternative parts after member
  | binder name body =>
      have same : after = unfold name body := by simpa [epsilonSuccessors] using member
      subst after
      exact .unfold name body

/-- Epsilon reachability is a restricted sequence of the already covered primitive requests. -/
theorem epsilon_reachable (root target : Shape (Payload Symbol))
    (reached : Productivity.Reachable epsilonSuccessors [root] target) : Reachable root target := by
  induction reached with
  | @seed state member =>
      have same : state = root := by simpa using member
      subst state
      exact .root
  | step previous member ih => exact .step ih (epsilon_request _ _ member)

/-- Visited epsilon closure uses the finite inventory derived from the lexical input. -/
def visited [DecidableEq (Shape (Payload Symbol))] (root : Shape (Payload Symbol)) :
    List (Shape (Payload Symbol)) :=
  EpsilonUnion.visit epsilonSuccessors (inventory (fun _ => none) root).eraseDups [root]

/-- The visited worker terminates with precisely the epsilon-reachable lexical instances. -/
theorem visited_exact [DecidableEq (Shape (Payload Symbol))]
    (root : Shape (Payload Symbol)) (closed : free root = []) (target : Shape (Payload Symbol)) :
    target ∈ visited root ↔ Productivity.Reachable epsilonSuccessors [root] target := by
  have spec := EpsilonUnion.visit_spec epsilonSuccessors
    (inventory (fun _ => none) root).eraseDups [root] (SymbolicDriver.eraseDups_nodup _)
  have covered : ∀ target, Productivity.Reachable epsilonSuccessors [root] target →
      target ∈ (inventory (fun _ => none) root).eraseDups := by
    intro target reached
    exact List.mem_eraseDups.mpr (reachable_inventory root closed target (epsilon_reachable root target reached))
  constructor
  · exact spec.reachable target
  · intro reached
    induction reached with
    | seed member =>
        exact (spec.requested _ member).resolve_left (fun absent => absent (covered _ (.seed member)))
    | step previous member ih =>
        exact (spec.closed _ ih _ member).resolve_left (fun absent => absent (covered _ (.step previous member)))

/-- The finite worker visits each lexical instance at most once. -/
theorem visited_distinct [DecidableEq (Shape (Payload Symbol))] (root : Shape (Payload Symbol)) :
    (visited root).Nodup :=
  (EpsilonUnion.visit_spec epsilonSuccessors (inventory (fun _ => none) root).eraseDups [root]
    (SymbolicDriver.eraseDups_nodup _)).distinct

/-- Read constructor rows without consuming child depth or changing payloads. -/
def constructorRows : Shape (Payload Symbol) → List (EnumerationBinderExposure.Row Symbol)
  | .branch payload children => [(payload, children)]
  | _ => []

/-- Collect all constructor rows after the finite visited epsilon closure. -/
def exposedRows [DecidableEq (Shape (Payload Symbol))] (root : Shape (Payload Symbol)) :
    List (EnumerationBinderExposure.Row Symbol) := (visited root).flatMap constructorRows

/-- The concrete closure emits exactly the rows at epsilon-reachable constructor instances. -/
theorem exposed_rows_exact [DecidableEq (Shape (Payload Symbol))]
    (root : Shape (Payload Symbol)) (closed : free root = []) (row : EnumerationBinderExposure.Row Symbol) :
    row ∈ exposedRows root ↔ ∃ shape, Productivity.Reachable epsilonSuccessors [root] shape ∧
      row ∈ constructorRows shape := by
  simp only [exposedRows, List.mem_flatMap, visited_exact root closed]

/-- Every emitted constructor retains closed child instances in the same finite inventory. -/
theorem exposed_child_in_inventory [DecidableEq (Shape (Payload Symbol))]
    (root : Shape (Payload Symbol)) (closed : free root = [])
    (row : EnumerationBinderExposure.Row Symbol) (member : row ∈ exposedRows root)
    (child : Shape (Payload Symbol)) (childMember : child ∈ row.2) :
    child ∈ inventory (fun _ => none) root ∧ free child = [] := by
  obtain ⟨shape, reached, rowMember⟩ := (exposed_rows_exact root closed row).mp member
  have reachable := epsilon_reachable root shape reached
  cases shape with
  | empty | ref | alternatives | binder => simp [constructorRows] at rowMember
  | branch payload children =>
      have same : row = (payload, children) := by simpa [constructorRows] using rowMember
      subst row
      have requested := Reachable.step reachable (.child payload children child childMember)
      exact ⟨reachable_inventory root closed child requested, reachable_closed closed requested⟩

/-- A retained self binder has one lexical instance despite infinitely many possible unfold requests. -/
theorem self_inventory (name : Nat) :
    inventory (fun _ => none) (.binder name (.ref name) : Shape (Payload Symbol)) =
      [.binder name (.ref name)] := by simp [inventory, substitute, mask]

/-- Visited epsilon closure exposes no constructor for the retained empty self-cycle. -/
theorem self_rows [DecidableEq (Shape (Payload Symbol))] (name : Nat) :
    exposedRows (.binder name (.ref name) : Shape (Payload Symbol)) = [] := by
  let root : Shape (Payload Symbol) := .binder name (.ref name)
  have next : epsilonSuccessors root = [root] := by
    simp [root, epsilonSuccessors, unfold, prepare, free, single, substitute]
  simp only [exposedRows, visited, self_inventory, List.eraseDups_cons, List.filter_nil, List.eraseDups_nil]
  change (EpsilonUnion.visit epsilonSuccessors [root] [root]).flatMap constructorRows = []
  rw [EpsilonUnion.visit]
  simp only [List.mem_singleton, ↓reduceDIte, List.erase_cons_head, next, List.append_nil]
  rw [EpsilonUnion.visit]
  simp only [List.not_mem_nil, ↓reduceDIte]
  rw [EpsilonUnion.visit]
  rfl

/-- Any fixed identity representation has a concrete finite image of all requested instances. -/
theorem finite_identity_image (root : Shape (Payload Symbol)) (closed : free root = [])
    (identity : Shape (Payload Symbol) → Identity) :
    ∃ identities : List Identity, ∀ target, Reachable root target → identity target ∈ identities := by
  refine ⟨(inventory (fun _ => none) root).map identity, ?_⟩
  intro target reached
  exact List.mem_map.mpr ⟨target, reachable_inventory root closed target reached, rfl⟩

end MicroCFTA.LexicalBinderClosure
