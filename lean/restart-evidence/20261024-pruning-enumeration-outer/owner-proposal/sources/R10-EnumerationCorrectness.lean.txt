import MicroCFTA.EnumerationState

/-!
# Concrete suspended-enumeration step invariants

The operations in this module are the executable `EnumerationState` actions.
Complete assignments interpret holes. Stored node restrictions and residual
guards remain explicit. Diagnostic recursion truncation is not acceptance.
-/

namespace MicroCFTA.EnumerationCorrectness

open Language Fragments EnumerationState

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

/-- A successful branch of an actual state action. Errors remain separate list entries. -/
def Success (action : EnumerateM Symbol Guard α) (before : State Symbol Guard)
    (value : α) (after : State Symbol Guard) : Prop :=
  Except.ok (value, after) ∈ ExceptT.run (action before)

/-- Binding runs each successful branch in its own stored state and retains error branches. -/
theorem run_bind (action : EnumerateM Symbol Guard α) (next : α → EnumerateM Symbol Guard β)
    (state : State Symbol Guard) :
    ExceptT.run ((action >>= next) state) = (ExceptT.run (action state)).flatMap
      (fun result => match result with
        | .error error => [.error error]
        | .ok (value, after) => ExceptT.run (next value after)) := by
  simp only [bind, StateT.bind, ExceptT.run, ExceptT.bind, ExceptT.mk]
  congr 1
  funext result
  cases result with
  | error error => rfl
  | ok pair => cases pair; rfl

/-- Successful sequential execution is exactly composition through one successful intermediate state. -/
theorem success_bind (action : EnumerateM Symbol Guard α) (next : α → EnumerateM Symbol Guard β)
    (before : State Symbol Guard) (value : β) (after : State Symbol Guard) :
    Success (action >>= next) before value after ↔
      ∃ middle intermediate, Success action before middle intermediate ∧ Success (next middle) intermediate value after := by
  simp only [Success, run_bind, List.mem_flatMap]
  constructor
  · rintro ⟨result, member, continued⟩
    cases result with
    | error error => simp at continued
    | ok pair => exact ⟨pair.1, pair.2, member, continued⟩
  · rintro ⟨middle, intermediate, member, continued⟩
    exact ⟨.ok (middle, intermediate), member, continued⟩

/-- A deterministic first step supplies exactly its returned state to the next step. -/
theorem bind_single (action : EnumerateM Symbol Guard α) (next : α → EnumerateM Symbol Guard β)
    (before after : State Symbol Guard) (value : α)
    (result : action before = [.ok (value, after)]) :
    (action >>= next) before = next value after := by
  change ExceptT.run ((action >>= next) before) = ExceptT.run (next value after)
  rw [run_bind]
  change (action before : List (Except Error (α × State Symbol Guard))).flatMap _ = _
  rw [result]
  simp

/-- Stored graph references denote their complete term languages. -/
abbrev NodeLanguage (Symbol : Type) := Nat → Term Symbol → Prop

/-- One source equality class requires a common existing subtree at every represented path. -/
def EqualityHolds (term : Term Symbol) (trie : EqualityTrie.Trie) : Prop :=
  ∃ common, ∀ path ∈ EqualityTrie.fromPathTrie trie, term.atPath path = some common

/-- An absent residual imposes no predicate; a present residual applies at this term. -/
def ResidualHolds (meaning : Guard → Term Symbol → Prop) (residual : Option Guard) (term : Term Symbol) : Prop :=
  match residual with
  | none => True
  | some guard => meaning guard term

/-- Finite-run denotation of the actual node view consumed by the state driver. -/
inductive Accepted (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop) :
    Nat → Term Symbol → Prop where
  | edge (node : Nat) (edges : List (EnumerationState.Edge Symbol Guard))
      (edge : EnumerationState.Edge Symbol Guard) (children : List (Term Symbol)) :
      graph.node node = .alternatives edges → edge ∈ edges →
      All₂ (Accepted graph meaning) edge.children children →
      (∀ equality ∈ edge.equalities, EqualityHolds (.node edge.symbol children) equality) →
      ResidualHolds meaning edge.residual (.node edge.symbol children) →
      Accepted graph meaning node (.node edge.symbol children)
  | recursive (node body : Nat) (term : Term Symbol) :
      graph.node node = .recursive body → Accepted graph meaning body term → Accepted graph meaning node term

/-- A structurally empty graph node has no finite accepting run. -/
theorem accepted_empty (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (node : Nat) (term : Term Symbol) (empty : graph.node node = .empty) : ¬Accepted graph meaning node term := by
  intro accepted
  cases accepted <;> simp_all

/-- Recursive graph views retain finite-run semantics through their exposed body. -/
theorem accepted_recursive (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (node body : Nat) (term : Term Symbol) (recursive : graph.node node = .recursive body) :
    Accepted graph meaning node term ↔ Accepted graph meaning body term := by
  constructor
  · intro accepted
    cases accepted with
    | edge _ _ _ _ alternative _ _ _ _ => simp [recursive] at alternative
    | recursive _ actual _ unfolded inside =>
        have same : actual = body := by simpa [recursive] using unfolded.symm
        simpa [same] using inside
  · exact Accepted.recursive node body term recursive

/-- Interpret one concrete source slot as the previously verified fragment-domain slot. -/
def slot (language : NodeLanguage Symbol) : UVarValue Symbol → Slot Symbol
  | .unenumerated node scs =>
      .pending (node.map language) (scs.map fun sc => fun assignment term => Suspended.Holds assignment term sc)
  | .enumerated fragment => .expanded fragment
  | .eliminated => .eliminated

/-- Missing array positions impose no term restriction; operations still report invalid accesses. -/
def heap (language : NodeLanguage Symbol) (values : List (UVarValue Symbol)) : Heap Symbol :=
  fun uv => slot language (values[uv]?.getD .eliminated)

/-- Retained residual guards apply to their completed guarded fragments. -/
def guardsHold (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (obligations : List (Guard × Fragment Symbol)) : Prop :=
  ∀ obligation ∈ obligations, meaning obligation.1 (fill assignment obligation.2)

/-- A complete assignment satisfies all forest equalities, stored slots, and retained guards. -/
def Satisfies (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (state : State Symbol Guard) : Prop :=
  Fragments.stateSatisfies state.representatives (heap language state.values) assignment ∧
    guardsHold meaning assignment state.obligations

/-- An empty slot array imposes no restriction. -/
theorem heap_empty (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) :
    heapSatisfies (heap language []) assignment := by
  intro uv
  simp [heap, slot, slotSatisfies]

/-- The slot array and allocator identify the same finite domain. -/
def SupplyAligned (state : State Symbol Guard) : Prop := state.counter = state.values.length

/-- A successful representative lookup has exactly the source state update. -/
theorem representative_exact (fuel uv : Nat) (state : State Symbol Guard) (found : UnionFind.Result)
    (result : UnionFind.findRoot fuel state.representatives uv = some found) :
    representative fuel uv state = [.ok (found.representative, {state with representatives := found.forest})] := by
  simp [representative, result, bind, get, getThe, MonadStateOf.get, set, pure,
    StateT.bind, StateT.pure, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk]

/-- The actual representative action preserves exactly every complete assignment. -/
theorem representative_semantics (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel uv : Nat) (state : State Symbol Guard) (found : UnionFind.Result)
    (valid : UnionFind.Total state.representatives)
    (result : UnionFind.findRoot fuel state.representatives uv = some found) :
    Satisfies language meaning assignment {state with representatives := found.forest} ↔
      Satisfies language meaning assignment state := by
  simp only [Satisfies, Fragments.stateSatisfies, UnionFind.findRoot_satisfies valid result]

/-- The actual union action has exactly one successful branch after its primitive succeeds. -/
theorem union_exact (fuel left right : Nat) (state : State Symbol Guard) (after : UnionFind.Forest)
    (result : UnionFind.union fuel fuel state.representatives left right = some after) :
    unionVariables fuel left right state = [.ok ((), {state with representatives := after})] := by
  simp [unionVariables, result, bind, get, getThe, MonadStateOf.get, set, pure,
    StateT.bind, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk]

/-- Union adds exactly the requested value equality and retains every slot and guard restriction. -/
theorem union_semantics (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel left right : Nat) (state : State Symbol Guard) (after : UnionFind.Forest)
    (valid : UnionFind.Total state.representatives)
    (result : UnionFind.union fuel fuel state.representatives left right = some after) :
    Satisfies language meaning assignment {state with representatives := after} ↔
      Satisfies language meaning assignment state ∧ assignment left = assignment right := by
  simp only [Satisfies, Fragments.stateSatisfies, UnionFind.union_satisfies valid result]
  grind

/-- Source slot writes update one in-range heap entry and no other entry. -/
theorem heap_set (language : NodeLanguage Symbol) (values : List (UVarValue Symbol))
    (uv : Nat) (value : UVarValue Symbol) (bound : uv < values.length) :
    heap language (values.set uv value) = Fragments.setSlot (heap language values) uv (slot language value) := by
  funext other
  by_cases same : other = uv
  · subst other
    simp [heap, Fragments.setSlot, bound]
  · simp [heap, Fragments.setSlot, same, Ne.symm same]

/-- Allocation retains all previous slots and constrains only the fresh appended variable. -/
theorem heap_append (language : NodeLanguage Symbol) (values : List (UVarValue Symbol))
    (assignment : Nat → Term Symbol) (value : UVarValue Symbol) :
    heapSatisfies (heap language (values ++ [value])) assignment ↔
      heapSatisfies (heap language values) assignment ∧ slotSatisfies assignment values.length (slot language value) := by
  constructor
  · intro after
    refine ⟨?_, ?_⟩
    · intro uv
      by_cases bound : uv < values.length
      · simpa [heap, List.getElem?_append, bound] using after uv
      · simp [heap, List.getElem?_eq_none (by omega : values.length ≤ uv), slot, slotSatisfies]
    · simpa [heap] using after values.length
  · rintro ⟨before, added⟩ uv
    by_cases bound : uv < values.length
    · simpa [heap, List.getElem?_append, bound] using before uv
    · by_cases same : uv = values.length
      · subst uv; simpa [heap] using added
      · have outside : (values ++ [value]).length ≤ uv := by simp; omega
        simp [heap, List.getElem?_eq_none outside, slot, slotSatisfies]

/-- Concrete allocation preserves exactly the old assignment restrictions and the new optional node restriction. -/
theorem allocation_semantics (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (node : Option Nat) (state : State Symbol Guard)
    (aligned : SupplyAligned state) :
    Satisfies language meaning assignment (allocated node state) ↔
      Satisfies language meaning assignment state ∧ permits (node.map language) (assignment state.counter) := by
  simp only [Satisfies, Fragments.stateSatisfies, allocated, heap_append, slot, slotSatisfies]
  simp only [List.map_nil, List.not_mem_nil, false_implies, implies_true, and_true]
  rw [← aligned]
  grind

/-- Suspended equality construction returns the exact new variable and a pure equality slot. -/
theorem suspend_exact (trie : EqualityTrie.Trie) (state : State Symbol Guard) :
    suspend trie state = [.ok (⟨trie, state.counter⟩, allocated none state)] := rfl

/-- Merely allocating a suspended equality variable does not discard a complete assignment. -/
theorem suspend_semantics (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (state : State Symbol Guard) (aligned : SupplyAligned state) :
    Satisfies language meaning assignment (allocated none state) ↔ Satisfies language meaning assignment state := by
  simpa [permits] using allocation_semantics language meaning assignment none state aligned

/-- The initial state denotes exactly the requested root language. -/
theorem initial_semantics (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (root : Nat) :
    Satisfies language meaning assignment (initial root) ↔ language root (assignment 0) := by
  have appended := heap_append language [] assignment (.unenumerated (some root) [])
  simp only [List.nil_append, List.length_nil] at appended
  simp [Satisfies, Fragments.stateSatisfies, initial, UnionFind.initial_satisfies, appended,
    heap_empty, slot, slotSatisfies, permits, guardsHold]

/-- The actual graph primitive must implement semantic intersection. This is not a state-transition premise. -/
def IntersectionCorrect (graph : Graph Symbol Guard) (language : NodeLanguage Symbol) : Prop :=
  ∀ left right term, language (graph.intersect left right) term ↔ language left term ∧ language right term

/-- The concrete intersection of pending source slots matches the proved abstract intersection exactly. -/
theorem slot_intersection (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (correct : IntersectionCorrect graph language) (left right merged : UVarValue Symbol)
    (success : intersectValues graph left right = some merged) :
    intersectSlots (slot language left) (slot language right) = some (slot language merged) := by
  cases left <;> cases right <;> simp only [intersectValues] at success
  all_goals try cases success
  rename_i left ls right rs
  cases left <;> cases right <;> simp [slot, intersectSlots, intersectDomains, List.map_append]
  rename_i left right
  have same : language (graph.intersect left right) = fun term => language left term ∧ language right term :=
    funext (fun term => propext (correct left right term))
  rw [same]

/-- A successful source intersection retains both input restrictions exactly. -/
theorem intersection_semantics (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (correct : IntersectionCorrect graph language) (assignment : Nat → Term Symbol) (uv : Nat)
    (left right merged : UVarValue Symbol) (success : intersectValues graph left right = some merged) :
    slotSatisfies assignment uv (slot language merged) ↔
      slotSatisfies assignment uv (slot language left) ∧ slotSatisfies assignment uv (slot language right) :=
  intersectSlots_correct assignment uv _ _ _ (slot_intersection graph language correct left right merged success)

/-- The concrete array and ancestry update performed by successful pending-slot assimilation. -/
def assimilated (state : State Symbol Guard) (target source : Nat) (merged : UVarValue Symbol) : State Symbol Guard :=
  {state with
    values := (state.values.set target merged).set source .eliminated
    recursionAncestry := fun other => if other = target then
      (state.recursionAncestry source ++ state.recursionAncestry target).eraseDups
      else state.recursionAncestry other}

/-- A pending source and target follow the actual source assimilation branch exactly. -/
theorem assimilate_exact (graph : Graph Symbol Guard) (state : State Symbol Guard)
    (target source : Nat) (sourceNode targetNode : Option Nat) (sourceScs targetScs : List Suspended)
    (merged : UVarValue Symbol) (different : target ≠ source)
    (sourceRead : state.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetRead : state.values[target]? = some (.unenumerated targetNode targetScs))
    (intersection : intersectValues graph (.unenumerated sourceNode sourceScs) (.unenumerated targetNode targetScs) = some merged)
    (notEmpty : hasEmptyContents graph merged = false) :
    EnumerationState.assimilate graph target source state = [.ok ((), assimilated state target source merged)] := by
  simp [EnumerationState.assimilate, different, rawValue, sourceRead, targetRead, intersection,
    require, notEmpty, setValue, assimilated, bind, get, getThe, MonadStateOf.get, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
    ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk]

/-- Actual pending-slot assimilation preserves exactly the complete assignments already equated by union-find. -/
theorem assimilation_semantics (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (correct : IntersectionCorrect graph language) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (state : State Symbol Guard) (target source : Nat)
    (sourceValue targetValue merged : UVarValue Symbol) (different : target ≠ source)
    (sourceRead : state.values[source]? = some sourceValue) (targetRead : state.values[target]? = some targetValue)
    (intersection : intersectValues graph sourceValue targetValue = some merged)
    (equal : assignment target = assignment source) :
    Satisfies language meaning assignment (assimilated state target source merged) ↔
      Satisfies language meaning assignment state := by
  have targetBound := (List.getElem?_eq_some_iff.mp targetRead).1
  have sourceBound := (List.getElem?_eq_some_iff.mp sourceRead).1
  have sourceAfter : source < (state.values.set target merged).length := by simpa using sourceBound
  have sourceHeap : heap language state.values source = slot language sourceValue := by simp [heap, sourceRead]
  have targetHeap : heap language state.values target = slot language targetValue := by simp [heap, targetRead]
  have slots := slot_intersection graph language correct sourceValue targetValue merged intersection
  have abstract : Fragments.assimilate (heap language state.values) target source =
      some (heap language (assimilated state target source merged).values) := by
    simp only [assimilated, heap_set language _ source .eliminated sourceAfter,
      heap_set language _ target merged targetBound, slot]
    cases sourceValue <;> cases targetValue <;> simp only [intersectValues] at intersection
    all_goals try cases intersection
    simp only [slot, List.map_append] at slots
    simp [Fragments.assimilate, different, sourceHeap, targetHeap, slot, slots]
  have exactHeap := Fragments.assimilate_correct _ _ target source assignment equal abstract
  simp only [Satisfies, Fragments.stateSatisfies, assimilated] at exactHeap ⊢
  exact and_congr (and_congr Iff.rfl exactHeap) Iff.rfl

/-- The concrete state after a node restriction is merged into a representative. -/
def nodeMerged (state : State Symbol Guard) (found : UnionFind.Result) (merged : UVarValue Symbol) : State Symbol Guard :=
  {state with
    representatives := found.forest
    values := state.values.set found.representative merged
    recursionAncestry := fun other => if other = found.representative then
      (state.expansionAncestry ++ state.recursionAncestry found.representative).eraseDups
      else state.recursionAncestry other}

/-- The actual node-merge action performs the representative lookup, payload intersection, and ancestry update. -/
theorem mergeNode_exact (graph : Graph Symbol Guard) (state : State Symbol Guard) (fuel uv node : Nat)
    (scs : List Suspended) (found : UnionFind.Result) (previous merged : UVarValue Symbol)
    (lookup : UnionFind.findRoot fuel state.representatives uv = some found)
    (stored : state.values[found.representative]? = some previous)
    (intersection : intersectValues graph (.unenumerated (some node) scs) previous = some merged)
    (notEmpty : hasEmptyContents graph merged = false) :
    mergeNode graph fuel uv node scs state = [.ok ((), nodeMerged state found merged)] := by
  simp [mergeNode, representative, lookup, rawValue, stored, intersection, require, notEmpty,
    setValue, inheritAncestry, nodeMerged, bind, get, getThe, MonadStateOf.get, set, pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.bind, StateT.pure, StateT.get, StateT.set, StateT.modifyGet,
    ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk]

/-- The actual merged node adds exactly its graph language and inherited suspended equalities. -/
theorem mergeNode_semantics (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (correct : IntersectionCorrect graph language) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (state : State Symbol Guard) (fuel uv node : Nat)
    (scs : List Suspended) (found : UnionFind.Result) (previous merged : UVarValue Symbol)
    (valid : UnionFind.Total state.representatives)
    (lookup : UnionFind.findRoot fuel state.representatives uv = some found)
    (stored : state.values[found.representative]? = some previous)
    (intersection : intersectValues graph (.unenumerated (some node) scs) previous = some merged) :
    Satisfies language meaning assignment (nodeMerged state found merged) ↔
      Satisfies language meaning assignment state ∧ language node (assignment uv) ∧
        ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
  have bound := (List.getElem?_eq_some_iff.mp stored).1
  have sourceHeap : heap language state.values found.representative = slot language previous := by simp [heap, stored]
  have slots := slot_intersection graph language correct (.unenumerated (some node) scs) previous merged intersection
  have abstract : Fragments.mergeInto (heap language state.values) found.representative
      (some (language node)) (scs.map fun sc => fun assigned term => Suspended.Holds assigned term sc) =
      some (heap language (nodeMerged state found merged).values) := by
    simp only [nodeMerged, heap_set language _ found.representative merged bound]
    unfold Fragments.mergeInto
    rw [sourceHeap]
    change intersectSlots (.pending (some (language node))
      (scs.map fun sc => fun assigned term => Suspended.Holds assigned term sc))
      (slot language previous) = some (slot language merged) at slots
    rw [slots]
    rfl
  have exactHeap := Fragments.mergeInto_correct _ _ found.representative _ _ assignment abstract
  have path := (UnionFind.findRoot_correct fuel state.representatives uv found lookup).1
  have assigned : UnionFind.Satisfies state.representatives assignment → assignment uv = assignment found.representative :=
    fun consistent => consistent uv found.representative (UnionFind.sameClass_root path)
  simp only [Satisfies, Fragments.stateSatisfies, nodeMerged,
    UnionFind.findRoot_satisfies valid lookup] at exactHeap ⊢
  rw [exactHeap]
  simp only [slotSatisfies, permits, List.mem_map, forall_exists_index, and_imp]
  constructor
  · rintro ⟨⟨consistent, oldHeap, domain, obligations⟩, guards⟩
    refine ⟨⟨⟨consistent, oldHeap⟩, guards⟩, ?_, ?_⟩
    · simpa [assigned consistent] using domain
    · intro sc member
      have holds := obligations _ sc member rfl
      simpa [assigned consistent] using holds
  · rintro ⟨⟨⟨consistent, oldHeap⟩, guards⟩, domain, obligations⟩
    refine ⟨⟨consistent, oldHeap, ?_, ?_⟩, guards⟩
    · simpa [assigned consistent] using domain
    · intro obligation sc member same
      subst obligation
      simpa [assigned consistent] using obligations sc member

/-- A structural-empty check cannot reject a satisfying pending slot for the actual graph denotation. -/
theorem empty_check_sound (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (uv : Nat) (value : UVarValue Symbol)
    (empty : hasEmptyContents graph value = true) :
    ¬slotSatisfies assignment uv (slot (Accepted graph meaning) value) := by
  cases value with
  | enumerated _ | eliminated => simp [hasEmptyContents] at empty
  | unenumerated node scs =>
      cases node with
      | none => simp [hasEmptyContents] at empty
      | some node =>
          cases view : graph.node node <;> simp [hasEmptyContents, view] at empty
          intro satisfies
          exact accepted_empty graph meaning node (assignment uv) view satisfies.1

/-- The consecutive variables assigned to one edge's equality classes. -/
def suspendedVars (start : Nat) : List EqualityTrie.Trie → List Suspended
  | [] => []
  | trie :: rest => ⟨trie, start⟩ :: suspendedVars (start + 1) rest

/-- Apply the actual pure-equality allocation update once per class. -/
def suspendedState : Nat → State Symbol Guard → State Symbol Guard
  | 0, state => state
  | count + 1, state => suspendedState count (allocated none state)

/-- The actual equality-class traversal allocates exactly the consecutive variables and states above. -/
theorem suspendMany_exact (tries : List EqualityTrie.Trie) (state : State Symbol Guard) :
    tries.mapM suspend state = [.ok (suspendedVars state.counter tries, suspendedState tries.length state)] := by
  induction tries generalizing state with
  | nil => rfl
  | cons trie rest ih =>
      rw [List.mapM_cons]
      rw [bind_single _ _ state (allocated none state) ⟨trie, state.counter⟩ (suspend_exact trie state)]
      rw [bind_single _ _ (allocated none state) (suspendedState rest.length (allocated none state))
        (suspendedVars (allocated none state).counter rest) (ih (allocated none state))]
      rfl

/-- Multi-class suspension retains the allocator-slot alignment. -/
theorem suspended_supply (count : Nat) (state : State Symbol Guard) (aligned : SupplyAligned state) :
    SupplyAligned (suspendedState count state) := by
  induction count generalizing state with
  | zero => exact aligned
  | succ count ih => exact ih (allocated none state) (allocated_supply none state aligned)

/-- The actual class allocations preserve all prior semantic restrictions. -/
theorem suspendMany_semantics (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (count : Nat) (state : State Symbol Guard) (aligned : SupplyAligned state) :
    Satisfies language meaning assignment (suspendedState count state) ↔ Satisfies language meaning assignment state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      exact (ih (allocated none state) (allocated_supply none state aligned)).trans
        (suspend_semantics language meaning assignment state aligned)

/-- Every source equality class occurs in the actual suspended list. -/
theorem suspendedVars_tries (start : Nat) (tries : List EqualityTrie.Trie) :
    (suspendedVars start tries).map EqualityTrie.Suspended.trie = tries := by
  induction tries generalizing start with
  | nil => rfl
  | cons trie rest ih => simp [suspendedVars, ih]

/-- The fresh variables are the ascending interval of the source allocator. -/
theorem suspendedVars_variables (start : Nat) (tries : List EqualityTrie.Trie) :
    (suspendedVars start tries).map EqualityTrie.Suspended.var = List.range' start tries.length := by
  induction tries generalizing start with
  | nil => rfl
  | cons trie rest ih => simp [suspendedVars, ih, List.range'_succ]

/-- Different introduced equality classes use different variables. -/
theorem suspendedVars_distinct (start : Nat) (tries : List EqualityTrie.Trie) :
    ((suspendedVars start tries).map EqualityTrie.Suspended.var).Nodup := by
  rw [suspendedVars_variables]
  exact List.nodup_range'

/-- Reached child obligations reconstruct one source equality class, including terminal and empty classes. -/
theorem equality_from_descendants (assignment : Nat → Term Symbol) (symbol : Symbol)
    (children : List (Term Symbol)) (sc : Suspended) (valid : EqualityTrie.Valid sc.trie)
    (arity : arityAllows children.length [sc] = true)
    (descendants : ∀ index child, children[index]? = some child →
      ∀ descended ∈ descendScs index [sc], Suspended.Holds assignment child descended) :
    EqualityHolds (.node symbol children) sc.trie := by
  cases sc with
  | mk trie uv =>
      cases trie with
      | empty => exact ⟨.node symbol children, by simp [EqualityTrie.fromPathTrie]⟩
      | terminal => exact ⟨.node symbol children, by simp [EqualityTrie.fromPathTrie, Term.atPath]⟩
      | branch branches =>
          have holds := suspended_descent_complete assignment symbol children [⟨.branch branches, uv⟩]
            (by simpa using valid) arity (by simp [EqualityTrie.isTerminal]) descendants
          exact ⟨assignment uv, holds ⟨.branch branches, uv⟩ (by simp)⟩

/-- Arity validity for the fresh class list is precisely the source edge-construction requirement. -/
theorem fresh_arity_iff (arity start : Nat) (tries : List EqualityTrie.Trie) :
    arityAllows arity (suspendedVars start tries) = true ↔
      ∀ trie ∈ tries, ∀ index suffix, index :: suffix ∈ EqualityTrie.fromPathTrie trie → index < arity := by
  rw [arityAllows_correct]
  constructor
  · intro allows trie member index suffix path
    have presented : trie ∈ (suspendedVars start tries).map EqualityTrie.Suspended.trie := by simpa [suspendedVars_tries] using member
    obtain ⟨sc, scMember, same⟩ := List.mem_map.mp presented
    exact allows sc scMember index suffix (by simpa [same] using path)
  · intro allows sc member index suffix path
    have present : sc.trie ∈ tries := by
      rw [← suspendedVars_tries start tries]
      exact List.mem_map.mpr ⟨sc, member, rfl⟩
    exact allows sc.trie present index suffix path

/-- The source's child descent retains an obligation from any sublist of suspended classes. -/
theorem descendScs_mono (index : Nat) (left right : List Suspended) (included : left ⊆ right) :
    descendScs index left ⊆ descendScs index right := by
  intro sc member
  simp only [descendScs, EqualityTrie.descendScs, List.mem_filter, List.mem_map] at member ⊢
  obtain ⟨⟨original, present, same⟩, nonempty⟩ := member
  exact ⟨⟨original, included present, same⟩, nonempty⟩

/-- Every equality on a selected edge follows from the actual descended fresh obligations. -/
theorem edge_equalities_from_children (assignment : Nat → Term Symbol) (symbol : Symbol)
    (children : List (Term Symbol)) (tries : List EqualityTrie.Trie) (start : Nat) (inherited : List Suspended)
    (valid : ∀ trie ∈ tries, EqualityTrie.Valid trie)
    (fits : arityAllows children.length (suspendedVars start tries) = true)
    (descendants : ∀ index child, children[index]? = some child →
      ∀ sc ∈ descendScs index (inherited ++ suspendedVars start tries), Suspended.Holds assignment child sc) :
    ∀ trie ∈ tries, EqualityHolds (.node symbol children) trie := by
  intro trie member
  have presented : trie ∈ (suspendedVars start tries).map EqualityTrie.Suspended.trie := by simpa [suspendedVars_tries] using member
  obtain ⟨sc, scMember, same⟩ := List.mem_map.mp presented
  rw [← same]
  apply equality_from_descendants assignment symbol children sc (by simpa [same] using valid trie member)
  · apply (arityAllows_correct _ _).mpr
    intro candidate only index suffix path
    have identical : candidate = sc := by simpa using only
    subst candidate
    exact (arityAllows_correct _ _).mp fits sc scMember index suffix path
  · intro index child found candidate present
    apply descendants index child found candidate
    exact descendScs_mono index [sc] (inherited ++ suspendedVars start tries)
      (by
        intro item only
        have same : item = sc := by simpa using only
        subst item
        exact List.mem_append_right inherited scMember) present

/-- Install one witness per fresh class while preserving the pre-existing variable prefix. -/
def install (assignment : Nat → Term Symbol) (start : Nat) : List (Term Symbol) → Nat → Term Symbol
  | [] => assignment
  | term :: rest => install (fun uv => if uv = start then term else assignment uv) (start + 1) rest

/-- Fresh class witnesses do not change any previously allocated value. -/
theorem install_before (assignment : Nat → Term Symbol) (start : Nat) (terms : List (Term Symbol))
    (uv : Nat) (earlier : uv < start) : install assignment start terms uv = assignment uv := by
  induction terms generalizing start assignment with
  | nil => rfl
  | cons term rest ih =>
      rw [install, ih _ _ (by omega)]
      simp [show uv ≠ start by omega]

/-- Every finite collection of satisfied equality classes has a same-length witness vector. -/
theorem equality_witnesses (term : Term Symbol) (tries : List EqualityTrie.Trie)
    (holds : ∀ trie ∈ tries, EqualityHolds term trie) :
    ∃ witnesses, All₂ (fun trie common => ∀ path ∈ EqualityTrie.fromPathTrie trie,
      term.atPath path = some common) tries witnesses := by
  induction tries with
  | nil => exact ⟨[], .nil⟩
  | cons trie rest ih =>
      obtain ⟨common, paths⟩ := holds trie (by simp)
      obtain ⟨witnesses, remaining⟩ := ih (fun next member => holds next (by simp [member]))
      exact ⟨common :: witnesses, .cons paths remaining⟩

/-- Installing the witness vector satisfies the exact variables produced by suspension. -/
theorem installed_classes (term : Term Symbol) (tries : List EqualityTrie.Trie) (witnesses : List (Term Symbol))
    (valid : All₂ (fun trie common => ∀ path ∈ EqualityTrie.fromPathTrie trie,
      term.atPath path = some common) tries witnesses)
    (assignment : Nat → Term Symbol) (start : Nat) :
    ∀ sc ∈ suspendedVars start tries, Suspended.Holds (install assignment start witnesses) term sc := by
  induction valid generalizing assignment start with
  | nil => simp [suspendedVars]
  | @cons trie common rest remaining head tail ih =>
      intro sc member
      simp only [suspendedVars, List.mem_cons] at member
      rcases member with same | member
      · subst sc
        intro path present
        simp only [install]
        rw [install_before _ (start + 1) remaining start (by omega)]
        simpa using head path present
      · exact ih _ _ sc member

/-- Fresh equality variables encode exactly the source classes and preserve every old allocated value. -/
theorem fresh_classes_exact (term : Term Symbol) (tries : List EqualityTrie.Trie)
    (assignment : Nat → Term Symbol) (start : Nat) :
    (∀ trie ∈ tries, EqualityHolds term trie) ↔
      ∃ extended : Nat → Term Symbol, (∀ uv < start, extended uv = assignment uv) ∧
        ∀ sc ∈ suspendedVars start tries, Suspended.Holds extended term sc := by
  constructor
  · intro holds
    obtain ⟨witnesses, valid⟩ := equality_witnesses term tries holds
    exact ⟨install assignment start witnesses, install_before assignment start witnesses,
      installed_classes term tries witnesses valid assignment start⟩
  · rintro ⟨extended, _, holds⟩ trie member
    have present : trie ∈ (suspendedVars start tries).map EqualityTrie.Suspended.trie := by
      simpa [suspendedVars_tries] using member
    obtain ⟨sc, scMember, same⟩ := List.mem_map.mp present
    refine ⟨extended sc.var, ?_⟩
    intro path member
    exact holds sc scMember path (by simpa [same] using member)

/-- One selected edge is accepting when its completed children, descended fresh classes, and residual hold. -/
theorem edge_rule_sound (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (node : Nat) (edges : List (EnumerationState.Edge Symbol Guard)) (edge : EnumerationState.Edge Symbol Guard)
    (children : List (Term Symbol)) (assignment : Nat → Term Symbol) (start : Nat) (inherited : List Suspended)
    (view : graph.node node = .alternatives edges) (selected : edge ∈ edges)
    (accepted : All₂ (Accepted graph meaning) edge.children children)
    (valid : ∀ trie ∈ edge.equalities, EqualityTrie.Valid trie)
    (fits : arityAllows children.length (suspendedVars start edge.equalities) = true)
    (descendants : ∀ index child, children[index]? = some child →
      ∀ sc ∈ descendScs index (inherited ++ suspendedVars start edge.equalities), Suspended.Holds assignment child sc)
    (residual : ResidualHolds meaning edge.residual (.node edge.symbol children)) :
    Accepted graph meaning node (.node edge.symbol children) := by
  exact Accepted.edge node edges edge children view selected accepted
    (edge_equalities_from_children assignment edge.symbol children edge.equalities start inherited valid fits descendants)
    residual

mutual
/-- Every hole of a fragment names an allocated slot. -/
def FragmentBound (limit : Nat) : Fragment Symbol → Prop
  | .hole uv => uv < limit
  | .node _ children => FragmentsBound limit children

/-- The finite child list contains only allocated holes. -/
def FragmentsBound (limit : Nat) : List (Fragment Symbol) → Prop
  | [] => True
  | child :: rest => FragmentBound limit child ∧ FragmentsBound limit rest
end

/-- Every stored equality reference and every stored fragment hole is allocated. -/
def SlotBound (limit : Nat) : UVarValue Symbol → Prop
  | .unenumerated _ scs => ∀ sc ∈ scs, sc.var < limit
  | .enumerated fragment => FragmentBound limit fragment
  | .eliminated => True

/-- Every stored union-find address and parent target stays inside the allocation domain. -/
def ForestBound (limit : Nat) (forest : UnionFind.Forest) : Prop :=
  ∀ uv entry, forest uv = some entry → uv < limit ∧
    match entry with
    | .root _ => True
    | .parent next => next < limit

/-- Storage safety needed to justify fresh-variable extension and representative lookup. -/
structure StorageValid (state : State Symbol Guard) : Prop where
  aligned : SupplyAligned state
  total : UnionFind.Total state.representatives
  forest : ForestBound state.counter state.representatives
  values : ∀ value ∈ state.values, SlotBound state.counter value
  guards : ∀ obligation ∈ state.obligations, FragmentBound state.counter obligation.2

/-- No unallocated variable has an explicit union-find entry. -/
theorem outside_forest (forest : UnionFind.Forest) (limit uv : Nat) (bounded : ForestBound limit forest)
    (outside : limit ≤ uv) : forest uv = none := by
  cases entry : forest uv with
  | none => rfl
  | some value => have below := (bounded uv value entry).1; omega

/-- Every representative reached from an allocated variable remains allocated. -/
theorem reaches_bounded (forest : UnionFind.Forest) (limit : Nat) (bounded : ForestBound limit forest)
    (path : UnionFind.Reaches forest uv root count) : uv < limit → root < limit := by
  induction path with
  | root _ => exact id
  | @parent uv next root count lookup tail ih =>
      intro _
      have actual : forest uv = some (.parent next) := by
        cases entry : forest uv with
        | none => simp [UnionFind.read, entry] at lookup
        | some value => simpa [UnionFind.read, entry] using congrArg some lookup
      exact ih (bounded uv (.parent next) actual).2

/-- An unallocated variable is alone in its union-find class. -/
theorem outside_class (forest : UnionFind.Forest) (limit uv other : Nat) (bounded : ForestBound limit forest)
    (outside : limit ≤ uv) (same : UnionFind.SameClass forest uv other) : uv = other := by
  obtain ⟨root, count, left, right⟩ := same
  have singleton : UnionFind.Reaches forest uv uv 1 :=
    .root (by simp [UnionFind.read, outside_forest forest limit uv bounded outside])
  have equal := (UnionFind.reaches_unique left singleton).1
  subst root
  by_cases inside : other < limit
  · have impossible := reaches_bounded forest limit bounded right inside
    omega
  · have singletonOther : UnionFind.Reaches forest other other 1 :=
      .root (by simp [UnionFind.read, outside_forest forest limit other bounded (by omega)])
    exact (UnionFind.reaches_unique right singletonOther).1

/-- Changing only fresh variable values preserves every old forest equality. -/
theorem forest_assignment_congr (forest : UnionFind.Forest) (limit : Nat) (bounded : ForestBound limit forest)
    (left right : Nat → Term Symbol) (agree : ∀ uv < limit, left uv = right uv) :
    UnionFind.Satisfies forest left ↔ UnionFind.Satisfies forest right := by
  have transfer : ∀ (a b : Nat → Term Symbol), (∀ uv < limit, a uv = b uv) →
      UnionFind.Satisfies forest a → UnionFind.Satisfies forest b := by
    intro a b equal satisfies uv other same
    by_cases inside : uv < limit
    · have otherInside : other < limit := by
        by_cases h : other < limit
        · exact h
        · have identical := outside_class forest limit other uv bounded (by omega) (UnionFind.sameClass_symm same)
          omega
      rw [← equal uv inside, ← equal other otherInside]
      exact satisfies uv other same
    · have identical := outside_class forest limit uv other bounded (by omega) same
      simp [identical]
  exact ⟨transfer left right agree, transfer right left (fun uv h => (agree uv h).symm)⟩

mutual
/-- A bounded fragment depends only on the values of allocated holes. -/
theorem fill_bounded (limit : Nat) (left right : Nat → Term Symbol)
    (agree : ∀ uv < limit, left uv = right uv) (fragment : Fragment Symbol)
    (bounded : FragmentBound limit fragment) : fill left fragment = fill right fragment := by
  cases fragment with
  | hole uv => simpa [fill] using agree uv bounded
  | node symbol children =>
      simp only [fill]
      rw [fill_children_bounded limit left right agree children bounded]
termination_by sizeOf fragment

/-- Bounded child lists preserve their order and each completed subtree under agreement. -/
theorem fill_children_bounded (limit : Nat) (left right : Nat → Term Symbol)
    (agree : ∀ uv < limit, left uv = right uv) (children : List (Fragment Symbol))
    (bounded : FragmentsBound limit children) : children.map (fill left) = children.map (fill right) := by
  cases children with
  | nil => rfl
  | cons child rest =>
      have both : FragmentBound limit child ∧ FragmentsBound limit rest := bounded
      simp only [List.map_cons]
      rw [fill_bounded limit left right agree child both.1, fill_children_bounded limit left right agree rest both.2]
termination_by sizeOf children
end

/-- A bounded slot imposes the same restriction after values of fresh variables change. -/
theorem slot_assignment_congr (language : NodeLanguage Symbol) (limit uv : Nat) (allocated : uv < limit)
    (left right : Nat → Term Symbol) (agree : ∀ index < limit, left index = right index)
    (value : UVarValue Symbol) (bounded : SlotBound limit value) :
    slotSatisfies left uv (slot language value) ↔ slotSatisfies right uv (slot language value) := by
  cases value with
  | eliminated => rfl
  | enumerated fragment =>
      simp only [slot, slotSatisfies, fill_bounded limit left right agree fragment bounded, agree uv allocated]
  | unenumerated node scs =>
      simp only [slot, slotSatisfies, List.mem_map, forall_exists_index, and_imp]
      rw [agree uv allocated]
      apply and_congr Iff.rfl
      constructor
      · intro holds obligation sc member same
        subst obligation
        intro path present
        have result := holds _ sc member rfl path present
        simpa [agree sc.var (bounded sc member)] using result
      · intro holds obligation sc member same
        subst obligation
        intro path present
        have result := holds _ sc member rfl path present
        simpa [agree sc.var (bounded sc member)] using result

/-- Storage safety makes extension on fresh variables invisible to every existing state restriction. -/
theorem state_assignment_congr (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (state : State Symbol Guard) (valid : StorageValid state) (left right : Nat → Term Symbol)
    (agree : ∀ uv < state.counter, left uv = right uv) :
    Satisfies language meaning left state ↔ Satisfies language meaning right state := by
  apply and_congr
  · apply and_congr (forest_assignment_congr state.representatives state.counter valid.forest left right agree)
    apply forall_congr'
    intro uv
    cases found : state.values[uv]? with
    | none => simp [heap, found, slot, slotSatisfies]
    | some value =>
        have member := List.mem_of_getElem? found
        have inRange := (List.getElem?_eq_some_iff.mp found).1
        simpa [heap, found] using slot_assignment_congr language state.counter uv (by rw [valid.aligned]; exact inRange)
          left right agree value (valid.values value member)
  · unfold guardsHold
    apply forall_congr'
    intro obligation
    apply imp_congr_right
    intro member
    rw [fill_bounded state.counter left right agree obligation.2 (valid.guards obligation member)]

/-- Fresh class witnesses extend a valid stored assignment without losing any source equality class. -/
theorem fresh_classes_state_complete (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (state : State Symbol Guard) (valid : StorageValid state) (assignment : Nat → Term Symbol)
    (satisfies : Satisfies language meaning assignment state) (term : Term Symbol) (tries : List EqualityTrie.Trie)
    (equalities : ∀ trie ∈ tries, EqualityHolds term trie) :
    ∃ extended, Satisfies language meaning extended (suspendedState tries.length state) ∧
      (∀ uv < state.counter, extended uv = assignment uv) ∧
      ∀ sc ∈ suspendedVars state.counter tries, Suspended.Holds extended term sc := by
  obtain ⟨extended, agree, holds⟩ := (fresh_classes_exact term tries assignment state.counter).mp equalities
  have old := (state_assignment_congr language meaning state valid extended assignment agree).mpr satisfies
  exact ⟨extended, (suspendMany_semantics language meaning extended tries.length state valid.aligned).mpr old, agree, holds⟩

mutual
theorem fragmentBound_mono (low high : Nat) (increase : low ≤ high) (fragment : Fragment Symbol)
    (bounded : FragmentBound low fragment) : FragmentBound high fragment := by
  cases fragment with
  | hole uv => exact Nat.lt_of_lt_of_le bounded increase
  | node symbol children => exact fragmentsBound_mono low high increase children bounded
termination_by sizeOf fragment

theorem fragmentsBound_mono (low high : Nat) (increase : low ≤ high) (children : List (Fragment Symbol))
    (bounded : FragmentsBound low children) : FragmentsBound high children := by
  cases children with
  | nil => trivial
  | cons child rest => exact ⟨fragmentBound_mono low high increase child bounded.1,
      fragmentsBound_mono low high increase rest bounded.2⟩
termination_by sizeOf children
end

theorem slotBound_mono (low high : Nat) (increase : low ≤ high) (value : UVarValue Symbol)
    (bounded : SlotBound low value) : SlotBound high value := by
  cases value with
  | eliminated => trivial
  | enumerated fragment => exact fragmentBound_mono low high increase fragment bounded
  | unenumerated _ scs => exact fun sc member => Nat.lt_of_lt_of_le (bounded sc member) increase

theorem forestBound_mono (low high : Nat) (increase : low ≤ high) (forest : UnionFind.Forest)
    (bounded : ForestBound low forest) : ForestBound high forest := by
  intro uv entry stored
  obtain ⟨address, target⟩ := bounded uv entry stored
  refine ⟨Nat.lt_of_lt_of_le address increase, ?_⟩
  cases entry with
  | root _ => trivial
  | parent _ => exact Nat.lt_of_lt_of_le target increase

/-- The actual initial state establishes the complete finite storage invariant. -/
theorem initial_storage (root : Nat) : StorageValid (initial root : State Symbol Guard) := by
  refine ⟨rfl, UnionFind.initial_total _, ?_, ?_, ?_⟩
  · intro uv entry stored
    simp only [initial, UnionFind.withInitialValues, List.mem_singleton] at stored
    by_cases zero : uv = 0
    · subst uv
      simp at stored
      subst entry
      simp [initial]
    · simp [zero] at stored
  · intro value member
    have same : value = .unenumerated (some root) [] := by simpa [initial] using member
    subst value
    simp [initial, SlotBound]
  · simp [initial]

/-- Actual allocation preserves finite storage bounds and the absence of old references to the new variable. -/
theorem allocation_storage (node : Option Nat) (state : State Symbol Guard) (valid : StorageValid state) :
    StorageValid (allocated node state) := by
  refine ⟨allocated_supply node state valid.aligned, valid.total,
    forestBound_mono state.counter (state.counter + 1) (by omega) state.representatives valid.forest, ?_, ?_⟩
  · intro value member
    simp only [allocated, List.mem_append, List.mem_singleton] at member
    rcases member with old | fresh
    · exact slotBound_mono state.counter (state.counter + 1) (by omega) value (valid.values value old)
    · subst value
      simp [SlotBound]
  · intro obligation member
    exact fragmentBound_mono state.counter (state.counter + 1) (by omega) obligation.2 (valid.guards obligation member)

/-- Every class allocation in the actual edge traversal preserves storage safety. -/
theorem suspension_storage (count : Nat) (state : State Symbol Guard) (valid : StorageValid state) :
    StorageValid (suspendedState count state) := by
  induction count generalizing state with
  | zero => exact valid
  | succ count ih => exact ih (allocated none state) (allocation_storage none state valid)

/-- Writing one bounded forest entry preserves the finite support and parent bounds. -/
theorem put_forest_bound (forest : UnionFind.Forest) (limit uv : Nat) (entry : UnionFind.Entry)
    (bounded : ForestBound limit forest) (address : uv < limit)
    (target : match entry with | .root _ => True | .parent next => next < limit) :
    ForestBound limit (UnionFind.put forest uv entry) := by
  intro other value stored
  by_cases same : other = uv
  · subst other
    simp [UnionFind.put] at stored
    subst value
    exact ⟨address, target⟩
  · exact bounded other value (by simpa [UnionFind.put, same] using stored)

/-- Concrete path compression writes only allocated addresses and allocated representative targets. -/
theorem findRoot_bounded (fuel : Nat) (forest : UnionFind.Forest) (limit uv : Nat)
    (bounded : ForestBound limit forest) (inside : uv < limit) (found : UnionFind.Result)
    (result : UnionFind.findRoot fuel forest uv = some found) :
    found.representative < limit ∧ ForestBound limit found.forest := by
  induction fuel generalizing forest uv found with
  | zero => simp [UnionFind.findRoot] at result
  | succ fuel ih =>
      cases stored : forest uv with
      | none =>
          simp [UnionFind.findRoot, stored] at result
          subst found
          exact ⟨inside, put_forest_bound forest limit uv (.root 1) bounded inside trivial⟩
      | some entry =>
          cases entry with
          | root size =>
              simp [UnionFind.findRoot, stored] at result
              subst found
              exact ⟨inside, bounded⟩
          | parent next =>
              cases recursive : UnionFind.findRoot fuel forest next with
              | none => simp [UnionFind.findRoot, stored, recursive] at result
              | some earlier =>
                  obtain ⟨repBound, forestBound⟩ := ih forest next bounded (bounded uv (.parent next) stored).2 earlier recursive
                  simp [UnionFind.findRoot, stored, recursive] at result
                  subst found
                  exact ⟨repBound, put_forest_bound earlier.forest limit uv (.parent earlier.representative)
                    forestBound inside repBound⟩

/-- Linking two allocated roots preserves the forest support bound. -/
theorem link_bounded (forest : UnionFind.Forest) (limit loser winner ls ws : Nat)
    (bounded : ForestBound limit forest) (hl : loser < limit) (hw : winner < limit) :
    ForestBound limit (UnionFind.link forest loser winner ls ws) := by
  exact put_forest_bound _ limit winner (.root (ls + ws))
    (put_forest_bound forest limit loser (.parent winner) bounded hl hw) hw trivial

/-- The actual union implementation preserves allocated forest support and parent targets. -/
theorem union_bounded (fuel : Nat) (forest : UnionFind.Forest) (limit left right : Nat)
    (bounded : ForestBound limit forest) (hl : left < limit) (hr : right < limit)
    (after : UnionFind.Forest) (result : UnionFind.union fuel fuel forest left right = some after) :
    ForestBound limit after := by
  cases firstResult : UnionFind.findRoot fuel forest left with
  | none => simp [UnionFind.union, firstResult] at result
  | some first =>
      obtain ⟨firstBound, firstForest⟩ := findRoot_bounded fuel forest limit left bounded hl first firstResult
      cases secondResult : UnionFind.findRoot fuel first.forest right with
      | none => simp [UnionFind.union, firstResult, secondResult] at result
      | some second =>
          obtain ⟨secondBound, secondForest⟩ := findRoot_bounded fuel first.forest limit right firstForest hr second secondResult
          simp only [UnionFind.union, firstResult, bind, Option.bind, secondResult] at result
          split at result
          · cases result; exact secondForest
          · split at result
            · cases result; exact link_bounded _ _ _ _ _ _ secondForest firstBound secondBound
            · cases result; exact link_bounded _ _ _ _ _ _ secondForest secondBound firstBound

/-- The concrete representative operation preserves the established storage invariant. -/
theorem representative_storage (state : State Symbol Guard) (valid : StorageValid state) (fuel uv : Nat)
    (inside : uv < state.counter) (found : UnionFind.Result)
    (result : UnionFind.findRoot fuel state.representatives uv = some found) :
    StorageValid {state with representatives := found.forest} :=
  ⟨valid.aligned, UnionFind.findRoot_total valid.total result,
    (findRoot_bounded fuel state.representatives state.counter uv valid.forest inside found result).2,
    valid.values, valid.guards⟩

/-- Union of actual allocated variables preserves the established storage invariant. -/
theorem union_storage (state : State Symbol Guard) (valid : StorageValid state) (fuel left right : Nat)
    (hl : left < state.counter) (hr : right < state.counter) (after : UnionFind.Forest)
    (result : UnionFind.union fuel fuel state.representatives left right = some after) :
    StorageValid {state with representatives := after} :=
  ⟨valid.aligned, (UnionFind.union_correct valid.total result).1,
    union_bounded fuel state.representatives state.counter left right valid.forest hl hr after result,
    valid.values, valid.guards⟩

/-- A successful pending intersection preserves the bounds on every suspended variable. -/
theorem intersection_storage (graph : Graph Symbol Guard) (limit : Nat)
    (left right merged : UVarValue Symbol) (hl : SlotBound limit left) (hr : SlotBound limit right)
    (result : intersectValues graph left right = some merged) : SlotBound limit merged := by
  cases left <;> cases right <;> simp only [intersectValues] at result
  all_goals try cases result
  simp only [SlotBound, List.mem_append] at hl hr ⊢
  intro sc member
  exact member.elim (hl sc) (hr sc)

/-- A bounded slot write preserves all concrete storage bounds. -/
theorem set_storage (state : State Symbol Guard) (valid : StorageValid state) (uv : Nat)
    (value : UVarValue Symbol) (bounded : SlotBound state.counter value) :
    StorageValid {state with values := state.values.set uv value} := by
  refine ⟨by simpa [SupplyAligned] using valid.aligned, valid.total, valid.forest, ?_, valid.guards⟩
  intro stored member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact valid.values stored old
  · simpa [same] using bounded

/-- Successful assimilation preserves the concrete storage invariant. -/
theorem assimilation_storage (graph : Graph Symbol Guard) (state : State Symbol Guard)
    (valid : StorageValid state) (target source : Nat) (sourceValue targetValue merged : UVarValue Symbol)
    (sourceRead : state.values[source]? = some sourceValue)
    (targetRead : state.values[target]? = some targetValue)
    (intersection : intersectValues graph sourceValue targetValue = some merged) :
    StorageValid (assimilated state target source merged) := by
  have sourceBound := valid.values sourceValue (List.mem_of_getElem? sourceRead)
  have targetBound := valid.values targetValue (List.mem_of_getElem? targetRead)
  have mergedBound := intersection_storage graph state.counter sourceValue targetValue merged sourceBound targetBound intersection
  have first := set_storage state valid target merged mergedBound
  have second := set_storage _ first source .eliminated trivial
  exact ⟨second.aligned, second.total, second.forest, second.values, second.guards⟩

/-- Node merging preserves the invariant when inherited suspended variables are allocated. -/
theorem mergeNode_storage (graph : Graph Symbol Guard) (state : State Symbol Guard)
    (valid : StorageValid state) (fuel uv node : Nat) (inside : uv < state.counter)
    (scs : List Suspended) (bounded : ∀ sc ∈ scs, sc.var < state.counter)
    (found : UnionFind.Result) (previous merged : UVarValue Symbol)
    (lookup : UnionFind.findRoot fuel state.representatives uv = some found)
    (stored : state.values[found.representative]? = some previous)
    (intersection : intersectValues graph (.unenumerated (some node) scs) previous = some merged) :
    StorageValid (nodeMerged state found merged) := by
  have previousBound := valid.values previous (List.mem_of_getElem? stored)
  have mergedBound := intersection_storage graph state.counter (.unenumerated (some node) scs) previous merged bounded previousBound intersection
  have foundValid := representative_storage state valid fuel uv inside found lookup
  have written := set_storage _ foundValid found.representative merged mergedBound
  exact ⟨written.aligned, written.total, written.forest, written.values, written.guards⟩

/-- Retaining a bounded residual fragment preserves storage safety. -/
theorem guard_storage (state : State Symbol Guard) (valid : StorageValid state)
    (guard : Guard) (fragment : Fragment Symbol) (bounded : FragmentBound state.counter fragment) :
    StorageValid {state with obligations := (guard, fragment) :: state.obligations} := by
  refine ⟨valid.aligned, valid.total, valid.forest, valid.values, ?_⟩
  intro obligation member
  rcases List.mem_cons.mp member with same | old
  · simpa [same] using bounded
  · exact valid.guards obligation old

/-- A pure result leaves the complete state unchanged. -/
theorem success_pure (value result : α) (before after : State Symbol Guard) :
    Success (pure value) before result after ↔ result = value ∧ after = before := by
  simp [Success, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run, eq_comm]

/-- An explicit failure has no successful branch. -/
theorem success_failure (error : Error) (before after : State Symbol Guard) (result : α) :
    ¬Success (failure error) before result after := by
  simp [Success, EnumerationState.failure, ExceptT.run]

/-- The actual representative read returns exactly the slot of its compressed representative. -/
theorem getValue_success (fuel uv : Nat) (state after : State Symbol Guard) (value : UVarValue Symbol) :
    Success (getValue fuel uv) state value after ↔
      ∃ found, UnionFind.findRoot fuel state.representatives uv = some found ∧
        state.values[found.representative]? = some value ∧ after = {state with representatives := found.forest} := by
  cases lookup : UnionFind.findRoot fuel state.representatives uv with
  | none =>
      simp [Success, getValue, representative, lookup, rawValue, EnumerationState.failure, bind, get, getThe, MonadStateOf.get, set, pure,
        StateT.bind, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run]
  | some found =>
      cases stored : state.values[found.representative]? with
      | none =>
          simp [Success, getValue, representative, lookup, rawValue, stored, EnumerationState.failure, bind, get, getThe, MonadStateOf.get, set, pure,
            StateT.bind, StateT.pure, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run]
      | some previous =>
          simp [Success, getValue, representative, lookup, rawValue, stored, bind, get, getThe, MonadStateOf.get, set, pure,
            StateT.bind, StateT.pure, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run, eq_comm]

/-- A concrete completed rendering has no pending recursive marker branch. -/
def NoMarkers (graph : Graph Symbol Guard) (state : State Symbol Guard) : Prop :=
  ∀ (uv node : Nat) (scs : List Suspended), state.values[uv]? = some (.unenumerated (some node) scs) →
    ∀ body, graph.node node ≠ .recursive body

/-- Conditions retained by reads during concrete rendering. -/
structure RenderValid (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol) (state : State Symbol Guard) : Prop where
  total : UnionFind.Total state.representatives
  satisfies : Satisfies language meaning assignment state
  markers : NoMarkers graph state

/-- Reading a stored value preserves the rendering conditions and its assigned term equation. -/
theorem getValue_sound (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (fuel uv : Nat) (before after : State Symbol Guard) (value : UVarValue Symbol)
    (valid : RenderValid graph language meaning assignment before)
    (success : Success (getValue fuel uv) before value after) :
    RenderValid graph language meaning assignment after ∧
      slotSatisfies assignment uv (slot language value) ∧
      (∀ node scs, value = .unenumerated (some node) scs → ∀ body, graph.node node ≠ .recursive body) := by
  obtain ⟨found, lookup, stored, same⟩ := (getValue_success fuel uv before after value).mp success
  subst after
  have path := (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1
  have assigned := valid.satisfies.1.1 uv found.representative (UnionFind.sameClass_root path)
  have storedHolds := valid.satisfies.1.2 found.representative
  have slotHolds : slotSatisfies assignment found.representative (slot language value) := by
    simpa [heap, stored] using storedHolds
  refine ⟨⟨UnionFind.findRoot_total valid.total lookup,
    (representative_semantics language meaning assignment fuel uv before found valid.total lookup).mpr valid.satisfies,
    valid.markers⟩, ?_, ?_⟩
  · cases value <;> simp_all [slot, slotSatisfies]
  · intro node scs same body
    exact valid.markers found.representative node scs (by simpa [same] using stored) body

/-- List traversal composes established local invariants without reordering outputs. -/
theorem mapM_sound (action : α → EnumerateM Symbol Guard β) (invariant : State Symbol Guard → Prop)
    (relation : α → β → Prop)
    (step : ∀ input before output after, invariant before → Success (action input) before output after →
      invariant after ∧ relation input output)
    (inputs : List α) (before after : State Symbol Guard) (outputs : List β)
    (valid : invariant before) (success : Success (inputs.mapM action) before outputs after) :
    invariant after ∧ All₂ relation inputs outputs := by
  induction inputs generalizing before after outputs with
  | nil =>
      have result := (success_pure [] outputs before after).mp success
      obtain ⟨rfl, rfl⟩ := result
      exact ⟨valid, .nil⟩
  | cons input rest ih =>
      rw [List.mapM_cons] at success
      obtain ⟨output, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨validMiddle, related⟩ := step input before output middle valid first
      obtain ⟨tail, last, remaining, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨validLast, relatedTail⟩ := ih middle last tail validMiddle remaining
      obtain ⟨rfl, rfl⟩ := (success_pure (output :: tail) outputs last after).mp final
      exact ⟨validLast, .cons related relatedTail⟩

/-- Pointwise deterministic outputs form exactly the corresponding mapped list. -/
theorem all₂_map_eq (function : α → β) (inputs : List α) (outputs : List β)
    (related : All₂ (fun input output => output = function input) inputs outputs) :
    outputs = inputs.map function := by
  induction related with
  | nil => rfl
  | cons same _ ih => simp [same, ih]

/-- Actual rendering follows stored fragment equations and preserves the complete assignment.
Pending recursive markers are excluded explicitly; they are not accepted terms. -/
theorem expandFragment_sound (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol) (marker : Symbol)
    (fuel : Nat) (fragment : Fragment Symbol) (before after : State Symbol Guard) (result : Term Symbol)
    (valid : RenderValid graph language meaning assignment before)
    (success : Success (expandFragment graph marker fuel fragment) before result after) :
    RenderValid graph language meaning assignment after ∧ result = fill assignment fragment := by
  induction fuel generalizing fragment before after result with
  | zero => exact (success_failure .fuelExhausted before after result success).elim
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          change Success (children.mapM (expandFragment graph marker fuel) >>= fun terms => pure (.node symbol terms))
            before result after at success
          obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨validMiddle, related⟩ := mapM_sound (expandFragment graph marker fuel)
            (RenderValid graph language meaning assignment) (fun child term => term = fill assignment child)
            (fun child before term after valid success => ih child before after term valid success)
            children before middle terms valid traversed
          obtain ⟨rfl, rfl⟩ := (success_pure (.node symbol terms) result middle after).mp final
          exact ⟨validMiddle, by simp [fill, all₂_map_eq (fill assignment) children terms related]⟩
      | hole uv =>
          change Success (getValue (fuel + 1) uv >>= fun value => match value with
            | .enumerated fragment => expandFragment graph marker fuel fragment
            | .unenumerated (some node) _ => match graph.node node with
              | .recursive _ => pure (.node marker [])
              | _ => EnumerationState.failure .unfinishedFragment
            | _ => EnumerationState.failure .unfinishedFragment) before result after at success
          obtain ⟨value, middle, read, final⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨validMiddle, stored, markers⟩ := getValue_sound graph language meaning assignment
            (fuel + 1) uv before middle value valid read
          cases value with
          | eliminated => exact (success_failure .unfinishedFragment middle after result final).elim
          | enumerated fragment =>
              obtain ⟨validAfter, exactTerm⟩ := ih fragment middle after result validMiddle final
              exact ⟨validAfter, by simpa [fill, slot, slotSatisfies] using exactTerm.trans stored⟩
          | unenumerated node scs =>
              cases node with
              | none => exact (success_failure .unfinishedFragment middle after result final).elim
              | some node =>
                  cases view : graph.node node with
                  | recursive body => exact (markers node scs rfl body view).elim
                  | empty | alternatives _ | unresolved _ =>
                      simp only [view] at final
                      exact (success_failure .unfinishedFragment middle after result final).elim

/-- Reading and rendering one complete UVar returns its assigned term. -/
theorem expandUVar_sound (graph : Graph Symbol Guard) (language : NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol) (marker : Symbol)
    (fuel uv : Nat) (before after : State Symbol Guard) (result : Term Symbol)
    (valid : RenderValid graph language meaning assignment before)
    (success : Success (expandUVar graph marker fuel uv) before result after) :
    RenderValid graph language meaning assignment after ∧ result = assignment uv := by
  unfold expandUVar at success
  obtain ⟨value, middle, read, final⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨validMiddle, stored, markers⟩ := getValue_sound graph language meaning assignment
    (fuel + 1) uv before middle value valid read
  cases value with
  | enumerated fragment =>
      obtain ⟨validAfter, exactTerm⟩ := expandFragment_sound graph language meaning assignment marker fuel
        fragment middle after result validMiddle final
      exact ⟨validAfter, exactTerm.trans stored⟩
  | eliminated => simp [Success, reject, ExceptT.run] at final
  | unenumerated node scs =>
      cases node with
      | none => simp [Success, reject, ExceptT.run] at final
      | some node =>
          cases view : graph.node node with
          | recursive body => exact (markers node scs rfl body view).elim
          | empty | alternatives _ | unresolved _ => simp [view, Success, reject, ExceptT.run] at final

/-- Suspended inputs avoid the class of a root that must retain its current slot. -/
def Avoids (forest : UnionFind.Forest) (root : Nat) (scs : List Suspended) : Prop :=
  ∀ sc ∈ scs, ¬UnionFind.SameClass forest root sc.var

/-- Descent cannot introduce a reference to the protected root. -/
theorem descend_avoids (forest : UnionFind.Forest) (root index : Nat) (scs : List Suspended)
    (avoids : Avoids forest root scs) : Avoids forest root (descendScs index scs) := by
  intro sc member
  simp only [descendScs, EqualityTrie.descendScs, List.mem_filter, List.mem_map] at member
  obtain ⟨⟨original, present, rfl⟩, _⟩ := member
  exact avoids original present

/-- Newly allocated equality variables cannot name an old protected class. -/
theorem fresh_avoids (state : State Symbol Guard) (valid : StorageValid state) (root : Nat)
    (inside : root < state.counter) (tries : List EqualityTrie.Trie) :
    Avoids state.representatives root (suspendedVars state.counter tries) := by
  intro sc member same
  have fresh : state.counter ≤ sc.var := by
    have listed : sc.var ∈ (suspendedVars state.counter tries).map EqualityTrie.Suspended.var :=
      List.mem_map.mpr ⟨sc, member, rfl⟩
    rw [suspendedVars_variables] at listed
    obtain ⟨index, _, equal⟩ := List.mem_range'.mp listed
    omega
  have equal := outside_class state.representatives state.counter sc.var root valid.forest fresh
    (UnionFind.sameClass_symm same)
  omega

/-- Path compression retains the protected-class restriction exactly. -/
theorem representative_avoids (forest : UnionFind.Forest) (valid : UnionFind.Total forest)
    (fuel uv root : Nat) (scs : List Suspended) (found : UnionFind.Result)
    (result : UnionFind.findRoot fuel forest uv = some found) :
    Avoids found.forest root scs ↔ Avoids forest root scs := by
  simp only [Avoids, UnionFind.findRoot_classes valid result]

/-- A union of two other classes leaves the protected class unchanged. -/
theorem union_protected_class (forest : UnionFind.Forest) (valid : UnionFind.Total forest)
    (fuel left right root : Nat) (after : UnionFind.Forest)
    (leftOther : ¬UnionFind.SameClass forest root left)
    (rightOther : ¬UnionFind.SameClass forest root right)
    (result : UnionFind.union fuel fuel forest left right = some after) (uv : Nat) :
    UnionFind.SameClass after root uv ↔ UnionFind.SameClass forest root uv := by
  rw [(UnionFind.union_correct valid result).2 root uv]
  simp [leftOther, rightOther]

/-- Combining other equality variables preserves every existing protected input. -/
theorem union_avoids (forest : UnionFind.Forest) (valid : UnionFind.Total forest)
    (fuel left right root : Nat) (after : UnionFind.Forest) (scs : List Suspended)
    (leftOther : ¬UnionFind.SameClass forest root left)
    (rightOther : ¬UnionFind.SameClass forest root right)
    (result : UnionFind.union fuel fuel forest left right = some after) :
    Avoids after root scs ↔ Avoids forest root scs := by
  simp only [Avoids, union_protected_class forest valid fuel left right root after leftOther rightOther result]

/-- Looking up a class disjoint from the protected class cannot return the protected slot. -/
theorem representative_away (forest : UnionFind.Forest) (fuel uv root : Nat)
    (separate : ¬UnionFind.SameClass forest root uv) (found : UnionFind.Result)
    (result : UnionFind.findRoot fuel forest uv = some found) : found.representative ≠ root := by
  intro same
  have related := UnionFind.sameClass_symm (UnionFind.sameClass_root
    (UnionFind.findRoot_correct fuel forest uv found result).1)
  apply separate
  simpa [same] using related

/-- Concrete assimilation writes only its two designated slots. -/
theorem assimilation_frame (state : State Symbol Guard) (target source root : Nat)
    (merged : UVarValue Symbol) (targetOther : root ≠ target) (sourceOther : root ≠ source) :
    (assimilated state target source merged).values[root]? = state.values[root]? := by
  simp [assimilated, Ne.symm targetOther, Ne.symm sourceOther]

/-- Concrete node merging cannot overwrite a slot outside the reached equality class. -/
theorem mergeNode_frame (state : State Symbol Guard) (fuel uv root : Nat)
    (found : UnionFind.Result) (merged : UVarValue Symbol)
    (separate : ¬UnionFind.SameClass state.representatives root uv)
    (lookup : UnionFind.findRoot fuel state.representatives uv = some found) :
    (nodeMerged state found merged).values[root]? = state.values[root]? := by
  have different := representative_away state.representatives fuel uv root separate found lookup
  simp [nodeMerged, different]

/-- A raw graph can contain an edge that the source smart constructor rejects. -/
def invalidArityGraph : Graph Nat Bool :=
  ⟨fun _ => .alternatives [⟨0, [], [.branch [(0, .terminal)]], none⟩], fun left _ => left⟩

/-- The driver relies on the constructor check for new classes; its own guard checks inherited classes. -/
theorem raw_graph_arity_required :
    EnumerationState.results invalidArityGraph 99 6 0 = [.ok (.node 0 [], [])] ∧
      ¬Accepted invalidArityGraph (fun _ _ => True) 0 (.node 0 []) := by
  constructor
  · rfl
  · have emptyLanguage : ∀ term, ¬Accepted invalidArityGraph (fun _ _ => True) 0 term := by
      intro term accepted
      cases accepted with
      | recursive _ _ _ view _ => simp [invalidArityGraph] at view
      | edge _ edges edge children view member childRuns equalities residual =>
          have edgesExact : edges = [⟨0, [], [.branch [(0, .terminal)]], none⟩] := by
            simpa [invalidArityGraph] using view.symm
          subst edges
          have edgeExact : edge = ⟨0, [], [.branch [(0, .terminal)]], none⟩ := List.mem_singleton.mp member
          subst edge
          cases childRuns
          obtain ⟨common, reaches⟩ := equalities (.branch [(0, .terminal)]) (by simp)
          have impossible := reaches [0] (by simp [EqualityTrie.fromPathTrie, EqualityTrie.fromChildren])
          simp [Term.atPath] at impossible
    exact emptyLanguage (.node 0 [])

end MicroCFTA.EnumerationCorrectness
