import MicroCFTA.SymbolicCacheIndependence

/-!
# Count requests made by the actual symbolic decoder

Instrumentation counts calls from the five selection workers to `countNode`.
It retains the selected value and the exact cache state. It does not count
work inside the counter, graph primitives, sorting, or integer arithmetic.
The singleton worker still restores each source cache snapshot.
-/
namespace MicroCFTA.SymbolicSelectionCost
open Language SymbolicDriver

/-- A measured action returns its value and its number of count requests. -/
abbrev Measured (Symbol Value : Type) := CountM Symbol (Value × Nat)

/-- Returning a value makes no count request. -/
def ret (value : Value) : Measured Symbol Value := (pure (value, 0) : CountM Symbol (Value × Nat))

/-- Sequential measured actions add their count requests. -/
def bind (first : Measured Symbol Input) (rest : Input → Measured Symbol Value) :
    Measured Symbol Value := show CountM Symbol (Value × Nat) from do
  let (value, firstCost) ← first
  let (result, restCost) ← rest value
  pure (result, firstCost + restCost)

/-- One counter call retains its exact source result and cache changes. -/
def request (action : CountM Symbol Value) : Measured Symbol Value := show CountM Symbol (Value × Nat) from do
  let value ← action
  pure (value, 1)

/-- A finite traversal adds each element's measured work. -/
def traverse (action : Input → Measured Symbol Value) : List Input → Measured Symbol (List Value)
  | [] => ret []
  | first :: rest => bind (action first) fun value =>
      bind (traverse action rest) fun values => ret (value :: values)

/-- Remove only the measured cost. -/
def erase (action : Measured Symbol Value) : CountM Symbol Value := do
  pure (← action).1

/-- Instrumentation of a return preserves the complete source action. -/
theorem erase_ret (value : Value) : erase (ret value : Measured Symbol Value) = pure value := by
  rfl

/-- Erasure commutes with stateful sequencing, including every error. -/
theorem erase_bind (first : Measured Symbol Input) (rest : Input → Measured Symbol Value) :
    erase (bind first rest) = (erase first >>= fun value => erase (rest value)) := by
  simp [erase, bind]

/-- Counting a request does not change its result or cache. -/
theorem erase_request (action : CountM Symbol Value) : erase (request action) = action := by
  simp [erase, request]

/-- Snapshot restoration preserves measured work but discards the same cache changes. -/
theorem erase_isolated (action : Measured Symbol Value) :
    erase (isolated action) = isolated (erase action) := by
  funext before
  simp [erase, isolated, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, Pure.pure, StateT.pure, Except.pure, liftM, monadLift, MonadLift.monadLift, StateT.lift]
  cases action before <;> rfl

/-- Traversal erasure gives the exact source traversal. -/
theorem erase_traverse (action : Input → Measured Symbol Value) (inputs : List Input) :
    erase (traverse action inputs) = inputs.mapM (fun input => erase (action input)) := by
  induction inputs with
  | nil => rfl
  | cons first rest ih => simp only [traverse, erase_bind, erase_ret, ih, List.mapM_cons]

mutual
  /-- Instrument `selectAt`, including its singleton projection test. -/
  def select [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → Int → Measured Symbol (Term Symbol × Nat × Int)
    | 0, _, _, _ => fun _ => .error .fuelExhausted
    | fuel + 1, root, path, rank =>
      bind (request (countNode graph fuel (graph.project path root))) fun count =>
        if count = 1 then
          bind (isolated (unique graph order fuel (graph.project path root) [])) fun term =>
            ret (term, root, rank)
        else choose graph order fuel root path rank (constructorsAt graph order path root)

  /-- Instrument every tested constructor block, including skipped blocks. -/
  def choose [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → Int → List (Symbol × Nat) → Measured Symbol (Term Symbol × Nat × Int)
    | 0, _, _, _, _ => fun _ => .error .fuelExhausted
    | _ + 1, _, _, _, [] => fun _ => .error .missingConstructor
    | fuel + 1, root, path, rank, constructor :: rest =>
      bind (request (countNode graph fuel (graph.condition path constructor root))) fun count =>
        if rank ≥ count then choose graph order fuel root path (rank - count) rest
        else bind (children graph order fuel (graph.condition path constructor root) path rank
          (List.range constructor.2)) fun result => ret (.node constructor.1 result.1, result.2)

  /-- Instrument only the children selected from the progressively conditioned graph. -/
  def children [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → Int → List Nat → Measured Symbol (List (Term Symbol) × Nat × Int)
    | _, root, _, rank, [] => ret ([], root, rank)
    | 0, _, _, _, _ :: _ => fun _ => .error .fuelExhausted
    | fuel + 1, root, path, rank, index :: rest =>
      bind (select graph order fuel root (path ++ [index]) rank) fun result =>
        bind (children graph order fuel result.2.1 path result.2.2 rest) fun remaining =>
          ret (result.1 :: remaining.1, remaining.2)

  /-- Instrument the singleton constructor decoder. -/
  def unique [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) : Nat → Nat → List Nat → Measured Symbol (Term Symbol)
    | 0, _, _ => fun _ => .error .fuelExhausted
    | fuel + 1, root, path => uniqueChoose graph order fuel root path (constructorsAt graph order path root)

  /-- Singleton children use separate copies of the source count snapshot. -/
  def uniqueChoose [DecidableEq Symbol] [Ord Symbol] [Ord Order]
      (graph : Graph Symbol) (order : Symbol → Order) :
      Nat → Nat → List Nat → List (Symbol × Nat) → Measured Symbol (Term Symbol)
    | 0, _, _, _ => fun _ => .error .fuelExhausted
    | _ + 1, _, _, [] => fun _ => .error .missingConstructor
    | fuel + 1, root, path, constructor :: rest =>
      bind (request (countNode graph fuel (graph.condition path constructor root))) fun count =>
        if count = 0 then uniqueChoose graph order fuel root path rest
        else bind (traverse (fun index => isolated (unique graph order fuel root (path ++ [index])))
          (List.range constructor.2)) fun terms => ret (.node constructor.1 terms)
end

/-- All five measured workers erase to their actual source ports, with identical errors and caches. -/
theorem erasure [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat) :
    (∀ root path rank, erase (select graph order fuel root path rank) = selectAt graph order fuel root path rank) ∧
    (∀ root path rank available, erase (choose graph order fuel root path rank available) =
      chooseConstructor graph order fuel root path rank available) ∧
    (∀ root path rank indices, erase (children graph order fuel root path rank indices) =
      selectChildren graph order fuel root path rank indices) ∧
    (∀ root path, erase (unique graph order fuel root path) = selectUnique graph order fuel root path) ∧
    (∀ root path available, erase (uniqueChoose graph order fuel root path available) =
      uniqueConstructor graph order fuel root path available) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intros; rfl
    · intros; rfl
    · intro root path rank indices; cases indices <;> rfl
    · intros; rfl
    · intros; rfl
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro root path rank
      simp only [select, erase_bind, erase_request, selectAt]
      congr 1
      funext count
      split
      · simp only [erase_bind, erase_isolated, ih.2.2.2.1, erase_ret]
      · exact ih.2.1 root path rank _
    · intro root path rank available
      cases available with
      | nil => rfl
      | cons constructor rest =>
        simp only [choose, erase_bind, erase_request, chooseConstructor]
        congr 1
        funext count
        split
        · exact ih.2.1 root path (rank - count) rest
        · simp only [erase_bind, ih.2.2.1, erase_ret]
    · intro root path rank indices
      cases indices with
      | nil => rfl
      | cons index rest =>
        simp only [children, erase_bind, ih.1, ih.2.2.1, erase_ret, selectChildren]
    · intro root path
      exact ih.2.2.2.2 root path _
    · intro root path available
      cases available with
      | nil => rfl
      | cons constructor rest =>
        simp only [uniqueChoose, erase_bind, erase_request, uniqueConstructor]
        congr 1
        funext count
        split
        · exact ih.2.2.2.2 root path rest
        · simp only [erase_bind, erase_traverse, erase_isolated, ih.2.2.2.1, erase_ret]

mutual
  /-- Count every constructor in one returned term. -/
  def nodes : Term Symbol → Nat
    | .node _ terms => 1 + forestNodes terms

  /-- Count every constructor in a returned child list. -/
  def forestNodes : List (Term Symbol) → Nat
    | [] => 0
    | term :: terms => nodes term + forestNodes terms
end

/-- Every returned term contains its root constructor. -/
theorem nodes_positive (term : Term Symbol) : 0 < nodes term := by
  cases term
  simp only [nodes]
  omega

/-- A measured postcondition concerns every successful execution from every cache. -/
def Ensures (action : Measured Symbol Value) (post : Value → Nat → Prop) : Prop :=
  ∀ before value cost after, action before = .ok ((value, cost), after) → post value cost

/-- A measured return satisfies its zero-cost postcondition. -/
theorem ensures_ret (value : Value) (post : Value → Nat → Prop) (holds : post value 0) :
    Ensures (ret value : Measured Symbol Value) post := by
  intro before result cost after completed
  cases completed
  exact holds

/-- A failing measured action has no successful postcondition to check. -/
theorem ensures_error (error : Error) (post : Value → Nat → Prop) :
    Ensures (fun _ : Counts Symbol => .error error) post := by
  intro before value cost after completed
  cases completed

/-- Every completed counter request has measured cost one. -/
theorem ensures_request (action : CountM Symbol Value) :
    Ensures (request action) (fun _ cost => cost = 1) := by
  intro before value cost after completed
  change Except.bind (action before) (fun pair => .ok ((pair.1, 1), pair.2)) = _ at completed
  cases run : action before with
  | error error => simp only [run, Except.bind] at completed; cases completed
  | ok pair =>
    simp only [run, Except.bind, Except.ok.injEq, Prod.mk.injEq] at completed
    exact completed.1.2.symm

/-- Measured postconditions compose at the exact intermediate cache. -/
theorem ensures_bind (first : Measured Symbol Input) (rest : Input → Measured Symbol Value)
    (firstPost : Input → Nat → Prop) (post : Value → Nat → Prop)
    (firstCorrect : Ensures first firstPost)
    (restCorrect : ∀ value cost, firstPost value cost →
      Ensures (rest value) (fun result more => post result (cost + more))) :
    Ensures (bind first rest) post := by
  intro before result cost after completed
  change Except.bind (first before) (fun pair => Except.bind (rest pair.1.1 pair.2)
    (fun other => .ok ((other.1.1, pair.1.2 + other.1.2), other.2))) = _ at completed
  cases firstRun : first before with
  | error error => simp only [firstRun, Except.bind] at completed; cases completed
  | ok pair =>
    rcases pair with ⟨⟨value, firstCost⟩, middle⟩
    cases restRun : rest value middle with
    | error error => simp only [firstRun, restRun, Except.bind] at completed; cases completed
    | ok pair =>
      rcases pair with ⟨⟨output, more⟩, final⟩
      simp only [firstRun, restRun, Except.bind, Except.ok.injEq, Prod.mk.injEq] at completed
      rcases completed with ⟨⟨rfl, rfl⟩, rfl⟩
      exact restCorrect value firstCost (firstCorrect before value firstCost middle firstRun)
        middle output more final restRun

/-- A weaker measured postcondition follows from the proved postcondition. -/
theorem ensures_weaken (action : Measured Symbol Value) (first second : Value → Nat → Prop)
    (correct : Ensures action first) (weaker : ∀ value cost, first value cost → second value cost) :
    Ensures action second := by
  intro before value cost after completed
  exact weaker value cost (correct before value cost after completed)

/-- Cache isolation leaves the inner request count unchanged. -/
theorem ensures_isolated (action : Measured Symbol Value) (post : Value → Nat → Prop)
    (correct : Ensures action post) : Ensures (isolated action) post := by
  intro before value cost after completed
  obtain ⟨inner, run, _⟩ := isolated_inner action before after (value, cost) completed
  exact correct before value cost inner run

/-- A measured traversal adds the bounds of its returned terms. -/
theorem ensures_traverse (action : Input → Measured Symbol (Term Symbol)) (inputs : List Input)
    (factor : Nat) (correct : ∀ input ∈ inputs,
      Ensures (action input) (fun term cost => cost ≤ factor * nodes term)) :
    Ensures (traverse action inputs) (fun terms cost => cost ≤ factor * forestNodes terms) := by
  induction inputs with
  | nil => exact ensures_ret [] _ (by simp [forestNodes])
  | cons first rest ih =>
    rw [traverse]
    refine ensures_bind _ _ _ _ (correct first (by simp)) ?_
    intro term firstCost firstBound
    refine ensures_bind _ _ _ _ (ih (fun input member => correct input (by simp [member]))) ?_
    intro terms restCost restBound
    refine ensures_ret _ _ ?_
    simp only [forestNodes, Nat.mul_add]
    omega

/-- A constructor bound applies to every projected graph queried by these workers. -/
def ConstructorBound [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (bound : Nat) : Prop :=
  ∀ root path, (constructorsAt graph order path root).length ≤ bound

/-- Successful decoding uses at most one projection test and `bound` constructor tests per output node. -/
theorem selection_bounds [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (bound : Nat)
    (bounded : ConstructorBound graph order bound) (fuel : Nat) :
    (∀ root path rank, Ensures (select graph order fuel root path rank)
      (fun result cost => cost ≤ (bound + 1) * nodes result.1)) ∧
    (∀ root path rank available, Ensures (choose graph order fuel root path rank available)
      (fun result cost => cost ≤ available.length + (bound + 1) * (nodes result.1 - 1))) ∧
    (∀ root path rank indices, Ensures (children graph order fuel root path rank indices)
      (fun result cost => cost ≤ (bound + 1) * forestNodes result.1)) ∧
    (∀ root path, Ensures (unique graph order fuel root path)
      (fun term cost => cost ≤ bound * nodes term)) ∧
    (∀ root path available, Ensures (uniqueChoose graph order fuel root path available)
      (fun term cost => cost ≤ available.length + bound * (nodes term - 1))) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intros; exact ensures_error _ _
    · intros; exact ensures_error _ _
    · intro root path rank indices
      cases indices with
      | nil => exact ensures_ret _ _ (by simp [forestNodes])
      | cons index rest => exact ensures_error _ _
    · intros; exact ensures_error _ _
    · intros; exact ensures_error _ _
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro root path rank
      rw [select]
      refine ensures_bind _ _ _ _ (ensures_request _) ?_
      intro count cost costOne
      subst cost
      split
      · refine ensures_bind _ _ _ _ (ensures_isolated _ _ (ih.2.2.2.1 (graph.project path root) [])) ?_
        intro term cost costBound
        refine ensures_ret _ _ ?_
        have positive := nodes_positive term
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      · refine ensures_weaken _ _ _ (ih.2.1 root path rank _) ?_
        intro result cost costBound
        have available := bounded root path
        have positive := nodes_positive result.1
        have rewriteNodes : nodes result.1 = (nodes result.1 - 1) + 1 := by omega
        conv => rhs; rw [rewriteNodes, Nat.mul_add, Nat.mul_one]
        omega
    · intro root path rank available
      cases available with
      | nil => exact ensures_error _ _
      | cons constructor rest =>
        rw [choose]
        refine ensures_bind _ _ _ _ (ensures_request _) ?_
        intro count cost costOne
        subst cost
        split
        · refine ensures_weaken _ _ _ (ih.2.1 root path (rank - count) rest) ?_
          intro result cost costBound
          simp only [List.length_cons]
          omega
        · refine ensures_bind _ _ _ _ (ih.2.2.1 (graph.condition path constructor root) path rank _) ?_
          intro result cost costBound
          refine ensures_ret _ _ ?_
          simp only [nodes, Nat.add_sub_cancel_left, List.length_cons]
          omega
    · intro root path rank indices
      cases indices with
      | nil => exact ensures_ret _ _ (by simp [forestNodes])
      | cons index rest =>
        rw [children]
        refine ensures_bind _ _ _ _ (ih.1 root (path ++ [index]) rank) ?_
        intro result firstCost firstBound
        refine ensures_bind _ _ _ _ (ih.2.2.1 result.2.1 path result.2.2 rest) ?_
        intro remaining restCost restBound
        refine ensures_ret _ _ ?_
        simp only [forestNodes, Nat.mul_add]
        omega
    · intro root path
      rw [unique]
      refine ensures_weaken _ _ _ (ih.2.2.2.2 root path _) ?_
      intro term cost costBound
      have available := bounded root path
      have positive := nodes_positive term
      have rewriteNodes : nodes term = (nodes term - 1) + 1 := by omega
      conv => rhs; rw [rewriteNodes, Nat.mul_add, Nat.mul_one]
      omega
    · intro root path available
      cases available with
      | nil => exact ensures_error _ _
      | cons constructor rest =>
        rw [uniqueChoose]
        refine ensures_bind _ _ _ _ (ensures_request _) ?_
        intro count cost costOne
        subst cost
        split
        · refine ensures_weaken _ _ _ (ih.2.2.2.2 root path rest) ?_
          intro term cost costBound
          simp only [List.length_cons]
          omega
        · refine ensures_bind _ _ _ _ (ensures_traverse _ _ bound
            (fun index _ => ensures_isolated _ _ (ih.2.2.2.1 root (path ++ [index])))) ?_
          intro terms cost costBound
          refine ensures_ret _ _ ?_
          simp only [nodes, Nat.add_sub_cancel_left, List.length_cons]
          omega

/-- Constructor candidates belong to the supplied finite symbol/arity vocabulary. -/
theorem constructor_bound_of_vocabulary [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (vocabulary : List (Symbol × Nat))
    (covers : ∀ root edge, edge ∈ graph.edges root → (edge.symbol, edge.children.length) ∈ vocabulary) :
    ConstructorBound graph order vocabulary.length := by
  intro root path
  apply (constructorsAt_nodup graph order path root).length_le_of_subset
  intro constructor member
  have unsorted := (List.mergeSort_perm _ _).mem_iff.mp member
  obtain ⟨edge, present, same⟩ := List.mem_map.mp (List.mem_eraseDups.mp unsorted)
  exact same ▸ covers (graph.project path root) edge present

/-- Successful erasure retains a unique measured execution with the same output and cache. -/
theorem erased_success (action : Measured Symbol Value) (before after : Counts Symbol) (value : Value)
    (completed : erase action before = .ok (value, after)) :
    ∃ cost, action before = .ok ((value, cost), after) := by
  change Except.bind (action before) (fun pair => .ok (pair.1.1, pair.2)) = _ at completed
  cases run : action before with
  | error error => simp only [run, Except.bind] at completed; cases completed
  | ok pair =>
    rcases pair with ⟨⟨result, cost⟩, final⟩
    simp only [run, Except.bind, Except.ok.injEq, Prod.mk.injEq] at completed
    rcases completed with ⟨rfl, rfl⟩
    exact ⟨cost, rfl⟩

/-- The actual source selection has the proved request bound from any initial count snapshot. -/
theorem source_selection_requests [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (bound : Nat)
    (bounded : ConstructorBound graph order bound) (fuel root : Nat) (path : List Nat) (rank : Int)
    (before after : Counts Symbol) (term : Term Symbol) (final : Nat) (suffix : Int)
    (completed : selectAt graph order fuel root path rank before = .ok ((term, final, suffix), after)) :
    ∃ cost, select graph order fuel root path rank before = .ok (((term, final, suffix), cost), after) ∧
      cost ≤ (bound + 1) * nodes term := by
  obtain ⟨cost, measured⟩ := erased_success (select graph order fuel root path rank) before after
    (term, final, suffix) (by rw [(erasure graph order fuel).1]; exact completed)
  exact ⟨cost, measured, (selection_bounds graph order bound bounded fuel).1 root path rank
    before (term, final, suffix) cost after measured⟩

/-- A finite vocabulary bounds selection requests without using language cardinality. -/
theorem vocabulary_selection_requests [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (vocabulary : List (Symbol × Nat))
    (covers : ∀ root edge, edge ∈ graph.edges root → (edge.symbol, edge.children.length) ∈ vocabulary)
    (fuel root : Nat) (path : List Nat) (rank : Int) (before after : Counts Symbol)
    (term : Term Symbol) (final : Nat) (suffix : Int)
    (completed : selectAt graph order fuel root path rank before = .ok ((term, final, suffix), after)) :
    ∃ cost, select graph order fuel root path rank before = .ok (((term, final, suffix), cost), after) ∧
      cost ≤ (vocabulary.length + 1) * nodes term :=
  source_selection_requests graph order vocabulary.length
    (constructor_bound_of_vocabulary graph order vocabulary covers) fuel root path rank
    before after term final suffix completed

/-- A stored graph count resolves one request without changing the count snapshot. -/
theorem cached_request [DecidableEq Symbol] [Ord Symbol]
    (graph : Graph Symbol) (fuel root : Nat) (before : Counts Symbol) (count : Int)
    (nonempty : (graph.edges root).isEmpty = false) (stored : lookup before.graphs root = some count) :
    request (countNode graph (fuel + 1) root) before = .ok ((count, 1), before) := by
  change Except.bind (countNode graph (fuel + 1) root before) (fun pair => .ok ((pair.1, 1), pair.2)) = _
  rw [countNode_cached graph fuel root before count nonempty stored]
  rfl

/-- Singleton isolation retains its measured requests and restores the entire original snapshot. -/
theorem isolated_requests (action : Measured Symbol Value) (before inner : Counts Symbol)
    (value : Value) (cost : Nat) (completed : action before = .ok ((value, cost), inner)) :
    isolated action before = .ok ((value, cost), before) := by
  rw [isolated_run, completed]

end MicroCFTA.SymbolicSelectionCost
