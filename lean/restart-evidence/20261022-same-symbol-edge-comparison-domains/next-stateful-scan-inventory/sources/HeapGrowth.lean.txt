import MicroCFTA.InternedBinderProtocol
import MicroCFTA.EnumerationBuilderCaches

/-!
# Constructor templates through separate edge and node caches

Templates generate the cache computations. Edge and node counters remain
separate. Canonical records retain the actual child lists and cached metadata.
-/
namespace MicroCFTA.InternedConstructorTemplates
open Cache InternedBinderProtocol

/-- Complete nonrecursive edge keys retain the symbol, ordered child references, and constraint. -/
structure EdgeKey (Symbol Guard : Type) where
  symbol : Symbol
  children : List NodeRef
  constraint : Guard
  deriving DecidableEq

mutual
/-- Stored node records retain the source constructor data and cached free/depth fields. -/
inductive Value (Symbol Guard : Type) where
  | empty
  | reference (name : Reference)
  | node (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
  | union (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
  | mu (entry : Interned NodeKey) (body depthShape ordinaryShape : Value Symbol Guard)

/-- Stored edge records retain the canonical key and complete immutable child records. -/
inductive EdgeValue (Symbol Guard : Type) where
  | mk (entry : Interned (EdgeKey Symbol Guard)) (children : List (Value Symbol Guard))
end

/-- Node equality observes only the constructor tag and its canonical identity. -/
def Value.referenceOf : Value Symbol Guard → NodeRef
  | .empty => .empty
  | .reference name => .ref name
  | .node entry _ _ _ => .node entry.identity
  | .union entry _ _ _ => .union entry.identity
  | .mu entry _ _ _ => .mu entry.identity

/-- Read the cached depth; only Mu adds one to its stored body's depth. -/
def Value.depth : Value Symbol Guard → Nat
  | .empty | .reference _ => 0
  | .node _ _ depth _ | .union _ _ depth _ => depth
  | .mu _ body _ _ => body.depth + 1

/-- Read cached free references and remove the local reference of a Mu. -/
def Value.free : Value Symbol Guard → List Reference
  | .empty => []
  | .reference name => [name]
  | .node _ _ _ free | .union _ _ _ free => free
  | .mu entry body _ _ => body.free.filter (· != .interned entry.identity)

def EdgeValue.entry : EdgeValue Symbol Guard → Interned (EdgeKey Symbol Guard)
  | .mk entry _ => entry

def EdgeValue.children : EdgeValue Symbol Guard → List (Value Symbol Guard)
  | .mk _ children => children

/-- Separate canonical counters plus immutable first-writer record payloads. -/
structure State (Symbol Guard : Type) where
  edges : Cache.State (EdgeKey Symbol Guard)
  nodes : Cache.State NodeKey
  edgeRecords : Table (EdgeKey Symbol Guard) (EdgeValue Symbol Guard)
  nodeRecords : Table NodeKey (Value Symbol Guard)

/-- Both source cache families and both record maps start empty. -/
def empty : State Symbol Guard := ⟨Cache.emptyState, Cache.emptyState, fun _ => none, fun _ => none⟩

/-- Every counter retains its own reservation and canonical-key invariant. -/
def Valid (state : State Symbol Guard) : Prop := Cache.Valid state.edges ∧ Cache.Valid state.nodes

/-- Empty independent caches satisfy both reservation invariants. -/
theorem empty_valid : Valid (empty (Symbol := Symbol) (Guard := Guard)) := ⟨Cache.empty_valid, Cache.empty_valid⟩

/-- Later operations preserve both identity tables and both record tables. -/
structure Grows (before after : State Symbol Guard) : Prop where
  edges : Extends before.edges.table after.edges.table
  nodes : Extends before.nodes.table after.nodes.table
  edgeRecords : Extends before.edgeRecords after.edgeRecords
  nodeRecords : Extends before.nodeRecords after.nodeRecords

theorem grows_refl (state : State Symbol Guard) : Grows state state :=
  ⟨extends_refl _, extends_refl _, extends_refl _, extends_refl _⟩

theorem grows_trans (first : Grows before middle) (second : Grows middle after) : Grows before after :=
  ⟨extends_trans first.edges second.edges, extends_trans first.nodes second.nodes,
    extends_trans first.edgeRecords second.edgeRecords, extends_trans first.nodeRecords second.nodeRecords⟩

/-- An edge request computes its record only from the canonical entry returned by its own cache. -/
def edgeStep [DecidableEq (EdgeKey Symbol Guard)] (key : EdgeKey Symbol Guard)
    (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard) (state : State Symbol Guard) :
    EdgeValue Symbol Guard × State Symbol Guard :=
  let entry := Cache.intern state.edges key
  let records := keepFirst state.edgeRecords key (identify entry.1)
  ((records key).getD (identify entry.1), {state with edges := entry.2, edgeRecords := records})

/-- A node request preserves the first complete record attached to its structural key. -/
def nodeStep (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard) (state : State Symbol Guard) :
    Value Symbol Guard × State Symbol Guard :=
  let entry := Cache.intern state.nodes key
  let records := keepFirst state.nodeRecords key (identify entry.1)
  ((records key).getD (identify entry.1), {state with nodes := entry.2, nodeRecords := records})

/-- Finite generated computations can alternate between the two independent caches. -/
inductive Work (Symbol Guard : Type) : Type → Type 1 where
  | pure (value : Result) : Work Symbol Guard Result
  | edge (key : EdgeKey Symbol Guard) (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard)
      (next : EdgeValue Symbol Guard → Work Symbol Guard Result) : Work Symbol Guard Result
  | node (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
      (next : Value Symbol Guard → Work Symbol Guard Result) : Work Symbol Guard Result

/-- Preserve both cache effects when sequencing generated templates. -/
def Work.bind (work : Work Symbol Guard First) (next : First → Work Symbol Guard Result) : Work Symbol Guard Result :=
  match work with
  | .pure value => next value
  | .edge key identify resume => .edge key identify (fun value => (resume value).bind next)
  | .node key identify resume => .node key identify (fun value => (resume value).bind next)

/-- Execute generated cache requests with separate state updates. -/
def run [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard Result) (state : State Symbol Guard) :
    Result × State Symbol Guard :=
  match work with
  | .pure value => (value, state)
  | .edge key identify resume =>
      let result := edgeStep key identify state
      run (resume result.1) result.2
  | .node key identify resume =>
      let result := nodeStep key identify state
      run (resume result.1) result.2

/-- Each edge-cache request preserves validity and every earlier canonical record. -/
theorem edgeStep_correct [DecidableEq (EdgeKey Symbol Guard)] (key : EdgeKey Symbol Guard)
    (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard) (state : State Symbol Guard)
    (valid : Valid state) : Valid (edgeStep key identify state).2 ∧ Grows state (edgeStep key identify state).2 ∧
      (edgeStep key identify state).2.edgeRecords key = some (edgeStep key identify state).1 := by
  have entry := Cache.intern_correct state.edges key valid.1
  obtain ⟨stored, present⟩ := keepFirst_present state.edgeRecords key (identify (Cache.intern state.edges key).1)
  refine ⟨⟨entry.1, valid.2⟩, ⟨InternedBinderProtocol.intern_grows _ _, extends_refl _,
    keepFirst_extends _ _ _, extends_refl _⟩, ?_⟩
  simp [edgeStep, present]

/-- Each node-cache request preserves validity and every earlier canonical record. -/
theorem nodeStep_correct (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : State Symbol Guard) (valid : Valid state) :
    Valid (nodeStep key identify state).2 ∧ Grows state (nodeStep key identify state).2 ∧
      (nodeStep key identify state).2.nodeRecords key = some (nodeStep key identify state).1 := by
  have entry := Cache.intern_correct state.nodes key valid.2
  obtain ⟨stored, present⟩ := keepFirst_present state.nodeRecords key (identify (Cache.intern state.nodes key).1)
  refine ⟨⟨valid.1, entry.1⟩, ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _,
    extends_refl _, keepFirst_extends _ _ _⟩, ?_⟩
  simp [nodeStep, present]

/-- Every finite template-generated execution retains both canonical cache invariants. -/
theorem run_correct [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard Result)
    (state : State Symbol Guard) (valid : Valid state) : Valid (run work state).2 ∧ Grows state (run work state).2 := by
  induction work generalizing state with
  | pure value => exact ⟨valid, grows_refl _⟩
  | edge key identify resume ih =>
      have step := edgeStep_correct key identify state valid
      have tail := ih (edgeStep key identify state).1 _ step.1
      exact ⟨tail.1, grows_trans step.2.1 tail.2⟩
  | node key identify resume ih =>
      have step := nodeStep_correct key identify state valid
      have tail := ih (nodeStep key identify state).1 _ step.1
      exact ⟨tail.1, grows_trans step.2.1 tail.2⟩

/-- Repeated edge requests reuse both the original identity and its complete child record. -/
theorem edgeStep_replay [DecidableEq (EdgeKey Symbol Guard)] (key : EdgeKey Symbol Guard)
    (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard) (before after : State Symbol Guard)
    (valid : Valid before) (growth : Grows (edgeStep key identify before).2 after) :
    edgeStep key identify after = ((edgeStep key identify before).1, after) := by
  have entry := (Cache.intern_correct before.edges key valid.1).2.1
  have later := growth.edges key _ entry
  have record := growth.edgeRecords key _ (edgeStep_correct key identify before valid).2.2
  simp only [edgeStep, Cache.intern, later, keepFirst, record, Option.getD_some]

/-- Repeated node requests reuse the complete immutable metadata record. -/
theorem nodeStep_replay (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (before after : State Symbol Guard) (valid : Valid before) (growth : Grows (nodeStep key identify before).2 after) :
    nodeStep key identify after = ((nodeStep key identify before).1, after) := by
  have entry := (Cache.intern_correct before.nodes key valid.2).2.1
  have later := growth.nodes key _ entry
  have record := growth.nodeRecords key _ (nodeStep_correct key identify before valid).2.2
  simp only [nodeStep, Cache.intern, later, keepFirst, record, Option.getD_some]

/-- Completed generated computations replay with exactly the same values, metadata, and two counters. -/
theorem replay [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard Result)
    (before after : State Symbol Guard) (valid : Valid before) (growth : Grows (run work before).2 after) :
    run work after = ((run work before).1, after) := by
  induction work generalizing before after with
  | pure value => rfl
  | edge key identify resume ih =>
      have step := edgeStep_correct key identify before valid
      have tail := run_correct (resume (edgeStep key identify before).1) _ step.1
      have repeated := edgeStep_replay key identify before after valid (grows_trans tail.2 growth)
      simp only [run, repeated]
      exact ih _ _ after step.1 growth
  | node key identify resume ih =>
      have step := nodeStep_correct key identify before valid
      have tail := run_correct (resume (nodeStep key identify before).1) _ step.1
      have repeated := nodeStep_replay key identify before after valid (grows_trans tail.2 growth)
      simp only [run, repeated]
      exact ih _ _ after step.1 growth

/-- Sequencing retains all edge, node, and record-table effects. -/
theorem run_bind [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard First)
    (next : First → Work Symbol Guard Result) (state : State Symbol Guard) :
    run (work.bind next) state = run (next (run work state).1) (run work state).2 := by
  induction work generalizing state with
  | pure value => rfl
  | edge key identify resume ih => simp only [Work.bind, run, ih]
  | node key identify resume ih => simp only [Work.bind, run, ih]

/-- Store the same sorted free-reference set as the source's Set.unions. -/
def canonicalFree (names : List Reference) : List Reference :=
  names.eraseDups.mergeSort (fun first second => compare first second != .gt)

/-- Maximum Mu depth among a finite child list, with zero for the empty list. -/
def maximumDepth (children : List (Value Symbol Guard)) : Nat :=
  (children.map Value.depth).foldl max 0

/-- Canonical free references from all actual child records. -/
def childFree (children : List (Value Symbol Guard)) : List Reference :=
  canonicalFree (children.flatMap Value.free)

/-- Intern a complete edge after its ordered children have been built. -/
def makeEdge (symbol : Symbol) (constraint : Guard) (children : List (Value Symbol Guard)) :
    Work Symbol Guard (EdgeValue Symbol Guard) :=
  .edge ⟨symbol, children.map Value.referenceOf, constraint⟩ (fun entry => .mk entry children) Work.pure

/-- Remove exactly the source edges with an EmptyNode child. -/
def surviving (edges : List (EdgeValue Symbol Guard)) : List (EdgeValue Symbol Guard) :=
  edges.filter fun edge => !(edge.children.any (fun child => child.referenceOf == .empty))

/-- Set.toList orders and deduplicates edges by their canonical edge identity. -/
def canonicalEdges (edges : List (EdgeValue Symbol Guard)) : List (EdgeValue Symbol Guard) :=
  (EnumerationBuilderCaches.canonicalIds (edges.map (fun edge => edge.entry.identity))).filterMap
    fun identity => edges.find? (fun edge => edge.entry.identity == identity)

/-- Ordinary identification computes its metadata from the canonical edge children. -/
def identifyNode (edges : List (EdgeValue Symbol Guard)) (entry : Interned NodeKey) : Value Symbol Guard :=
  let children := edges.flatMap EdgeValue.children
  .node entry edges (maximumDepth children) (childFree children)

/-- Execute empty-child removal, canonical edge ordering, and the ordinary node-cache request. -/
def makeNode (edges : List (EdgeValue Symbol Guard)) : Work Symbol Guard (Value Symbol Guard) :=
  let kept := canonicalEdges (surviving edges)
  match kept with
  | [] => .pure .empty
  | first :: rest => .node (.node ((first :: rest).map (fun edge => edge.entry.identity)))
      (identifyNode (first :: rest)) Work.pure

/-- A union contributes its stored members; empty contributes no member. -/
def unionMembers : Value Symbol Guard → List (Value Symbol Guard)
  | .empty => []
  | .union _ members _ _ => members
  | value => [value]

/-- Preserve the first node with each source identity, as Data.List.nub does. -/
def distinctNodes : List (Value Symbol Guard) → List (Value Symbol Guard)
  | [] => []
  | first :: rest => first :: distinctNodes (rest.filter (fun other => other.referenceOf != first.referenceOf))
termination_by values => values.length
decreasing_by simp_wf; have := List.length_filter_le (fun other => other.referenceOf != first.referenceOf) rest; omega

/-- The ordinary-union fast path reads only existing ordinary edge records. -/
def ordinaryEdges : List (Value Symbol Guard) → Option (List (EdgeValue Symbol Guard))
  | [] => some []
  | .node _ edges _ _ :: rest => (ordinaryEdges rest).map (edges ++ ·)
  | _ => none

/-- Execute union flattening, first-identity deduplication, and the ordinary-node fast path. -/
def makeUnion (values : List (Value Symbol Guard)) : Work Symbol Guard (Value Symbol Guard) :=
  match distinctNodes (values.flatMap unionMembers) with
  | [] => .pure .empty
  | [value] => .pure value
  | members =>
      match ordinaryEdges members with
      | some edges => makeNode edges
      | none => .node (.union (members.map Value.referenceOf))
          (fun entry => .union entry members (maximumDepth members) (childFree members)) Work.pure

mutual
/-- Normal finite callback templates use their argument, captured records, constructors, and unions. -/
inductive Template (Symbol Guard : Type) where
  | argument
  | captured (value : Value Symbol Guard)
  | node (edges : List (EdgeTemplate Symbol Guard))
  | union (members : List (Template Symbol Guard))

/-- Each source edge template retains its complete symbol/constraint pair and ordered child templates. -/
inductive EdgeTemplate (Symbol Guard : Type) where
  | mk (symbol : Symbol) (constraint : Guard) (children : List (Template Symbol Guard))
end

mutual
/-- Compile every constructor recursively into the actual two-cache request operations. -/
def compile (template : Template Symbol Guard) (argument : Value Symbol Guard) : Work Symbol Guard (Value Symbol Guard) :=
  match template with
  | .argument => .pure argument
  | .captured value => .pure value
  | .node edges => (compileEdges edges argument).bind makeNode
  | .union members => (compileMany members argument).bind makeUnion
termination_by sizeOf template

/-- Compile ordered template children before their parent constructor. -/
def compileMany (templates : List (Template Symbol Guard)) (argument : Value Symbol Guard) :
    Work Symbol Guard (List (Value Symbol Guard)) :=
  match templates with
  | [] => .pure []
  | first :: rest => (compile first argument).bind fun head =>
      (compileMany rest argument).bind fun tail => .pure (head :: tail)
termination_by sizeOf templates

/-- Compile every edge's children before its separate edge-cache request. -/
def compileEdges (templates : List (EdgeTemplate Symbol Guard)) (argument : Value Symbol Guard) :
    Work Symbol Guard (List (EdgeValue Symbol Guard)) :=
  match templates with
  | [] => .pure []
  | .mk symbol constraint children :: rest => (compileMany children argument).bind fun nodes =>
      (makeEdge symbol constraint nodes).bind fun edge =>
        (compileEdges rest argument).bind fun tail => .pure (edge :: tail)
termination_by sizeOf templates
end

/-- Remove the binder's own bare reference only from a union at the body root. -/
def withoutSelfReference (name : Reference) (body : Value Symbol Guard) : Work Symbol Guard (Value Symbol Guard) :=
  match body with
  | .union _ members _ _ =>
      if members.any (fun member => member.referenceOf == .ref name) then
        makeUnion (members.filter (fun member => member.referenceOf != .ref name))
      else .pure body
  | _ => .pure body

/-- Reference identity selects exactly the bare self operand. -/
theorem referenceOf_self_iff (name : Reference) (value : Value Symbol Guard) :
    value.referenceOf = .ref name ↔ value = .reference name := by
  cases value <;> simp [Value.referenceOf]

/-- The body filter retains every operand except the selected bare reference. -/
theorem withoutSelfReference_members (name : Reference) (members : List (Value Symbol Guard))
    (value : Value Symbol Guard) :
    value ∈ members.filter (fun member => member.referenceOf != .ref name) ↔
      value ∈ members ∧ value ≠ .reference name := by
  simp only [List.mem_filter, bne_iff_ne]
  exact and_congr_right fun _ => not_congr (referenceOf_self_iff name value)

/-- A root union without the selected operand uses the original record without effects. -/
theorem withoutSelfReference_absent (name : Reference) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (absent : .reference name ∉ members) :
    withoutSelfReference name (.union entry members depth free) = .pure (.union entry members depth free) := by
  simp only [withoutSelfReference]
  rw [ite_eq_right_iff]
  intro present
  exfalso
  apply absent
  obtain ⟨member, found, same⟩ := List.any_eq_true.mp present
  exact (referenceOf_self_iff name member).mp (beq_iff_eq.mp same) ▸ found

/-- Normalize the callback result before each probe and before storing the binder body. -/
def compileBody (template : Template Symbol Guard) (name : Reference) : Work Symbol Guard (Value Symbol Guard) :=
  (compile template (.reference name)).bind (withoutSelfReference name)

/-- Rebuilding a normalized binder body reuses its complete records and both counters. -/
theorem compileBody_replay [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (name : Reference) (before after : State Symbol Guard) (valid : Valid before)
    (growth : Grows (run (compileBody template name) before).2 after) :
    run (compileBody template name) after = ((run (compileBody template name) before).1, after) :=
  replay (compileBody template name) before after valid growth

/-- Repeated ordinary constructor templates retain their complete canonical result through both caches. -/
theorem compile_replay [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (argument : Value Symbol Guard) (before after : State Symbol Guard) (valid : Valid before)
    (growth : Grows (run (compile template argument) before).2 after) :
    run (compile template argument) after = ((run (compile template argument) before).1, after) :=
  replay (compile template argument) before after valid growth

/-- Rebuilding ordered children preserves arity, so the source setChildren fast path remains applicable. -/
theorem compileMany_length [DecidableEq (EdgeKey Symbol Guard)] (templates : List (Template Symbol Guard))
    (argument : Value Symbol Guard) (state : State Symbol Guard) :
    (run (compileMany templates argument) state).1.length = templates.length := by
  induction templates generalizing state with
  | nil => simp [compileMany, run]
  | cons first rest ih => simp [compileMany, run_bind, run, ih]

/-- Ordinary constructor plans cannot request a pending Mu key. -/
def ordinaryKey : NodeKey → Prop
  | .mu _ => False
  | _ => True

/-- Every generated node-cache request in this computation uses an ordinary or union key. -/
def Ordinary (work : Work Symbol Guard Result) : Prop :=
  match work with
  | .pure _ => True
  | .edge _ _ resume => ∀ value, Ordinary (resume value)
  | .node key _ resume => ordinaryKey key ∧ ∀ value, Ordinary (resume value)

/-- Sequencing cannot introduce a Mu request when neither component can request one. -/
theorem ordinary_bind (work : Work Symbol Guard First) (next : First → Work Symbol Guard Result)
    (first : Ordinary work) (later : ∀ value, Ordinary (next value)) : Ordinary (work.bind next) := by
  induction work with
  | pure value => exact later value
  | edge key identify resume ih => exact fun value => ih value (first value)
  | node key identify resume ih => exact ⟨first.1, fun value => ih value (first.2 value)⟩

/-- The smart ordinary-node constructor never introduces a Mu cache request. -/
theorem makeNode_ordinary (edges : List (EdgeValue Symbol Guard)) : Ordinary (makeNode edges) := by
  unfold makeNode
  dsimp only
  split <;> simp [Ordinary, ordinaryKey]

/-- Union normalization only returns existing values or requests ordinary/union keys. -/
theorem makeUnion_ordinary (values : List (Value Symbol Guard)) : Ordinary (makeUnion values) := by
  unfold makeUnion
  split
  · trivial
  · trivial
  · split
    · exact makeNode_ordinary _
    · simp [Ordinary, ordinaryKey]

mutual
/-- Template structure derives the absence of recursive cache requests. -/
theorem compile_ordinary (template : Template Symbol Guard) (argument : Value Symbol Guard) :
    Ordinary (compile template argument) := by
  cases template <;> simp only [compile]
  case argument => trivial
  case captured => trivial
  case node edges => exact ordinary_bind _ _ (compileEdges_ordinary edges argument) makeNode_ordinary
  case union members => exact ordinary_bind _ _ (compileMany_ordinary members argument) makeUnion_ordinary
termination_by sizeOf template

/-- Child-list compilation retains the ordinary-request property. -/
theorem compileMany_ordinary (templates : List (Template Symbol Guard)) (argument : Value Symbol Guard) :
    Ordinary (compileMany templates argument) := by
  cases templates <;> simp only [compileMany]
  case nil => trivial
  case cons first rest =>
      exact ordinary_bind _ _ (compile_ordinary first argument) (fun _ =>
        ordinary_bind _ _ (compileMany_ordinary rest argument) (fun _ => trivial))
termination_by sizeOf templates

/-- Separate edge interning does not add a Mu node request. -/
theorem compileEdges_ordinary (templates : List (EdgeTemplate Symbol Guard)) (argument : Value Symbol Guard) :
    Ordinary (compileEdges templates argument) := by
  cases templates with
  | nil => simp [compileEdges, Ordinary]
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [compileEdges]
          exact ordinary_bind _ _ (compileMany_ordinary children argument) (fun _ =>
            ordinary_bind _ _ (by intro value; trivial) (fun _ =>
              ordinary_bind _ _ (compileEdges_ordinary rest argument) (fun _ => trivial)))
termination_by sizeOf templates
end

/-- Removing a bare self reference does not request a binder key. -/
theorem withoutSelfReference_ordinary (name : Reference) (body : Value Symbol Guard) :
    Ordinary (withoutSelfReference name body) := by
  cases body <;> simp only [withoutSelfReference]
  all_goals first | trivial | split <;> first | exact makeUnion_ordinary _ | trivial

/-- Body normalization preserves the absence of pending binder requests. -/
theorem compileBody_ordinary (template : Template Symbol Guard) (name : Reference) :
    Ordinary (compileBody template name) :=
  ordinary_bind _ _ (compile_ordinary template (.reference name)) (withoutSelfReference_ordinary name)

/-- All ordinary body effects leave a pending binder's record slot unchanged. -/
theorem run_preserves_mu [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard Result)
    (state : State Symbol Guard) (ordinary : Ordinary work) (probes : MuKey NodeRef) :
    (run work state).2.nodeRecords (.mu probes) = state.nodeRecords (.mu probes) := by
  induction work generalizing state with
  | pure value => rfl
  | edge key identify resume ih => exact ih _ _ (ordinary _)
  | node key identify resume ih =>
      have different : NodeKey.mu probes ≠ key := by
        intro same
        rw [← same] at ordinary
        exact ordinary.1
      rw [show run (.node key identify resume) state =
        run (resume (nodeStep key identify state).1) (nodeStep key identify state).2 from rfl]
      rw [ih _ _ (ordinary.2 _)]
      cases found : state.nodeRecords key <;> simp [nodeStep, keepFirst, found, put, different]

/-- The compiled finite template cannot force the Mu record currently being identified. -/
theorem compile_preserves_mu [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (argument : Value Symbol Guard) (state : State Symbol Guard) (probes : MuKey NodeRef) :
    (run (compile template argument) state).2.nodeRecords (.mu probes) = state.nodeRecords (.mu probes) :=
  run_preserves_mu _ _ (compile_ordinary template argument) probes

/-- The normalized body leaves its reserved binder record slot unchanged. -/
theorem compileBody_preserves_mu [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (name : Reference) (state : State Symbol Guard) (probes : MuKey NodeRef) :
    (run (compileBody template name) state).2.nodeRecords (.mu probes) = state.nodeRecords (.mu probes) :=
  run_preserves_mu _ _ (compileBody_ordinary template name) probes

/-- Evaluate the source depth probe, then the ordinary probe at that cached depth. -/
def probes [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard) (state : State Symbol Guard) :
    (Value Symbol Guard × Value Symbol Guard) × State Symbol Guard :=
  let first := run (compileBody template .depth) state
  let second := run (compileBody template (.uninterned first.1.depth)) first.2
  ((first.1, second.1), second.2)

/-- Both generated probe executions preserve all earlier cache entries. -/
theorem probes_correct [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (state : State Symbol Guard) (valid : Valid state) : Valid (probes template state).2 ∧ Grows state (probes template state).2 := by
  have first := run_correct (compileBody template .depth) state valid
  have second := run_correct
    (compileBody template (.uninterned (run (compileBody template .depth) state).1.depth)) _ first.1
  exact ⟨second.1, grows_trans first.2 second.2⟩

/-- Rebuilding the generated probe programs reproduces both complete probe records without allocations. -/
theorem probes_replay [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (before after : State Symbol Guard) (valid : Valid before) (growth : Grows (probes template before).2 after) :
    probes template after = ((probes template before).1, after) := by
  let first := run (compileBody template .depth) before
  let second := run (compileBody template (.uninterned first.1.depth)) first.2
  have firstValid : Valid first.2 := (run_correct _ _ valid).1
  have secondGrows : Grows first.2 second.2 := (run_correct _ _ firstValid).2
  have firstReplay := compileBody_replay template .depth before after valid (grows_trans secondGrows growth)
  have secondReplay := compileBody_replay template (.uninterned first.1.depth) first.2 after firstValid growth
  simp only [probes, firstReplay]
  change ((first.1, (run (compileBody template (.uninterned first.1.depth)) after).1),
    (run (compileBody template (.uninterned first.1.depth)) after).2) = _
  rw [secondReplay]

/-- Construct the binder key from the source references of both stored probe records. -/
def muKey (depthShape ordinaryShape : Value Symbol Guard) : NodeKey :=
  .mu ⟨depthShape.referenceOf, ordinaryShape.referenceOf⟩

/-- Reserve/install the binder identity before its ordinary body template runs, then complete its record. -/
def finishMu [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (depthShape ordinaryShape : Value Symbol Guard) (state : State Symbol Guard) : Value Symbol Guard × State Symbol Guard :=
  let key := muKey depthShape ordinaryShape
  match state.nodeRecords key with
  | some value => (value, state)
  | none =>
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      let body := run (compileBody template (.interned entry.1.identity)) allocated
      let candidate := Value.mu entry.1 body.1 depthShape ordinaryShape
      let records := keepFirst body.2.nodeRecords key candidate
      ((records key).getD candidate, {body.2 with nodeRecords := records})

/-- Completing a binder preserves both counters' validity and every installed record. -/
theorem finishMu_correct [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (depthShape ordinaryShape : Value Symbol Guard) (state : State Symbol Guard) (valid : Valid state) :
    Valid (finishMu template depthShape ordinaryShape state).2 ∧
      Grows state (finishMu template depthShape ordinaryShape state).2 := by
  cases found : state.nodeRecords (muKey depthShape ordinaryShape) with
  | some value => simpa [finishMu, found] using And.intro valid (grows_refl state)
  | none =>
      simp only [finishMu, found]
      let entry := Cache.intern state.nodes (muKey depthShape ordinaryShape)
      let allocated := {state with nodes := entry.2}
      have allocatedValid : Valid allocated := ⟨valid.1, (Cache.intern_correct _ _ valid.2).1⟩
      have allocatedGrows : Grows state allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have body := run_correct (compileBody template (.interned entry.1.identity)) allocated allocatedValid
      refine ⟨body.1, grows_trans allocatedGrows (grows_trans body.2 ?_)⟩
      exact ⟨extends_refl _, extends_refl _, extends_refl _, keepFirst_extends _ _ _⟩

/-- The completed binder record is stored under the exact two-probe key. -/
theorem finishMu_stored [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (depthShape ordinaryShape : Value Symbol Guard) (state : State Symbol Guard) :
    (finishMu template depthShape ordinaryShape state).2.nodeRecords (muKey depthShape ordinaryShape) =
      some (finishMu template depthShape ordinaryShape state).1 := by
  cases found : state.nodeRecords (muKey depthShape ordinaryShape) with
  | some value => simp [finishMu, found]
  | none =>
      simp only [finishMu, found]
      obtain ⟨stored, present⟩ := keepFirst_present
        (run (compileBody template (.interned (Cache.intern state.nodes (muKey depthShape ordinaryShape)).1.identity))
          {state with nodes := (Cache.intern state.nodes (muKey depthShape ordinaryShape)).2}).2.nodeRecords
        (muKey depthShape ordinaryShape) _
      rw [present]
      rfl

/-- The body cannot replace the pending Mu record before the outer identification completes. -/
theorem finishMu_miss [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (depthShape ordinaryShape : Value Symbol Guard) (state : State Symbol Guard)
    (missing : state.nodeRecords (muKey depthShape ordinaryShape) = none) :
    let entry := Cache.intern state.nodes (muKey depthShape ordinaryShape)
    let body := run (compileBody template (.interned entry.1.identity)) {state with nodes := entry.2}
    (finishMu template depthShape ordinaryShape state).1 = .mu entry.1 body.1 depthShape ordinaryShape := by
  have unchanged := compileBody_preserves_mu template
    (.interned (Cache.intern state.nodes (muKey depthShape ordinaryShape)).1.identity)
    {state with nodes := (Cache.intern state.nodes (muKey depthShape ordinaryShape)).2}
    ⟨depthShape.referenceOf, ordinaryShape.referenceOf⟩
  have absent := unchanged.trans missing
  dsimp only [muKey] at missing absent
  simp [finishMu, muKey, missing, keepFirst, absent, put]

/-- A completed Mu readback returns the same whole record even after other allocations. -/
theorem finishMu_replay [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (depthShape ordinaryShape : Value Symbol Guard) (before after : State Symbol Guard)
    (growth : Grows (finishMu template depthShape ordinaryShape before).2 after) :
    finishMu template depthShape ordinaryShape after = ((finishMu template depthShape ordinaryShape before).1, after) := by
  have stored := growth.nodeRecords _ _ (finishMu_stored template depthShape ordinaryShape before)
  simp only [finishMu, stored]

/-- The complete raw source Mu constructor uses recursively generated two-cache body templates. -/
def internMu [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard) (state : State Symbol Guard) :
    Value Symbol Guard × State Symbol Guard :=
  let checked := probes template state
  finishMu template checked.1.1 checked.1.2 checked.2

/-- Generated Mu construction preserves both independent cache invariants. -/
theorem internMu_correct [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (state : State Symbol Guard) (valid : Valid state) :
    Valid (internMu template state).2 ∧ Grows state (internMu template state).2 := by
  have first := probes_correct template state valid
  have second := finishMu_correct template (probes template state).1.1 (probes template state).1.2 _ first.1
  exact ⟨second.1, grows_trans first.2 second.2⟩

/-- Fixed template syntax derives stable complete binder identity without a supplied request-family law. -/
theorem internMu_replay [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (before after : State Symbol Guard) (valid : Valid before) (growth : Grows (internMu template before).2 after) :
    internMu template after = ((internMu template before).1, after) := by
  have probeValid := (probes_correct template before valid).1
  have finished := finishMu_correct template (probes template before).1.1 (probes template before).1.2 _ probeValid
  have repeated := probes_replay template before after valid (grows_trans finished.2 growth)
  simp only [internMu, repeated]
  exact finishMu_replay template _ _ _ after growth

/-- The smart constructor removes unused binders and the bare self-cycle after canonical identification. -/
def cleanup : Value Symbol Guard → Value Symbol Guard
  | value@(.mu entry body _ _) =>
      if .interned entry.identity ∉ body.free then body
      else if body.referenceOf = .ref (.interned entry.identity) then .empty else value
  | value => value

/-- Include the source cleanup step after raw canonical Mu construction. -/
def createMu [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard) (state : State Symbol Guard) :
    Value Symbol Guard × State Symbol Guard :=
  let result := internMu template state
  (cleanup result.1, result.2)

/-- Cleanup preserves exact repeated identity, cached metadata, and both counters. -/
theorem createMu_replay [DecidableEq (EdgeKey Symbol Guard)] (template : Template Symbol Guard)
    (before after : State Symbol Guard) (valid : Valid before) (growth : Grows (createMu template before).2 after) :
    createMu template after = ((createMu template before).1, after) := by
  simp only [createMu, internMu_replay template before after valid growth]

/-- Free-reference metadata retains every child reference and no other reference. -/
theorem childFree_member (children : List (Value Symbol Guard)) (reference : Reference) :
    reference ∈ childFree children ↔ ∃ child ∈ children, reference ∈ child.free := by
  simp [childFree, canonicalFree]

/-- The depth fold is exactly the maximum of zero and all child depths. -/
theorem maximumDepth_exact (children : List (Value Symbol Guard)) (limit : Nat) :
    maximumDepth children ≤ limit ↔ ∀ child ∈ children, child.depth ≤ limit := by
  have fold : ∀ (values : List Nat) initial,
      values.foldl max initial ≤ limit ↔ initial ≤ limit ∧ ∀ value ∈ values, value ≤ limit := by
    intro values
    induction values with
    | nil => simp
    | cons first rest ih =>
        intro initial
        simp only [List.foldl_cons, ih, Nat.max_le, List.forall_mem_cons]
        exact and_assoc
  simpa [maximumDepth] using fold (children.map Value.depth) 0

/-- Source ordinary-node identification computes both cached metadata fields from its actual canonical children. -/
theorem identifyNode_metadata (edges : List (EdgeValue Symbol Guard)) (entry : Interned NodeKey) :
    (identifyNode edges entry).depth = maximumDepth (edges.flatMap EdgeValue.children) ∧
      (identifyNode edges entry).free = childFree (edges.flatMap EdgeValue.children) := ⟨rfl, rfl⟩

/-- Every canonical edge lookup preserves its requested identity. -/
theorem canonicalEdges_ids (edges : List (EdgeValue Symbol Guard)) :
    (canonicalEdges edges).map (fun edge => edge.entry.identity) =
      EnumerationBuilderCaches.canonicalIds (edges.map (fun edge => edge.entry.identity)) := by
  have select : ∀ ids : List Nat, (∀ identity ∈ ids, identity ∈ edges.map (fun edge => edge.entry.identity)) →
      (ids.filterMap (fun identity => edges.find? (fun edge => edge.entry.identity == identity))).map
        (fun edge => edge.entry.identity) = ids := by
    intro ids member
    induction ids with
    | nil => rfl
    | cons identity rest ih =>
        have present := member identity (by simp)
        obtain ⟨edge, edgeMember, same⟩ := List.mem_map.mp present
        have available : (edges.find? (fun edge => edge.entry.identity == identity)).isSome :=
          List.find?_isSome.mpr ⟨edge, edgeMember, by simpa using same⟩
        cases found : edges.find? (fun edge => edge.entry.identity == identity) with
        | none => simp [found] at available
        | some selected =>
            have correct : selected.entry.identity = identity := by simpa using List.find?_some found
            simp only [List.filterMap_cons, found, List.map_cons, correct]
            rw [ih (fun name present => member name (by simp [present]))]
  exact select _ (fun identity member => (EnumerationBuilderCaches.canonicalIds_member _ identity).mp member)

mutual
/-- Collect the finite template requests directly from the original constructor syntax. -/
def family (template : Template Symbol Guard) : List (Template Symbol Guard) :=
  template :: match template with
    | .argument | .captured _ => []
    | .node edges => edgeFamily edges
    | .union members => families members
termination_by sizeOf template

/-- Child forests contribute the families of their actual source children. -/
def families (templates : List (Template Symbol Guard)) : List (Template Symbol Guard) :=
  match templates with
  | [] => []
  | first :: rest => family first ++ families rest
termination_by sizeOf templates

/-- Each original edge contributes its ordered child-template family. -/
def edgeFamily (edges : List (EdgeTemplate Symbol Guard)) : List (Template Symbol Guard) :=
  match edges with
  | [] => []
  | .mk _ _ children :: rest => families children ++ edgeFamily rest
termination_by sizeOf edges
end

/-- Every source template occurs in its own derived finite family. -/
theorem family_root (template : Template Symbol Guard) : template ∈ family template := by
  cases template <;> simp [family]

/-- Complete each template-generated request at one fixed argument and retain the returned records. -/
def warmup [DecidableEq (EdgeKey Symbol Guard)] (templates : List (Template Symbol Guard))
    (argument : Value Symbol Guard) (state : State Symbol Guard) : List (Value Symbol Guard) × State Symbol Guard :=
  match templates with
  | [] => ([], state)
  | first :: rest =>
      let head := run (compile first argument) state
      let tail := warmup rest argument head.2
      (head.1 :: tail.1, tail.2)

/-- Completing a finite template family preserves both caches and all cached metadata. -/
theorem warmup_correct [DecidableEq (EdgeKey Symbol Guard)] (templates : List (Template Symbol Guard))
    (argument : Value Symbol Guard) (state : State Symbol Guard) (valid : Valid state) :
    Valid (warmup templates argument state).2 ∧ Grows state (warmup templates argument state).2 := by
  induction templates generalizing state with
  | nil => exact ⟨valid, grows_refl _⟩
  | cons first rest ih =>
      have head := run_correct (compile first argument) state valid
      have tail := ih (run (compile first argument) state).2 head.1
      exact ⟨tail.1, grows_trans head.2 tail.2⟩

/-- The finite identity image has one recorded value per derived template request. -/
theorem warmup_length [DecidableEq (EdgeKey Symbol Guard)] (templates : List (Template Symbol Guard))
    (argument : Value Symbol Guard) (state : State Symbol Guard) :
    (warmup templates argument state).1.length = templates.length := by
  induction templates generalizing state with
  | nil => rfl
  | cons first rest ih => simp [warmup, ih]

/-- Every later member of the actual finite syntax family has one of its completed canonical records. -/
theorem warmup_replay [DecidableEq (EdgeKey Symbol Guard)] (templates : List (Template Symbol Guard))
    (argument : Value Symbol Guard) (before after : State Symbol Guard) (valid : Valid before)
    (growth : Grows (warmup templates argument before).2 after)
    (template : Template Symbol Guard) (member : template ∈ templates) :
    ∃ value ∈ (warmup templates argument before).1, run (compile template argument) after = (value, after) := by
  induction templates generalizing before with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨(run (compile template argument) before).1, by simp [warmup], ?_⟩
        apply compile_replay template argument before after valid
        exact grows_trans (warmup_correct rest argument _ (run_correct _ before valid).1).2 growth
      · obtain ⟨value, present, repeated⟩ := ih (run (compile first argument) before).2
          (run_correct _ before valid).1 growth member
        exact ⟨value, by simpa only [warmup, List.mem_cons] using Or.inr present, repeated⟩

/-- Template syntax derives one finite identity image for repeated rebuilt constructor requests. -/
theorem family_identity_image [DecidableEq (EdgeKey Symbol Guard)] (root : Template Symbol Guard)
    (argument : Value Symbol Guard) (before after : State Symbol Guard) (valid : Valid before)
    (growth : Grows (warmup (family root) argument before).2 after)
    (template : Template Symbol Guard) (member : template ∈ family root) :
    (run (compile template argument) after).1.referenceOf ∈
        (warmup (family root) argument before).1.map Value.referenceOf ∧
      (run (compile template argument) after).2 = after := by
  obtain ⟨value, present, repeated⟩ := warmup_replay (family root) argument before after valid growth template member
  rw [repeated]
  exact ⟨List.mem_map.mpr ⟨value, present, rfl⟩, rfl⟩

/-- A recursive unary template allocates three edge keys and four node keys, including its binder. -/
theorem unary_two_cache_example :
    let template : Template Nat Unit := .node [.mk 0 () [.argument]]
    let result := createMu template empty
    result.1.depth = 1 ∧ result.1.free = [] ∧ result.2.edges.next = 3 ∧ result.2.nodes.next = 4 := by
  cbv

/-- Root self removal gives the same canonical recursive record as the body without that operand. -/
theorem self_union_canonical_example :
    let body : Template Nat Unit := .node [.mk 0 () [.argument]]
    let withSelf := createMu (.union [.argument, body]) empty
    let withoutSelf := createMu body withSelf.2
    withSelf.1 = withoutSelf.1 ∧ withSelf.1.depth = 1 ∧ withSelf.1.free = [] := by
  cbv

/-- An unused binder becomes its remaining ordinary node after the source root filter. -/
theorem self_union_cleanup_example :
    let body : Template Nat Unit := .union [.argument, .node [.mk 0 () []]]
    let result := createMu body empty
    result.1.depth = 0 ∧ result.1.free = [] ∧
      (match result.1 with | .node _ _ _ _ => True | _ => False) := by
  cbv

end MicroCFTA.InternedConstructorTemplates
