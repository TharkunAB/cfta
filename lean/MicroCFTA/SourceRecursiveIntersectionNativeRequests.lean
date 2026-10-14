import MicroCFTA.SourceRecursiveIntersectionNative

/-!
# Actual native recursive request steps

These laws identify publication before compiled body execution, exact memo
hits, placeholder bypass, and blocked running thunks. Checked source requests
preserve both memo invariants through lookup and demand. Completion inside
recursive body execution needs a whole-execution correspondence proof.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- An unresolved source node request enters its body without touching either memo table. -/
theorem node_bypass_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (unresolved : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none) :
    step emptyGuard conjoin (.node request next) state = .yielded ((compileNode request).bind next) state := by
  simp only [step, lookupNode, unresolved]

/-- A node miss publishes and marks its original thunk before the compiled body runs. -/
theorem node_miss_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (key : Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (missing : state.nodes.table key = none) :
    let published := (lookupNode width request state).2
    let running := (demandNode state.nodes.next published).2
    step emptyGuard conjoin (.node request next) state =
      .yielded ((compileNode request).bind fun value => .finishNode state.nodes.next value (next value)) running := by
  simp [step, lookupNode, requested, FlatMemoThunk.lookupOrInsert, missing, demandNode,
    FlatMemoThunk.demand, FlatMemoThunk.setStatus, Cache.put]

/-- An edge miss publishes and marks its original row thunk before any child request runs. -/
theorem edge_miss_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (missing : state.edges.table (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = none) :
    let published := (lookupEdge width request state).2
    let running := (demandEdge state.edges.next published).2
    step emptyGuard conjoin (.edge request next) state =
      .yielded ((compileEdge emptyGuard conjoin request).bind fun value => .finishEdge state.edges.next value (next value)) running := by
  simp [step, lookupEdge, FlatMemoThunk.lookupOrInsert, missing, demandEdge,
    FlatMemoThunk.demand, FlatMemoThunk.setStatus, Cache.put]

/-- A completed node hit enters the original continuation without effects. -/
theorem node_ready_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request original : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (key : Triple width) (handle : Nat) (value : Value Symbol Guard)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (published : state.nodes.table key = some handle) (stored : state.nodes.cells handle = some ⟨original, .returned value⟩) :
    step emptyGuard conjoin (.node request next) state = .yielded (next value) state := by
  simp only [step, lookupNode, requested, FlatMemoThunk.lookupOrInsert, published, demandNode, FlatMemoThunk.demand, stored]

/-- A completed edge hit enters the original continuation without effects. -/
theorem edge_ready_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request original : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (handle : Nat) (value : EdgeValue Symbol Guard)
    (published : state.edges.table (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = some handle)
    (stored : state.edges.cells handle = some ⟨original, .returned value⟩) :
    step emptyGuard conjoin (.edge request next) state = .yielded (next value) state := by
  simp only [step, lookupEdge, FlatMemoThunk.lookupOrInsert, published, demandEdge, FlatMemoThunk.demand, stored]

/-- A running node hit retains the original recursive instruction and all current caches. -/
theorem node_busy_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request original : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (key : Triple width) (handle : Nat)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (published : state.nodes.table key = some handle) (stored : state.nodes.cells handle = some ⟨original, .evaluating⟩) :
    step emptyGuard conjoin (.node request next) state = .blocked (.nodeBusy handle) (.node request next) state := by
  simp only [step, lookupNode, requested, FlatMemoThunk.lookupOrInsert, published, demandNode, FlatMemoThunk.demand, stored]

/-- A running edge hit retains the original recursive instruction and all current caches. -/
theorem edge_busy_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request original : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (handle : Nat)
    (published : state.edges.table (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = some handle)
    (stored : state.edges.cells handle = some ⟨original, .evaluating⟩) :
    step emptyGuard conjoin (.edge request next) state = .blocked (.edgeBusy handle) (.edge request next) state := by
  simp only [step, lookupEdge, FlatMemoThunk.lookupOrInsert, published, demandEdge, FlatMemoThunk.demand, stored]

/-- Every checked source node request preserves both memo invariants before its body runs. -/
theorem node_step_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (next : Value Symbol Guard → Code Symbol Guard A) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin (step emptyGuard conjoin (.node request next) state).state := by
  have lookup := lookupNode_valid width emptyGuard conjoin state valid request ready safe
  cases selected : lookupNode width request state with
  | mk selection after =>
    have checked : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after := by simpa only [selected] using lookup
    cases selection with
    | direct actual => simpa only [step, selected, Outcome.state] using checked
    | memoized handle =>
      have demand := demandNode_valid width emptyGuard conjoin after checked handle
      cases demanded : demandNode handle after with
      | mk observation final =>
        have finalValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin final := by simpa only [demanded] using demand
        cases observation <;> simpa only [step, selected, demanded, Outcome.state] using finalValid

/-- Every checked source edge request preserves both memo invariants before its body runs. -/
theorem edge_step_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin (step emptyGuard conjoin (.edge request next) state).state := by
  have lookup := lookupEdge_valid width emptyGuard conjoin state valid request ready safe
  cases selected : lookupEdge width request state with
  | mk handle after =>
    have checked : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after := by simpa only [selected] using lookup
    have demand := demandEdge_valid width emptyGuard conjoin after checked handle
    cases demanded : demandEdge handle after with
    | mk observation final =>
      have finalValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin final := by simpa only [demanded] using demand
      cases observation <;> simpa only [step, selected, demanded, Outcome.state] using finalValid

end MicroCFTA.SourceRecursiveIntersectionNative
