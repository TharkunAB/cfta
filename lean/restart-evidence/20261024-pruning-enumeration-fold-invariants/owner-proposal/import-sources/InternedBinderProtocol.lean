import MicroCFTA.Cache

/-!
# Stable identity readback for the two-probe binder protocol

The protocol evaluates both key probes before lookup. A miss reserves and
installs the binder identity before its body computation runs. A hit skips
that computation. Completed finite computations can be replayed after any
table growth without another allocation.
-/
namespace MicroCFTA.InternedBinderProtocol
open Cache

/-- A finite effect tree records key requests, delayed identification, and result-dependent continuations. -/
inductive Work (Key : Type) : Type → Type 1 where
  | pure (value : Result) : Work Key Result
  | intern (key : Key) (identify : Nat → Work Key Unit)
      (next : Interned Key → Work Key Result) : Work Key Result

/-- Sequence probe results while preserving the delayed identification branch. -/
def Work.bind (work : Work Key First) (next : First → Work Key Result) : Work Key Result :=
  match work with
  | .pure value => next value
  | .intern key identify resume => .intern key identify (fun entry => (resume entry).bind next)

/-- Execute lookup before reservation, and install before forcing the winning body. -/
def run [DecidableEq Key] (work : Work Key Result) (state : State Key) : Result × State Key :=
  match work with
  | .pure value => (value, state)
  | .intern key identify resume =>
      match state.table key with
      | some entry => run (resume entry) state
      | none =>
          let reserved := Cache.intern state key
          let identified := run (identify reserved.1.identity) reserved.2
          run (resume reserved.1) identified.2

/-- Every interning call preserves all previously stored identities. -/
theorem intern_grows [DecidableEq Key] (state : State Key) (key : Key) :
    Extends state.table (Cache.intern state key).2.table := by
  cases found : state.table key with
  | some entry => simp only [Cache.intern, found]; exact extends_refl _
  | none =>
      simpa only [Cache.intern, found, reserve, install] using
        keepFirst_extends state.table key (⟨state.next, key⟩ : Interned Key)

/-- Compose two finite atomic cache traces. -/
theorem steps_trans [DecidableEq Key] {before middle after : State Key}
    (first : Steps before middle) (second : Steps middle after) : Steps before after := by
  induction second with
  | refl => exact first
  | next previous step ih => exact .next ih step

/-- A miss has one reservation and one installation; a hit has no atomic allocation step. -/
theorem intern_steps [DecidableEq Key] (state : State Key) (key : Key) :
    Steps state (Cache.intern state key).2 := by
  cases found : state.table key with
  | some entry => simpa only [Cache.intern, found] using Steps.refl state
  | none =>
      simpa only [Cache.intern, found] using
        Steps.next (Steps.next (Steps.refl state) (Step.reserve state key))
          (Step.install (reserve state key).2 (reserve state key).1 (reserve_issued state key))

/-- Each completed protocol execution has an actual finite reservation and installation trace. -/
theorem run_steps [DecidableEq Key] (work : Work Key Result) (state : State Key) :
    Steps state (run work state).2 := by
  induction work generalizing state with
  | pure value => exact .refl state
  | intern key identify resume identifyIH resumeIH =>
      cases found : state.table key with
      | some entry => simpa only [run, found] using resumeIH entry state
      | none =>
          exact steps_trans (intern_steps state key)
            (steps_trans (identifyIH _ _) (by simpa only [run, found] using resumeIH (Cache.intern state key).1 _))

/-- A valid finite counter gives an explicit finite list containing every stored structural key. -/
theorem stored_key_finite (state : State Key) (valid : Valid state) (key : Key) (entry : Interned Key)
    (present : state.table key = some entry) :
    key ∈ (List.range state.next).filterMap state.issued := by
  have issued := (valid.2 key entry present).2
  apply List.mem_filterMap.mpr
  exact ⟨entry.identity, List.mem_range.mpr (valid.1 entry.identity key issued), issued⟩

/-- All completed identification effects preserve the canonical cache invariant. -/
theorem run_valid [DecidableEq Key] (work : Work Key Result) (state : State Key) (valid : Valid state) :
    Valid (run work state).2 := by
  induction work generalizing state with
  | pure value => exact valid
  | intern key identify resume identifyIH continueIH =>
      cases found : state.table key with
      | some entry => simpa only [run, found] using continueIH entry state valid
      | none =>
          have allocated := intern_correct state key valid
          have bodyValid := identifyIH (Cache.intern state key).1.identity _ allocated.1
          simpa only [run, found] using continueIH (Cache.intern state key).1 _ bodyValid

/-- Arbitrary completed probe and identification effects only extend the table. -/
theorem run_grows [DecidableEq Key] (work : Work Key Result) (state : State Key) :
    Extends state.table (run work state).2.table := by
  induction work generalizing state with
  | pure value => exact extends_refl _
  | intern key identify resume identifyIH continueIH =>
      cases found : state.table key with
      | some entry => simpa only [run, found] using continueIH entry state
      | none =>
          exact extends_trans (intern_grows state key)
            (extends_trans (identifyIH _ _) (by simpa only [run, found] using continueIH (Cache.intern state key).1 _))

/-- A completed computation replays using cache hits, with exactly the same result and no state changes. -/
theorem replay [DecidableEq Key] (work : Work Key Result) (before after : State Key)
    (valid : Valid before) (growth : Extends (run work before).2.table after.table) :
    run work after = ((run work before).1, after) := by
  induction work generalizing before after with
  | pure value => rfl
  | intern key identify resume identifyIH continueIH =>
      cases found : before.table key with
      | some entry =>
          have stored := (run_grows (resume entry) before) key entry found
          have later : after.table key = some entry := growth key entry (by simpa only [run, found] using stored)
          simp only [run, found, later]
          exact continueIH entry before after valid (by simpa only [run, found] using growth)
      | none =>
          let allocated := Cache.intern before key
          let identified := run (identify allocated.1.identity) allocated.2
          have allocatedFacts := intern_correct before key valid
          have stored : allocated.2.table key = some allocated.1 := allocatedFacts.2.1
          have bodyStored := (run_grows (identify allocated.1.identity) allocated.2) key allocated.1 stored
          have finalStored := (run_grows (resume allocated.1) identified.2) key allocated.1 bodyStored
          have later : after.table key = some allocated.1 := growth key allocated.1 (by
            simpa only [run, found] using finalStored)
          simp only [run, found, later]
          exact continueIH allocated.1 identified.2 after
            (run_valid (identify allocated.1.identity) allocated.2 allocatedFacts.1)
            (by simpa only [run, found] using growth)

/-- Sequencing executes the second computation in the exact state returned by the first. -/
theorem run_bind [DecidableEq Key] (work : Work Key First) (next : First → Work Key Result)
    (state : State Key) :
    run (work.bind next) state = run (next (run work state).1) (run work state).2 := by
  induction work generalizing state with
  | pure value => rfl
  | intern key identify resume identifyIH resumeIH =>
      cases found : state.table key <;> simp only [Work.bind, run, found, resumeIH]

/-- Complete source reference tags distinguish both probes from actual binder references. -/
inductive Reference where
  | interned (identity : Nat)
  | uninterned (depth : Nat)
  | depth
  | intersection (first second : Nat)
  | state (position : Nat)
  deriving DecidableEq, Ord, Repr

/-- The probe returns its canonical node and cached maximum Mu nesting depth. -/
structure Probe (Node : Type) where
  node : Node
  depth : Nat
  deriving DecidableEq, Repr

/-- The uninterned Mu key contains both probe identities and excludes the callback function. -/
structure MuKey (Node : Type) where
  depthShape : Node
  ordinaryShape : Node
  deriving DecidableEq, Repr

/-- Execute createMuDontCleanup's probes in source order before interning the binder key. -/
def createMu (key : MuKey Node → Key) (body : Reference → Work Key (Probe Node)) : Work Key (Interned Key) :=
  (body .depth).bind fun depthShape =>
    (body (.uninterned depthShape.depth)).bind fun ordinaryShape =>
      .intern (key ⟨depthShape.node, ordinaryShape.node⟩)
        (fun identity => (body (.interned identity)).bind fun _ => .pure ())
        Work.pure

/-- Compute the key from the actual first probe and the depth-selected second probe. -/
def probeKey [DecidableEq Key] (body : Reference → Work Key (Probe Node)) (state : State Key) : MuKey Node :=
  let first := run (body .depth) state
  let second := run (body (.uninterned first.1.depth)) first.2
  ⟨first.1.node, second.1.node⟩

/-- The returned identity is stored under the exact two-probe key after all body effects finish. -/
theorem createMu_readback [DecidableEq Key] (key : MuKey Node → Key)
    (body : Reference → Work Key (Probe Node)) (state : State Key) (valid : Valid state) :
    let result := run (createMu key body) state
    result.1.key = key (probeKey body state) ∧
      result.2.table (key (probeKey body state)) = some result.1 := by
  let first := run (body .depth) state
  let second := run (body (.uninterned first.1.depth)) first.2
  let actualKey := key (MuKey.mk first.1.node second.1.node)
  have firstValid : Valid first.2 := run_valid _ _ valid
  have secondValid : Valid second.2 := run_valid _ _ firstValid
  simp only [createMu, run_bind]
  let request : Work Key (Interned Key) :=
    .intern actualKey (fun identity => (body (.interned identity)).bind fun _ => .pure ()) Work.pure
  change (run request second.2).1.key = actualKey ∧
    (run request second.2).2.table actualKey = some (run request second.2).1
  cases found : second.2.table actualKey with
  | some entry =>
      simp only [request, run, found]
      exact ⟨(secondValid.2 actualKey entry found).1, trivial⟩
  | none =>
      have allocated := intern_correct second.2 actualKey secondValid
      simp only [request, run, found]
      exact ⟨allocated.2.2, run_grows _ _ actualKey _ allocated.2.1⟩

/-- The source's complete two-probe request has stable structural identity after any intervening table growth. -/
theorem createMu_replay [DecidableEq Key] (key : MuKey Node → Key)
    (body : Reference → Work Key (Probe Node)) (before after : State Key)
    (valid : Valid before) (growth : Extends (run (createMu key body) before).2.table after.table) :
    run (createMu key body) after = ((run (createMu key body) before).1, after) :=
  replay (createMu key body) before after valid growth

/-- Replaying the two probes also reconstructs the same key despite intervening allocations. -/
theorem probeKey_replay [DecidableEq Key] (key : MuKey Node → Key)
    (body : Reference → Work Key (Probe Node)) (before after : State Key)
    (valid : Valid before) (growth : Extends (run (createMu key body) before).2.table after.table)
    (afterValid : Valid after) (injective : Function.Injective key) : probeKey body after = probeKey body before := by
  have repeated := createMu_replay key body before after valid growth
  have stored := createMu_readback key body before valid
  have rebuilt := createMu_readback key body after afterValid
  apply injective
  rw [← rebuilt.1, repeated]
  exact stored.1

/-- Source node equality compares its constructor tag and stored identity or reference. -/
inductive NodeRef where
  | empty
  | node (identity : Nat)
  | mu (identity : Nat)
  | union (identity : Nat)
  | ref (reference : Reference)
  deriving DecidableEq, Repr

/-- All fields of UninternedNode equality, with already interned edge identities. -/
inductive NodeKey where
  | node (edges : List Nat)
  | empty
  | union (members : List NodeRef)
  | mu (probes : MuKey NodeRef)
  deriving DecidableEq, Repr

/-- The actual Mu constructor distinguishes different pairs of probe identities. -/
theorem mu_key_injective : Function.Injective NodeKey.mu := by
  intro first second same
  cases same
  rfl

/-- The concrete source key, including both probes, is reconstructed exactly on replay. -/
theorem source_probeKey_replay (body : Reference → Work NodeKey (Probe NodeRef))
    (before after : State NodeKey) (valid : Valid before) (afterValid : Valid after)
    (growth : Extends (run (createMu NodeKey.mu body) before).2.table after.table) :
    probeKey body after = probeKey body before :=
  probeKey_replay NodeKey.mu body before after valid growth afterValid mu_key_injective

/-- Arbitrary later atomic allocations preserve the complete binder identity and key on replay. -/
theorem createMu_after_steps (body : Reference → Work NodeKey (Probe NodeRef))
    (before after : State NodeKey) (valid : Valid before)
    (trace : Steps (run (createMu NodeKey.mu body) before).2 after) :
    run (createMu NodeKey.mu body) after = ((run (createMu NodeKey.mu body) before).1, after) ∧
      probeKey body after = probeKey body before := by
  have growth := steps_table_extends trace
  have afterValid := steps_valid (run_valid _ before valid) trace
  exact ⟨createMu_replay _ body before after valid growth,
    source_probeKey_replay body before after valid afterValid growth⟩

/-- Complete a finite collection of requests and retain each returned value. -/
def warmup [DecidableEq Key] (works : List (Work Key Result)) (state : State Key) : List Result × State Key :=
  match works with
  | [] => ([], state)
  | work :: rest =>
      let head := run work state
      let tail := warmup rest head.2
      (head.1 :: tail.1, tail.2)

/-- A finite request collection preserves validity and every existing identity. -/
theorem warmup_valid_grows [DecidableEq Key] (works : List (Work Key Result)) (state : State Key)
    (valid : Valid state) : Valid (warmup works state).2 ∧ Extends state.table (warmup works state).2.table := by
  induction works generalizing state with
  | nil => exact ⟨valid, extends_refl _⟩
  | cons work rest ih =>
      have tail := ih (run work state).2 (run_valid work state valid)
      exact ⟨tail.1, extends_trans (run_grows work state) tail.2⟩

/-- Every later request from the same finite family returns one stored result and allocates nothing. -/
theorem finite_replay [DecidableEq Key] (works : List (Work Key Result)) (before after : State Key)
    (valid : Valid before) (growth : Extends (warmup works before).2.table after.table)
    (work : Work Key Result) (member : work ∈ works) :
    ∃ result ∈ (warmup works before).1, run work after = (result, after) := by
  induction works generalizing before with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨(run work before).1, by simp [warmup], ?_⟩
        apply replay work before after valid
        exact extends_trans
          (warmup_valid_grows rest (run work before).2 (run_valid work before valid)).2 growth
      · obtain ⟨result, present, repeated⟩ := ih (run first before).2 (run_valid first before valid)
          (by simpa only [warmup] using growth) member
        exact ⟨result, by simpa only [warmup, List.mem_cons] using Or.inr present, repeated⟩

/-- One completed result is recorded for each request in the finite source family. -/
theorem warmup_length [DecidableEq Key] (works : List (Work Key Result)) (state : State Key) :
    (warmup works state).1.length = works.length := by
  induction works generalizing state with
  | nil => rfl
  | cons first rest ih => simp [warmup, ih]

/-- Repeated requests from a completed finite family remain inside one finite structural identity image. -/
theorem finite_identity_image [DecidableEq Key] (works : List (Work Key (Interned Key)))
    (before after : State Key) (valid : Valid before)
    (growth : Extends (warmup works before).2.table after.table)
    (work : Work Key (Interned Key)) (member : work ∈ works) :
    (run work after).1.identity ∈ (warmup works before).1.map Interned.identity ∧
      (run work after).2 = after := by
  obtain ⟨entry, present, repeated⟩ := finite_replay works before after valid growth work member
  rw [repeated]
  exact ⟨List.mem_map.mpr ⟨entry, present, rfl⟩, rfl⟩

/-- Source Map.toAscList order after restriction to the node's finite free-variable set. -/
def bindings (free : List Reference) (environment : Reference → Option NodeRef) : List (Reference × NodeRef) :=
  ((free.mergeSort (fun first second => compare first second != .gt)).eraseDups).filterMap
    fun name => (environment name).map (name, ·)

/-- The binder-result memo key contains the original node identity and complete relevant bindings. -/
structure MemoKey where
  binder : NodeRef
  bindings : List (Reference × NodeRef)
  deriving DecidableEq, Repr

/-- Execute the actual restriction and ascending-list construction for the binder memo key. -/
def memoKey (binder : NodeRef) (free : List Reference) (environment : Reference → Option NodeRef) : MemoKey :=
  ⟨binder, bindings free environment⟩

/-- Irrelevant bindings cannot change the actual serialized memo key. -/
theorem memoKey_congr (binder : NodeRef) (free : List Reference) (first second : Reference → Option NodeRef)
    (agree : ∀ name ∈ free, first name = second name) :
    memoKey binder free first = memoKey binder free second := by
  unfold memoKey bindings
  congr 1
  have auxiliary : ∀ names : List Reference, (∀ name ∈ names, first name = second name) →
      names.filterMap (fun name => (first name).map (name, ·)) =
        names.filterMap (fun name => (second name).map (name, ·)) := by
    intro names agree
    induction names with
    | nil => rfl
    | cons name rest ih =>
        simp only [List.filterMap_cons, agree name (by simp)]
        rw [ih (fun name member => agree name (by simp [member]))]
  apply auxiliary
  intro name member
  have original : name ∈ free := by simpa using member
  rw [agree name original]

/-- Keep and read back the winning whole node, including its original identity. -/
def memoReadback (table : Table MemoKey NodeRef) (key : MemoKey) (candidate : NodeRef) : NodeRef × Table MemoKey NodeRef :=
  let installed := keepFirst table key candidate
  ((installed key).getD candidate, installed)

/-- A completed memo insertion stores exactly the node it returns. -/
theorem memoReadback_stored (table : Table MemoKey NodeRef) (key : MemoKey) (candidate : NodeRef) :
    (memoReadback table key candidate).2 key = some (memoReadback table key candidate).1 := by
  obtain ⟨stored, present⟩ := keepFirst_present table key candidate
  simp [memoReadback, present]

/-- Later same-key memo calls preserve the whole node even if they propose another identity. -/
theorem memoReadback_replay (before after : Table MemoKey NodeRef) (key : MemoKey)
    (first later : NodeRef) (growth : Extends (memoReadback before key first).2 after) :
    memoReadback after key later = ((memoReadback before key first).1, after) := by
  have stored := growth key _ (memoReadback_stored before key first)
  simp [memoReadback, keepFirst, stored]

/-- Source key restriction and completed memo readback give stable identity despite unrelated binding changes. -/
theorem binder_memo_replay (before after : Table MemoKey NodeRef) (binder : NodeRef) (free : List Reference)
    (first second : Reference → Option NodeRef) (agree : ∀ name ∈ free, first name = second name)
    (original candidate : NodeRef)
    (growth : Extends (memoReadback before (memoKey binder free first) original).2 after) :
    memoReadback after (memoKey binder free second) candidate =
      ((memoReadback before (memoKey binder free first) original).1, after) := by
  rw [← memoKey_congr binder free first second agree]
  exact memoReadback_replay before after _ original candidate growth

/-- The constructor-template fragment that returns its argument or one captured source node. -/
inductive RootTemplate where
  | argument
  | captured (node : NodeRef)
  deriving DecidableEq, Repr

/-- Evaluate the normal root template using the captured node's fixed depth metadata. -/
def rootBody (depth : NodeRef → Nat) (template : RootTemplate) (reference : Reference) :
    Work NodeKey (Probe NodeRef) :=
  match template with
  | .argument => .pure ⟨.ref reference, 0⟩
  | .captured node => .pure ⟨node, depth node⟩

/-- In the normal root-template fragment, the two source probes determine the whole callback template. -/
theorem root_probes_complete (depth : NodeRef → Nat) (first second : RootTemplate) (state : State NodeKey)
    (same : probeKey (rootBody depth first) state = probeKey (rootBody depth second) state) : first = second := by
  cases first with
  | argument =>
      cases second with
      | argument => rfl
      | captured node =>
          have first := congrArg MuKey.depthShape same
          have second := congrArg MuKey.ordinaryShape same
          simp only [probeKey, rootBody, run] at first second
          rw [← first] at second
          cases second
  | captured node =>
      cases second with
      | argument =>
          have first := congrArg MuKey.depthShape same
          have second := congrArg MuKey.ordinaryShape same
          simp only [probeKey, rootBody, run] at first second
          rw [first] at second
          cases second
      | captured other =>
          have nodes := congrArg MuKey.depthShape same
          have sameNode : node = other := by simpa only [probeKey, rootBody, run] using nodes
          cases sameNode
          rfl

/-- The source record retains both probes and the completed body at its assigned identity. -/
structure StoredMu where
  identity : Nat
  body : Probe NodeRef
  depthShape : Probe NodeRef
  ordinaryShape : Probe NodeRef

/-- MatchMu returns the stored probe before it runs the general substitution branch. -/
def matchMu (stored : StoredMu) (substitution : Reference → Work NodeKey (Probe NodeRef))
    (reference : Reference) : Work NodeKey (Probe NodeRef) :=
  if reference = .uninterned stored.body.depth then .pure stored.ordinaryShape
  else if reference = .depth then .pure stored.depthShape
  else substitution reference

/-- The complete stored key is the pair used by UninternedMu equality and hashing. -/
def storedKey (stored : StoredMu) : NodeKey :=
  .mu ⟨stored.depthShape.node, stored.ordinaryShape.node⟩

/-- Matching and rebuilding a cached binder retains its identity without running substitution or allocation. -/
theorem matchMu_cached (stored : StoredMu) (substitution : Reference → Work NodeKey (Probe NodeRef))
    (state : State NodeKey) (entry : Interned NodeKey)
    (depthSame : stored.depthShape.depth = stored.body.depth)
    (present : state.table (storedKey stored) = some entry) :
    run (createMu NodeKey.mu (matchMu stored substitution)) state = (entry, state) := by
  simp only [storedKey] at present
  simp [createMu, matchMu, run, Work.bind, depthSame, present]

/-- Construct all retained record fields directly from a normal root template. -/
def rootStored (depth : NodeRef → Nat) (template : RootTemplate) (identity : Nat) : StoredMu :=
  let state : State NodeKey := emptyState
  let first := (run (rootBody depth template .depth) state).1
  let ordinary := (run (rootBody depth template (.uninterned first.depth)) state).1
  let actual := (run (rootBody depth template (.interned identity)) state).1
  ⟨identity, actual, first, ordinary⟩

/-- Variable choice cannot change the Mu-depth metadata of the normal root-template fragment. -/
theorem rootStored_depth (depth : NodeRef → Nat) (template : RootTemplate) (identity : Nat) :
    (rootStored depth template identity).depthShape.depth = (rootStored depth template identity).body.depth := by
  cases template <;> rfl

/-- The source's cached matchMu/createMu round trip follows from derived template metadata. -/
theorem root_roundtrip (depth : NodeRef → Nat) (template : RootTemplate) (identity : Nat)
    (substitution : Reference → Work NodeKey (Probe NodeRef)) (state : State NodeKey)
    (entry : Interned NodeKey) (present : state.table (storedKey (rootStored depth template identity)) = some entry) :
    run (createMu NodeKey.mu (matchMu (rootStored depth template identity) substitution)) state = (entry, state) :=
  matchMu_cached _ substitution state entry (rootStored_depth depth template identity) present

/-- A normally constructed root binder immediately rebuilds to its own stored identity. -/
theorem constructed_root_roundtrip (depth : NodeRef → Nat) (template : RootTemplate)
    (substitution : Reference → Work NodeKey (Probe NodeRef)) (state : State NodeKey)
    (valid : Valid state) :
    let built := run (createMu NodeKey.mu (rootBody depth template)) state
    let stored := rootStored depth template built.1.identity
    run (createMu NodeKey.mu (matchMu stored substitution)) built.2 = built := by
  dsimp only
  apply root_roundtrip
  have present := (createMu_readback NodeKey.mu (rootBody depth template) state valid).2
  have same : storedKey (rootStored depth template
      (run (createMu NodeKey.mu (rootBody depth template)) state).1.identity) =
      NodeKey.mu (probeKey (rootBody depth template) state) := by cases template <;> rfl
  rw [same]
  exact present

/-- A callback that inspects the reference constructor violates the documented Mu parametricity contract. -/
def exoticBody (reference : Reference) : Work NodeKey (Probe NodeRef) :=
  .pure ⟨match reference with | .interned _ => .node 1 | _ => .node 0, 0⟩

/-- Equal probes alone do not imply equal callback behavior at actual binder identities. -/
theorem exotic_probes_incomplete :
    let ordinary := rootBody (fun _ => 0) (.captured (.node 0))
    probeKey ordinary emptyState = probeKey exoticBody emptyState ∧
      (run (ordinary (.interned 7)) emptyState).1.node ≠
        (run (exoticBody (.interned 7)) emptyState).1.node := by
  constructor
  · rfl
  · simp [rootBody, exoticBody, run]

end MicroCFTA.InternedBinderProtocol
