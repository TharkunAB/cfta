import MicroCFTA.EnumerationCorrectness

/-!
# Concrete suspended enumeration scheduling

The scheduler scan executes the actions from `EnumerationState`. The pure
summary below records its candidate slots and blocked representatives. The
proof follows each representative lookup and both source folds.
-/

namespace MicroCFTA.EnumerationSchedule
open Language Fragments EnumerationState EnumerationCorrectness

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

/-- The selected canonical representative of every variable has a finite path. -/
def Roots (forest : UnionFind.Forest) (roots : Nat → Nat) : Prop :=
  ∀ uv, ∃ size, UnionFind.Reaches forest uv (roots uv) size

/-- A total forest supplies canonical representatives without a search-bound assumption. -/
theorem roots_exist (forest : UnionFind.Forest) (valid : UnionFind.Total forest) :
    ∃ roots, Roots forest roots := by
  classical
  refine ⟨fun uv => (valid uv).choose, ?_⟩
  intro uv
  exact (valid uv).choose_spec

/-- The scan retains the value array and every chosen representative. -/
structure ScanValid (values : List (UVarValue Symbol)) (roots : Nat → Nat)
    (state : State Symbol Guard) : Prop where
  values : state.values = values
  roots : Roots state.representatives roots

/-- Successful representative lookup exposes its actual forest update. -/
theorem representative_success (fuel uv : Nat) (before after : State Symbol Guard) (root : Nat) :
    Success (representative fuel uv) before root after ↔
      ∃ found, UnionFind.findRoot fuel before.representatives uv = some found ∧
        root = found.representative ∧ after = {before with representatives := found.forest} := by
  cases lookup : UnionFind.findRoot fuel before.representatives uv with
  | none =>
      simp [Success, representative, lookup, EnumerationState.failure, bind, get, getThe, MonadStateOf.get,
        pure, StateT.bind, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run]
  | some found =>
      simp only [Success, representative_exact fuel uv before found lookup, ExceptT.run]
      simp

/-- Path compression leaves the scan's representative map unchanged. -/
theorem representative_scan (values : List (UVarValue Symbol)) (roots : Nat → Nat)
    (before after : State Symbol Guard) (fuel uv root : Nat)
    (valid : ScanValid values roots before)
    (success : Success (representative fuel uv) before root after) :
    ScanValid values roots after ∧ root = roots uv := by
  obtain ⟨found, lookup, rfl, rfl⟩ := (representative_success fuel uv before after root).mp success
  obtain ⟨size, path⟩ := valid.roots uv
  obtain ⟨actual, preserved⟩ := UnionFind.findRoot_correct fuel before.representatives uv found lookup
  refine ⟨⟨valid.values, ?_⟩, (UnionFind.reaches_unique actual path).1⟩
  intro other
  obtain ⟨count, old⟩ := valid.roots other
  exact ⟨count, preserved old⟩

/-- A deterministic fold composes the local action proofs in source order. -/
theorem foldlM_exact (action : α → β → EnumerateM Symbol Guard α) (step : α → β → α)
    (invariant : State Symbol Guard → Prop)
    (localStep : ∀ accumulator input before result after, invariant before →
      Success (action accumulator input) before result after →
      invariant after ∧ result = step accumulator input)
    (inputs : List β) (accumulator result : α) (before after : State Symbol Guard)
    (valid : invariant before) (success : Success (inputs.foldlM action accumulator) before result after) :
    invariant after ∧ result = inputs.foldl step accumulator := by
  induction inputs generalizing accumulator before with
  | nil =>
      obtain ⟨rfl, rfl⟩ := (success_pure accumulator result before after).mp success
      exact ⟨valid, rfl⟩
  | cons input rest ih =>
      rw [List.foldlM_cons] at success
      obtain ⟨middle, intermediate, first, restSuccess⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨validIntermediate, rfl⟩ := localStep accumulator input before middle intermediate valid first
      exact ih (step accumulator input) intermediate validIntermediate restSuccess

/-- The source's inner scan resolves one blocked suspended variable. -/
def resolve (fuel : Nat) (blocked : List Nat) (sc : Suspended) : EnumerateM Symbol Guard (List Nat) := do
  pure ((← representative fuel sc.var) :: blocked)

/-- The inner scan records the canonical representative of the exact suspended variable. -/
theorem resolve_scan (values : List (UVarValue Symbol)) (roots : Nat → Nat)
    (fuel : Nat) (blocked result : List Nat) (sc : Suspended) (before after : State Symbol Guard)
    (valid : ScanValid values roots before) (success : Success (resolve fuel blocked sc) before result after) :
    ScanValid values roots after ∧ result = roots sc.var :: blocked := by
  unfold resolve at success
  obtain ⟨root, middle, read, final⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨validMiddle, rfl⟩ := representative_scan values roots before middle fuel sc.var root valid read
  obtain ⟨rfl, rfl⟩ := (success_pure (roots sc.var :: blocked) result middle after).mp final
  exact ⟨validMiddle, rfl⟩

/-- One source value-slot scan, with its index. -/
def collect (graph : Graph Symbol Guard) (fuel : Nat) :
    (List Nat × List Nat) → (UVarValue Symbol × Nat) → EnumerateM Symbol Guard (List Nat × List Nat)
  | (candidates, blocked), (value, index) => do
    match value with
    | .unenumerated _ scs =>
        let blocked ← scs.foldlM (resolve fuel) blocked
        pure (if candidate graph value then candidates ++ [index] else candidates, blocked)
    | _ => pure (candidates, blocked)

/-- The exact pure result of a slot scan under the representative map. -/
def collectPure (graph : Graph Symbol Guard) (roots : Nat → Nat) (accumulator : List Nat × List Nat)
    (entry : UVarValue Symbol × Nat) : List Nat × List Nat :=
  match entry.1 with
  | .unenumerated _ scs =>
      (if candidate graph entry.1 then accumulator.1 ++ [entry.2] else accumulator.1,
        scs.foldl (fun blocked sc => roots sc.var :: blocked) accumulator.2)
  | _ => accumulator

/-- The actual outer scan implements its pure summary and preserves every representative. -/
theorem collect_scan (graph : Graph Symbol Guard) (values : List (UVarValue Symbol)) (roots : Nat → Nat)
    (fuel : Nat) (accumulator result : List Nat × List Nat) (entry : UVarValue Symbol × Nat)
    (before after : State Symbol Guard) (valid : ScanValid values roots before)
    (success : Success (collect graph fuel accumulator entry) before result after) :
    ScanValid values roots after ∧ result = collectPure graph roots accumulator entry := by
  obtain ⟨candidates, blocked⟩ := accumulator
  obtain ⟨value, index⟩ := entry
  cases value with
  | eliminated | enumerated _ =>
      obtain ⟨rfl, rfl⟩ := (success_pure (candidates, blocked) result before after).mp success
      exact ⟨valid, rfl⟩
  | unenumerated node scs =>
      unfold collect at success
      obtain ⟨blockedResult, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨validMiddle, rfl⟩ := foldlM_exact (resolve fuel) (fun blocked sc => roots sc.var :: blocked)
        (ScanValid values roots)
        (fun blocked sc before result after valid success => resolve_scan values roots fuel blocked result sc before after valid success)
        scs blocked blockedResult before middle valid traversed
      obtain ⟨rfl, rfl⟩ := (success_pure _ result middle after).mp final
      exact ⟨validMiddle, rfl⟩

/-- The scheduler's pure result separates completed work from blocked work. -/
def offered (candidates blocked : List Nat) : Option (List Nat) :=
  if candidates.isEmpty then none else some (candidates.filter fun uv => !(uv ∈ blocked))

/-- Return the source's three-way work status from the completed scan. -/
def finishScan : List Nat × List Nat → EnumerateM Symbol Guard (Option (List Nat))
  | (candidates, blocked) =>
      if candidates.isEmpty then pure none else pure (some (candidates.filter fun uv => !(uv ∈ blocked)))

/-- Finishing the scan changes no state and computes its pure result. -/
theorem finishScan_success (summary : List Nat × List Nat) (before after : State Symbol Guard)
    (result : Option (List Nat)) :
    Success (finishScan summary) before result after ↔ result = offered summary.1 summary.2 ∧ after = before := by
  obtain ⟨candidates, blocked⟩ := summary
  by_cases empty : candidates.isEmpty = true
  · simpa [finishScan, offered, empty] using (success_pure none result before after)
  · simpa [finishScan, offered, empty] using
      (success_pure (some (candidates.filter fun uv => !(uv ∈ blocked))) result before after)

/-- The complete actual scan returns exactly its candidate-minus-blocked summary. -/
theorem findExpandable_exact (graph : Graph Symbol Guard) (fuel : Nat) (roots : Nat → Nat)
    (before after : State Symbol Guard) (result : Option (List Nat))
    (rootPaths : Roots before.representatives roots)
    (success : Success (findExpandable graph fuel) before result after) :
    ScanValid before.values roots after ∧
      result = let summary := before.values.zipIdx.foldl (collectPure graph roots) ([], [])
        offered summary.1 summary.2 := by
  unfold findExpandable at success
  change Success (get >>= fun state => do
    let summary ← state.values.zipIdx.foldlM (collect graph fuel) ([], [])
    finishScan summary) before result after at success
  obtain ⟨current, middle, read, continued⟩ := (success_bind _ _ _ _ _).mp success
  have readExact : current = before ∧ middle = before := by
    simpa [Success, get, getThe, MonadStateOf.get, StateT.get, pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using read
  obtain ⟨currentSame, middleSame⟩ := readExact
  subst current
  subst middle
  obtain ⟨summary, scanned, traversed, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨validScanned, rfl⟩ := foldlM_exact (collect graph fuel) (collectPure graph roots)
    (ScanValid before.values roots)
    (fun accumulator entry before result after valid success =>
      collect_scan graph _ roots fuel accumulator result entry before after valid success)
    before.values.zipIdx ([], []) summary before scanned ⟨rfl, rootPaths⟩ traversed
  obtain ⟨rfl, rfl⟩ := (finishScan_success _ scanned after result).mp final
  exact ⟨validScanned, rfl⟩

/-- Suspended references carried by one live pending slot. -/
def references : UVarValue Symbol → List Suspended
  | .unenumerated _ scs => scs
  | _ => []

/-- One candidate insertion adds exactly the current eligible slot index. -/
theorem collect_candidates (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (accumulator : List Nat × List Nat) (entry : UVarValue Symbol × Nat) (uv : Nat) :
    uv ∈ (collectPure graph roots accumulator entry).1 ↔
      uv ∈ accumulator.1 ∨ (uv = entry.2 ∧ candidate graph entry.1 = true) := by
  obtain ⟨value, index⟩ := entry
  cases value with
  | eliminated | enumerated _ => simp [collectPure, candidate]
  | unenumerated node scs =>
      by_cases chosen : candidate graph (.unenumerated node scs) = true
      · simp [collectPure, chosen]
      · simp [collectPure, chosen]

/-- Resolving references adds exactly their canonical representatives. -/
theorem resolve_members (roots : Nat → Nat) (scs : List Suspended) (blocked : List Nat) (uv : Nat) :
    uv ∈ scs.foldl (fun previous sc => roots sc.var :: previous) blocked ↔
      uv ∈ blocked ∨ ∃ sc ∈ scs, roots sc.var = uv := by
  induction scs generalizing blocked with
  | nil => simp
  | cons first rest ih =>
      simp only [List.foldl_cons, ih, List.mem_cons]
      clear ih
      grind only

/-- One value-slot scan records every incoming suspended representative. -/
theorem collect_blocked (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (accumulator : List Nat × List Nat) (entry : UVarValue Symbol × Nat) (uv : Nat) :
    uv ∈ (collectPure graph roots accumulator entry).2 ↔
      uv ∈ accumulator.2 ∨ ∃ sc ∈ references entry.1, roots sc.var = uv := by
  obtain ⟨value, index⟩ := entry
  cases value with
  | eliminated | enumerated _ => simp [collectPure, references]
  | unenumerated _ scs => exact resolve_members roots scs accumulator.2 uv

/-- The full candidate summary includes exactly the eligible scanned indices. -/
theorem candidates_exact (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (entries : List (UVarValue Symbol × Nat)) (accumulator : List Nat × List Nat) (uv : Nat) :
    uv ∈ (entries.foldl (collectPure graph roots) accumulator).1 ↔
      uv ∈ accumulator.1 ∨ ∃ entry ∈ entries, uv = entry.2 ∧ candidate graph entry.1 = true := by
  induction entries generalizing accumulator with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons, ih, collect_candidates, List.mem_cons]
      clear ih
      grind only

/-- The full blocked summary includes exactly the referenced representatives. -/
theorem blocked_exact (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (entries : List (UVarValue Symbol × Nat)) (accumulator : List Nat × List Nat) (uv : Nat) :
    uv ∈ (entries.foldl (collectPure graph roots) accumulator).2 ↔
      uv ∈ accumulator.2 ∨ ∃ entry ∈ entries, ∃ sc ∈ references entry.1, roots sc.var = uv := by
  induction entries generalizing accumulator with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons, ih, collect_blocked, List.mem_cons, or_and_right, exists_or, exists_eq_left, or_assoc]

/-- A returned candidate is present and its canonical index is not blocked. -/
theorem offered_member (candidates blocked available : List Nat) (uv : Nat)
    (result : offered candidates blocked = some available) (member : uv ∈ available) :
    uv ∈ candidates ∧ uv ∉ blocked := by
  unfold offered at result
  split at result
  · cases result
  · cases result
    simpa using List.mem_filter.mp member

/-- A live slot holds a value exactly when its index is a representative. -/
def IsRoot (forest : UnionFind.Forest) (uv : Nat) : Prop :=
  ∃ size, UnionFind.Reaches forest uv uv size

/-- Every allocated nonrepresentative is eliminated; every allocated representative is live. -/
def LiveRoots (state : State Symbol Guard) : Prop :=
  ∀ uv value, state.values[uv]? = some value → (value ≠ .eliminated ↔ IsRoot state.representatives uv)

/-- A representative map identifies both root indices and equivalence classes. -/
theorem root_iff (forest : UnionFind.Forest) (roots : Nat → Nat) (paths : Roots forest roots) (uv : Nat) :
    IsRoot forest uv ↔ roots uv = uv := by
  obtain ⟨size, path⟩ := paths uv
  constructor
  · rintro ⟨count, self⟩
    exact (UnionFind.reaches_unique path self).1
  · intro same
    exact ⟨size, by simpa [same] using path⟩

theorem class_iff (forest : UnionFind.Forest) (roots : Nat → Nat) (paths : Roots forest roots) (left right : Nat) :
    UnionFind.SameClass forest left right ↔ roots left = roots right := by
  obtain ⟨ls, leftPath⟩ := paths left
  obtain ⟨rs, rightPath⟩ := paths right
  exact UnionFind.sameClass_iff_roots leftPath rightPath

/-- Scanning preserves the exact live-representative invariant. -/
theorem scan_live (before after : State Symbol Guard) (roots : Nat → Nat)
    (paths : Roots before.representatives roots) (valid : ScanValid before.values roots after)
    (live : LiveRoots before) : LiveRoots after := by
  intro uv value stored
  rw [valid.values] at stored
  rw [live uv value stored, root_iff before.representatives roots paths uv,
    root_iff after.representatives roots valid.roots uv]

/-- An eligible candidate always has a live pending value. -/
theorem candidate_live (graph : Graph Symbol Guard) (value : UVarValue Symbol)
    (chosen : candidate graph value = true) : value ≠ .eliminated := by
  cases value <;> simp_all [candidate]

/-- Every actual offered variable is a live representative with no incoming suspended aliases. -/
theorem findExpandable_safe (graph : Graph Symbol Guard) (fuel : Nat)
    (before after : State Symbol Guard) (available : List Nat) (uv : Nat)
    (total : UnionFind.Total before.representatives) (live : LiveRoots before)
    (success : Success (findExpandable graph fuel) before (some available) after) (member : uv ∈ available) :
    LiveRoots after ∧ IsRoot after.representatives uv ∧
      (∃ value, after.values[uv]? = some value ∧ candidate graph value = true) ∧
      (∀ (index : Nat) (node : Option Nat) (scs : List Suspended), after.values[index]? = some (.unenumerated node scs) →
        Avoids after.representatives uv scs) := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  obtain ⟨scanned, result⟩ := findExpandable_exact graph fuel roots before after (some available) paths success
  have availableFacts := offered_member _ _ available uv result.symm member
  have candidateMember := (candidates_exact graph roots before.values.zipIdx ([], []) uv).mp availableFacts.1
  obtain ⟨entry, present, same, chosen⟩ := candidateMember.resolve_left (by simp)
  have stored : before.values[uv]? = some entry.1 := by
    simpa [same] using List.mem_zipIdx_iff_getElem?.mp present
  have rootBefore := (live uv entry.1 stored).mp (candidate_live graph entry.1 chosen)
  have fixed := (root_iff before.representatives roots paths uv).mp rootBefore
  refine ⟨scan_live before after roots paths scanned live,
    (root_iff after.representatives roots scanned.roots uv).mpr fixed,
    ⟨entry.1, by simpa [scanned.values] using stored, chosen⟩, ?_⟩
  intro index node scs read sc scMember related
  apply availableFacts.2
  apply (blocked_exact graph roots before.values.zipIdx ([], []) uv).mpr
  refine Or.inr ⟨(.unenumerated node scs, index), ?_, sc, scMember, ?_⟩
  · exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa [scanned.values] using read)
  · exact ((class_iff after.representatives roots scanned.roots uv sc.var).mp related).symm.trans fixed

/-- The initialized root is live and is its own representative. -/
theorem initial_live (root : Nat) : LiveRoots (initial root : State Symbol Guard) := by
  intro uv value stored
  cases uv with
  | zero =>
      simp [initial] at stored
      subst value
      refine ⟨fun _ => ⟨1, .root (UnionFind.read_initial [0] 0)⟩, ?_⟩
      simp
  | succ uv => simp [initial] at stored

/-- Every actual fresh allocation establishes a live singleton and retains older live slots. -/
theorem allocation_live (node : Option Nat) (before : State Symbol Guard)
    (storage : StorageValid before) (live : LiveRoots before) : LiveRoots (allocated node before) := by
  intro uv value stored
  by_cases earlier : uv < before.values.length
  · have old : before.values[uv]? = some value := by
      simpa [allocated, List.getElem?_append_left earlier] using stored
    exact live uv value old
  · have bound := (List.getElem?_eq_some_iff.mp stored).1
    have index : uv = before.counter := by
      have aligned := storage.aligned
      simp only [allocated, List.length_append, List.length_singleton] at bound
      unfold SupplyAligned at aligned
      omega
    subst uv
    have fresh : before.representatives before.counter = none :=
      outside_forest before.representatives before.counter before.counter storage.forest (by omega)
    have valueExact : value = .unenumerated node [] := by
      have aligned : before.counter = before.values.length := storage.aligned
      simpa [allocated, aligned] using stored.symm
    subst value
    refine ⟨fun _ => ⟨1, .root ?_⟩, ?_⟩
    · simp [allocated, UnionFind.read, fresh]
    · simp

/-- The root predicate is exactly the effective root tag in the source forest. -/
theorem isRoot_read (forest : UnionFind.Forest) (uv : Nat) :
    IsRoot forest uv ↔ ∃ size, UnionFind.read forest uv = .root size := by
  constructor
  · rintro ⟨size, path⟩
    exact ⟨size, UnionFind.reaches_terminal path⟩
  · rintro ⟨size, stored⟩
    exact ⟨size, .root stored⟩

/-- Path compression preserves which indices are representatives. -/
theorem findRoot_isRoot (forest : UnionFind.Forest) (valid : UnionFind.Total forest)
    (fuel uv : Nat) (found : UnionFind.Result) (result : UnionFind.findRoot fuel forest uv = some found)
    (other : Nat) : IsRoot found.forest other ↔ IsRoot forest other := by
  simp only [IsRoot, UnionFind.findRoot_reaches_iff valid result]

/-- The actual representative action preserves the live-slot invariant. -/
theorem representative_live (before after : State Symbol Guard) (fuel uv root : Nat)
    (total : UnionFind.Total before.representatives) (live : LiveRoots before)
    (success : Success (representative fuel uv) before root after) : LiveRoots after := by
  obtain ⟨found, lookup, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  intro other value stored
  rw [findRoot_isRoot before.representatives total fuel uv found lookup other]
  exact live other value stored

/-- Linking existing roots cannot create a root at any other address. -/
theorem link_no_new_root (forest : UnionFind.Forest) (loser winner ls ws : Nat)
    (different : loser ≠ winner) (winnerRoot : IsRoot forest winner) (uv : Nat)
    (root : IsRoot (UnionFind.link forest loser winner ls ws) uv) : IsRoot forest uv := by
  by_cases atWinner : uv = winner
  · simpa [atWinner] using winnerRoot
  · by_cases atLoser : uv = loser
    · obtain ⟨size, read⟩ := (isRoot_read _ _).mp root
      simp [UnionFind.link, UnionFind.read, UnionFind.put, atLoser, different] at read
    · obtain ⟨size, read⟩ := (isRoot_read _ _).mp root
      exact (isRoot_read forest uv).mpr ⟨size, by
        simpa [UnionFind.link, UnionFind.read, UnionFind.put, atWinner, atLoser] using read⟩

/-- The concrete union implementation only removes root indices. -/
theorem union_no_new_root (forest : UnionFind.Forest) (valid : UnionFind.Total forest)
    (fuel left right : Nat) (after : UnionFind.Forest)
    (result : UnionFind.union fuel fuel forest left right = some after) (uv : Nat)
    (root : IsRoot after uv) : IsRoot forest uv := by
  cases firstResult : UnionFind.findRoot fuel forest left with
  | none => simp [UnionFind.union, firstResult] at result
  | some first =>
      have firstTotal := UnionFind.findRoot_total valid firstResult
      cases secondResult : UnionFind.findRoot fuel first.forest right with
      | none => simp [UnionFind.union, firstResult, secondResult] at result
      | some second =>
          have liftRoot : IsRoot second.forest uv → IsRoot forest uv := fun h =>
            (findRoot_isRoot forest valid fuel left first firstResult uv).mp
              ((findRoot_isRoot first.forest firstTotal fuel right second secondResult uv).mp h)
          have rightPath := (UnionFind.findRoot_correct fuel first.forest right second secondResult).2
            (UnionFind.findRoot_correct fuel first.forest right second secondResult).1
          have leftPath := (UnionFind.findRoot_correct fuel first.forest right second secondResult).2
            ((UnionFind.findRoot_correct fuel forest left first firstResult).2
              (UnionFind.findRoot_correct fuel forest left first firstResult).1)
          have rightRoot : IsRoot second.forest second.representative :=
            ⟨second.size, .root (UnionFind.reaches_terminal rightPath)⟩
          have leftRoot : IsRoot second.forest first.representative :=
            ⟨first.size, .root (UnionFind.reaches_terminal leftPath)⟩
          simp only [UnionFind.union, firstResult, bind, Option.bind, secondResult] at result
          split at result
          · cases result; exact liftRoot root
          · rename_i different
            split at result
            · cases result
              exact liftRoot (link_no_new_root _ _ _ _ _ different rightRoot uv root)
            · cases result
              exact liftRoot (link_no_new_root _ _ _ _ _ (Ne.symm different) leftRoot uv root)

/-- Equality classes after the terminal unions join exactly the selected original classes. -/
def Joined (roots : Nat → Nat) (selected : List Nat) (forest : UnionFind.Forest) : Prop :=
  ∀ left right, UnionFind.SameClass forest left right ↔ roots left = roots right ∨
    (roots left ∈ selected ∧ roots right ∈ selected)

/-- Before any union, selecting one original class changes no equivalences. -/
theorem joined_single (forest : UnionFind.Forest) (roots : Nat → Nat) (paths : Roots forest roots) (first : Nat) :
    Joined roots [roots first] forest := by
  intro left right
  rw [class_iff forest roots paths left right]
  simp only [List.mem_singleton]
  constructor
  · exact Or.inl
  · rintro (same | ⟨hl, hr⟩)
    · exact same
    · exact hl.trans hr.symm

/-- Each actual union adds precisely the next selected original class. -/
theorem joined_union (forest : UnionFind.Forest) (valid : UnionFind.Total forest) (roots : Nat → Nat)
    (selected : List Nat) (joined : Joined roots selected forest) (fuel first next : Nat)
    (firstSelected : roots first ∈ selected) (after : UnionFind.Forest)
    (result : UnionFind.union fuel fuel forest first next = some after) :
    Joined roots (roots next :: selected) after := by
  intro left right
  rw [(UnionFind.union_correct valid result).2 left right]
  simp only [joined left right, joined left first, joined right next, joined left next, joined right first,
    List.mem_cons]
  clear joined
  grind only

/-- The terminal pre-scan records the exact old representatives before any unions. -/
theorem representatives_scan (values : List (UVarValue Symbol)) (roots : Nat → Nat)
    (fuel : Nat) (scs : List Suspended) (before after : State Symbol Guard) (recorded : List Nat)
    (valid : ScanValid values roots before)
    (success : Success (scs.mapM fun sc => representative fuel sc.var) before recorded after) :
    ScanValid values roots after ∧ recorded = scs.map (fun sc => roots sc.var) := by
  obtain ⟨preserved, related⟩ := mapM_sound (fun sc => representative fuel sc.var)
    (ScanValid values roots) (fun sc root => root = roots sc.var)
    (fun sc before root after valid success => representative_scan values roots before after fuel sc.var root valid success)
    scs before after recorded valid success
  exact ⟨preserved, all₂_map_eq _ _ _ related⟩

/-- Successful concrete union exposes its exact forest update and retains all values. -/
theorem unionVariables_success (fuel left right : Nat) (before after : State Symbol Guard) :
    Success (unionVariables fuel left right) before () after ↔
      ∃ forest, UnionFind.union fuel fuel before.representatives left right = some forest ∧
        after = {before with representatives := forest} := by
  cases result : UnionFind.union fuel fuel before.representatives left right with
  | none =>
      simp [Success, unionVariables, result, EnumerationState.failure, bind, get, getThe, MonadStateOf.get,
        pure, StateT.bind, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run]
  | some forest =>
      simp only [Success, union_exact fuel left right before forest result, ExceptT.run]
      simp

/-- The terminal union loop retains old slots while it joins the selected classes. -/
structure Merging (values : List (UVarValue Symbol)) (roots : Nat → Nat) (selected : List Nat)
    (state : State Symbol Guard) : Prop where
  values : state.values = values
  total : UnionFind.Total state.representatives
  joined : Joined roots selected state.representatives
  oldRoots : ∀ uv, IsRoot state.representatives uv → roots uv = uv

/-- The pre-scan establishes the union-loop invariant for the first selected class. -/
theorem merging_initial (values : List (UVarValue Symbol)) (roots : Nat → Nat)
    (state : State Symbol Guard) (first : Nat) (valid : ScanValid values roots state) :
    Merging values roots [roots first] state := by
  refine ⟨valid.values, ?_, joined_single state.representatives roots valid.roots first, ?_⟩
  · intro uv
    obtain ⟨size, path⟩ := valid.roots uv
    exact ⟨roots uv, size, path⟩
  · intro uv root
    exact (root_iff state.representatives roots valid.roots uv).mp root

/-- The actual next union extends the selected group and creates no new root indices. -/
theorem merging_step (values : List (UVarValue Symbol)) (roots : Nat → Nat) (selected : List Nat)
    (fuel first next : Nat) (before after : State Symbol Guard)
    (valid : Merging values roots selected before) (firstSelected : roots first ∈ selected)
    (success : Success (unionVariables fuel first next) before () after) :
    Merging values roots (roots next :: selected) after := by
  obtain ⟨forest, unionResult, rfl⟩ := (unionVariables_success fuel first next before after).mp success
  refine ⟨valid.values, (UnionFind.union_correct valid.total unionResult).1,
    joined_union before.representatives valid.total roots selected valid.joined fuel first next firstSelected forest unionResult, ?_⟩
  intro uv root
  exact valid.oldRoots uv (union_no_new_root before.representatives valid.total fuel first next forest unionResult uv root)

/-- The actual batched terminal unions join every selected class, including duplicates. -/
theorem terminal_unions (values : List (UVarValue Symbol)) (roots : Nat → Nat)
    (selected : List Nat) (fuel first : Nat) (rest : List Suspended) (before after : State Symbol Guard)
    (valid : Merging values roots selected before) (firstSelected : roots first ∈ selected)
    (success : Success (rest.forM fun sc => unionVariables fuel first sc.var) before () after) :
    Merging values roots (rest.foldl (fun selected sc => roots sc.var :: selected) selected) after := by
  induction rest generalizing selected before with
  | nil =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact valid
  | cons sc rest ih =>
      change Success (unionVariables fuel first sc.var >>= fun _ => rest.forM fun sc => unionVariables fuel first sc.var)
        before () after at success
      obtain ⟨ignored, middle, firstSuccess, continued⟩ := (success_bind _ _ _ _ _).mp success
      cases ignored
      have validMiddle := merging_step values roots selected fuel first sc.var before middle valid firstSelected firstSuccess
      exact ih (roots sc.var :: selected) middle validMiddle (by simp [firstSelected]) continued

/-- Once all selected classes are joined, only the winning selected root remains a root. -/
theorem joined_root_set (values : List (UVarValue Symbol)) (roots : Nat → Nat) (selected : List Nat)
    (state : State Symbol Guard) (valid : Merging values roots selected state) (first target count : Nat)
    (firstSelected : roots first ∈ selected)
    (path : UnionFind.Reaches state.representatives first target count) (uv : Nat) :
    IsRoot state.representatives uv ↔ roots uv = uv ∧ (uv ∉ selected ∨ uv = target) := by
  have targetRoot : IsRoot state.representatives target := ⟨count, .root (UnionFind.reaches_terminal path)⟩
  constructor
  · intro root
    have fixed := valid.oldRoots uv root
    refine ⟨fixed, ?_⟩
    by_cases member : uv ∈ selected
    · have related := (valid.joined first uv).mpr (Or.inr ⟨firstSelected, by simpa [fixed] using member⟩)
      obtain ⟨size, self⟩ := root
      have rootEqual := (UnionFind.sameClass_iff_roots path self).mp related
      exact Or.inr rootEqual.symm
    · exact Or.inl member
  · rintro ⟨fixed, unselected | rfl⟩
    · obtain ⟨representative, size, reached⟩ := valid.total uv
      have representativeRoot : IsRoot state.representatives representative :=
        ⟨size, .root (UnionFind.reaches_terminal reached)⟩
      have representativeFixed := valid.oldRoots representative representativeRoot
      have related := UnionFind.sameClass_root reached
      rcases (valid.joined uv representative).mp related with same | both
      · have sameIndex : representative = uv := by simpa [fixed, representativeFixed] using same.symm
        exact ⟨size, by simpa [sameIndex] using reached⟩
      · exact (unselected (by simpa [fixed] using both.1)).elim
    · exact targetRoot

/-- A slot contains a live value, independently of its current forest representative. -/
def LiveAt (values : List (UVarValue Symbol)) (uv : Nat) : Prop :=
  ∃ value, values[uv]? = some value ∧ value ≠ .eliminated

/-- Successful pending intersection always produces another pending value. -/
theorem intersection_pending (graph : Graph Symbol Guard) (left right merged : UVarValue Symbol)
    (result : intersectValues graph left right = some merged) :
    ∃ node scs, merged = .unenumerated node scs := by
  cases left <;> cases right <;> simp only [intersectValues] at result
  all_goals try cases result
  exact ⟨_, _, rfl⟩

/-- Pending assimilation retains the target and eliminates exactly the different source. -/
theorem assimilated_live (graph : Graph Symbol Guard) (before : State Symbol Guard) (target source : Nat)
    (sourceValue targetValue merged : UVarValue Symbol) (different : target ≠ source)
    (sourceRead : before.values[source]? = some sourceValue)
    (targetRead : before.values[target]? = some targetValue)
    (intersection : intersectValues graph sourceValue targetValue = some merged) (uv : Nat) :
    LiveAt (assimilated before target source merged).values uv ↔
      LiveAt before.values uv ∧ (uv ≠ source ∨ uv = target) := by
  have sourceBound := (List.getElem?_eq_some_iff.mp sourceRead).1
  have targetBound := (List.getElem?_eq_some_iff.mp targetRead).1
  have targetLive : targetValue ≠ .eliminated := by
    intro same
    simp [same, intersectValues] at intersection
  obtain ⟨node, scs, rfl⟩ := intersection_pending graph sourceValue targetValue merged intersection
  by_cases atSource : uv = source
  · subst uv
    simp [LiveAt, assimilated, sourceBound, Ne.symm different]
  · by_cases atTarget : uv = target
    · subst uv
      have targetElem := (List.getElem?_eq_some_iff.mp targetRead).2
      simp [LiveAt, assimilated, targetBound, different, Ne.symm different, targetElem, targetLive]
    · have frame := assimilation_frame before target source uv (.unenumerated node scs) atTarget atSource
      simp [LiveAt, frame, atSource]

/-- Every successful assimilation has the exact source-slot elimination effect, including duplicate roots. -/
theorem assimilate_effect (graph : Graph Symbol Guard) (before after : State Symbol Guard) (target source : Nat)
    (success : Success (EnumerationState.assimilate graph target source) before () after) :
    after.representatives = before.representatives ∧ after.values.length = before.values.length ∧
      (∀ uv, LiveAt after.values uv ↔ LiveAt before.values uv ∧ (uv ≠ source ∨ uv = target)) ∧
      (∀ uv, uv ≠ target → uv ≠ source → after.values[uv]? = before.values[uv]?) ∧
      after.counter = before.counter ∧ (StorageValid before → StorageValid after) := by
  by_cases same : target = source
  · subst source
    have equal : after = before := by
      simpa [Success, EnumerationState.assimilate, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
    subst after
    exact ⟨rfl, rfl, by intro uv; by_cases h : uv = target <;> simp [h], by intros; rfl, rfl, id⟩
  · cases sourceRead : before.values[source]? with
    | none =>
        simp [Success, EnumerationState.assimilate, same, rawValue, sourceRead, EnumerationState.failure,
          bind, get, getThe, MonadStateOf.get, pure, StateT.bind, StateT.get,
          ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
    | some sourceValue =>
        cases sourceValue with
        | eliminated =>
            have equal : after = before := by
              simpa [Success, EnumerationState.assimilate, same, rawValue, sourceRead,
                bind, get, getThe, MonadStateOf.get, pure, StateT.bind, StateT.pure, StateT.get,
                ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] using success
            subst after
            refine ⟨rfl, rfl, ?_, by intros; rfl, rfl, id⟩
            intro uv
            by_cases atSource : uv = source
            · simp [LiveAt, atSource, sourceRead]
            · simp [atSource]
        | enumerated fragment =>
            cases targetRead : before.values[target]? <;>
              simp [Success, EnumerationState.assimilate, same, rawValue, sourceRead, targetRead,
                intersectValues, EnumerationState.failure, bind, get, getThe, MonadStateOf.get, pure,
                StateT.bind, StateT.pure, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont,
                ExceptT.mk, ExceptT.run] at success
        | unenumerated sourceNode sourceScs =>
            cases targetRead : before.values[target]? with
            | none =>
                simp [Success, EnumerationState.assimilate, same, rawValue, sourceRead, targetRead,
                  EnumerationState.failure, bind, get, getThe, MonadStateOf.get, pure,
                  StateT.bind, StateT.pure, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont,
                  ExceptT.mk, ExceptT.run] at success
            | some targetValue =>
                cases targetValue with
                | eliminated | enumerated _ =>
                    simp [Success, EnumerationState.assimilate, same, rawValue, sourceRead, targetRead,
                      intersectValues, EnumerationState.failure, bind, get, getThe, MonadStateOf.get, pure,
                      StateT.bind, StateT.pure, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont,
                      ExceptT.mk, ExceptT.run] at success
                | unenumerated targetNode targetScs =>
                    let merged : UVarValue Symbol := .unenumerated (match sourceNode, targetNode with
                      | none, node => node | node, none => node | some a, some b => some (graph.intersect a b))
                      (sourceScs ++ targetScs)
                    have intersection : intersectValues graph (.unenumerated sourceNode sourceScs)
                        (.unenumerated targetNode targetScs) = some merged := by
                          cases sourceNode <;> cases targetNode <;> rfl
                    cases empty : hasEmptyContents graph merged with
                    | true =>
                        simp [Success, EnumerationState.assimilate, same, rawValue, sourceRead, targetRead,
                          intersection, empty, require, reject, bind, get, getThe, MonadStateOf.get, pure,
                          StateT.bind, StateT.pure, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont,
                          ExceptT.mk, ExceptT.run] at success
                    | false =>
                        have execution := assimilate_exact graph before target source sourceNode targetNode sourceScs
                          targetScs merged same sourceRead targetRead intersection empty
                        have equal : after = assimilated before target source merged := by
                          simpa [Success, execution, ExceptT.run] using success
                        subst after
                        refine ⟨rfl, by simp [assimilated], ?_, ?_, rfl, ?_⟩
                        · exact assimilated_live graph before target source _ _ merged same sourceRead targetRead intersection
                        · exact fun uv targetOther sourceOther => assimilation_frame before target source uv merged targetOther sourceOther
                        · intro valid
                          exact assimilation_storage graph before valid target source _ _ merged sourceRead targetRead intersection

/-- The actual assimilation loop eliminates every selected old root except the winner. -/
theorem terminal_assimilations (graph : Graph Symbol Guard) (target : Nat) (sources : List Nat)
    (before after : State Symbol Guard)
    (success : Success (sources.forM (EnumerationState.assimilate graph target)) before () after) :
    after.representatives = before.representatives ∧ after.values.length = before.values.length ∧
      ∀ uv, LiveAt after.values uv ↔ LiveAt before.values uv ∧ (uv ∉ sources ∨ uv = target) := by
  induction sources generalizing before with
  | nil =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact ⟨rfl, rfl, by simp⟩
  | cons source rest ih =>
      change Success (EnumerationState.assimilate graph target source >>= fun _ =>
        rest.forM (EnumerationState.assimilate graph target)) before () after at success
      obtain ⟨ignored, middle, firstSuccess, continued⟩ := (success_bind _ _ _ _ _).mp success
      cases ignored
      obtain ⟨firstForest, firstLength, firstSlots, _⟩ := assimilate_effect graph before middle target source firstSuccess
      obtain ⟨lastForest, lastLength, lastSlots⟩ := ih middle continued
      refine ⟨lastForest.trans firstForest, lastLength.trans firstLength, ?_⟩
      intro uv
      rw [lastSlots uv, firstSlots uv]
      simp only [List.mem_cons]
      grind only

/-- A stored slot is live exactly when its concrete value is not eliminated. -/
theorem liveAt_read (values : List (UVarValue Symbol)) (uv : Nat) (value : UVarValue Symbol)
    (stored : values[uv]? = some value) : LiveAt values uv ↔ value ≠ .eliminated := by
  simp [LiveAt, stored]

/-- The old live-slot facts follow from the source array and its canonical root map. -/
theorem old_live_roots (state : State Symbol Guard) (roots : Nat → Nat)
    (paths : Roots state.representatives roots) (live : LiveRoots state) (uv : Nat)
    (inside : uv < state.values.length) : LiveAt state.values uv ↔ roots uv = uv := by
  rw [liveAt_read state.values uv state.values[uv] (List.getElem?_eq_getElem inside),
    live uv state.values[uv] (List.getElem?_eq_getElem inside), root_iff state.representatives roots paths uv]

/-- Looking up the winning root retains the established joined-class description. -/
theorem merging_representative (values : List (UVarValue Symbol)) (roots : Nat → Nat) (selected : List Nat)
    (fuel uv target : Nat) (before after : State Symbol Guard) (valid : Merging values roots selected before)
    (success : Success (representative fuel uv) before target after) :
    Merging values roots selected after ∧ ∃ count, UnionFind.Reaches after.representatives uv target count := by
  obtain ⟨found, lookup, rfl, rfl⟩ := (representative_success fuel uv before after target).mp success
  refine ⟨⟨valid.values, UnionFind.findRoot_total valid.total lookup, ?_, ?_⟩, ?_⟩
  · intro left right
    exact (UnionFind.findRoot_classes valid.total lookup left right).trans (valid.joined left right)
  · intro other root
    exact valid.oldRoots other ((findRoot_isRoot before.representatives valid.total fuel uv found lookup other).mp root)
  · exact ⟨found.size, (UnionFind.findRoot_correct fuel before.representatives uv found lookup).2
      (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1⟩

/-- Joined root classes and actual source-slot elimination restore the complete live-root invariant. -/
theorem terminal_assimilation_live (graph : Graph Symbol Guard) (values : List (UVarValue Symbol))
    (roots : Nat → Nat) (selected sources : List Nat) (first target count : Nat)
    (before after : State Symbol Guard) (valid : Merging values roots selected before)
    (oldLive : ∀ uv < values.length, LiveAt values uv ↔ roots uv = uv)
    (sameSelected : ∀ uv, uv ∈ sources ↔ uv ∈ selected) (firstSelected : roots first ∈ selected)
    (path : UnionFind.Reaches before.representatives first target count)
    (success : Success (sources.forM (EnumerationState.assimilate graph target)) before () after) :
    LiveRoots after := by
  obtain ⟨forestSame, lengthSame, liveSlots⟩ := terminal_assimilations graph target sources before after success
  intro uv value stored
  have insideAfter := (List.getElem?_eq_some_iff.mp stored).1
  have insideOld : uv < values.length := by simpa [lengthSame, valid.values] using insideAfter
  rw [← liveAt_read after.values uv value stored, liveSlots uv, valid.values, oldLive uv insideOld,
    sameSelected uv, forestSame, joined_root_set values roots selected before valid first target count firstSelected path uv]

/-- The actual terminal branch before adding its reached node restriction. -/
def mergeTerminal (graph : Graph Symbol Guard) (fuel : Nat) (first : Suspended) (rest : List Suspended) :
    EnumerateM Symbol Guard Nat := do
  let recorded ← (first :: rest).mapM fun sc => representative fuel sc.var
  rest.forM fun sc => unionVariables fuel first.var sc.var
  let target ← representative fuel first.var
  recorded.forM (EnumerationState.assimilate graph target)
  pure target

/-- The actual terminal pre-scan, batched unions, winner lookup, and assimilation restore live representatives. -/
theorem mergeTerminal_valid (graph : Graph Symbol Guard) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat)
    (total : UnionFind.Total before.representatives) (live : LiveRoots before)
    (success : Success (mergeTerminal graph fuel first rest) before target after) :
    LiveRoots after ∧ UnionFind.Total after.representatives := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, preScan, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨scanValid, recordedSame⟩ := representatives_scan before.values roots fuel (first :: rest)
    before scanned recorded ⟨rfl, paths⟩ preScan
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have joined := terminal_unions before.values roots [roots first.var] fuel first.var rest scanned united
    (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resolvedValid, count, path⟩ := merging_representative before.values roots _ fuel first.var winner
    united resolved joined resolution
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨targetSame, stateSame⟩ := (success_pure winner target assimilated after).mp final
  subst target
  subst after
  have restored : LiveRoots assimilated := by
    apply terminal_assimilation_live graph before.values roots _ recorded first.var winner count resolved assimilated
      resolvedValid (old_live_roots before roots paths live)
    · intro uv
      rw [recordedSame, resolve_members roots rest [roots first.var] uv]
      simp [List.mem_map]
    · exact (resolve_members roots rest [roots first.var] (roots first.var)).mpr (Or.inl (by simp))
    · exact path
    · exact assimilation
  refine ⟨restored, ?_⟩
  rw [(terminal_assimilations graph winner recorded resolved assimilated assimilation).1]
  exact resolvedValid.total

/-- A node write stores a live pending value at an actual representative. -/
theorem nodeMerged_live (before : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (live : LiveRoots before) (fuel uv : Nat) (found : UnionFind.Result)
    (lookup : UnionFind.findRoot fuel before.representatives uv = some found) (node : Option Nat) (scs : List Suspended) :
    LiveRoots (nodeMerged before found (.unenumerated node scs)) := by
  have rootPath := (UnionFind.findRoot_correct fuel before.representatives uv found lookup).2
    (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1
  intro other value stored
  by_cases same : other = found.representative
  · subst other
    have valueSame : value = .unenumerated node scs := by
      have bound := (List.getElem?_eq_some_iff.mp stored).1
      simp only [nodeMerged, List.length_set] at bound
      simpa [nodeMerged, bound] using stored.symm
    subst value
    refine ⟨fun _ => ⟨found.size, .root (UnionFind.reaches_terminal rootPath)⟩, ?_⟩
    simp
  · have previous : before.values[other]? = some value := by
      simpa [nodeMerged, Ne.symm same] using stored
    rw [show (nodeMerged before found (.unenumerated node scs)).representatives = found.forest from rfl,
      findRoot_isRoot before.representatives total fuel uv found lookup other]
    exact live other value previous

/-- Successful source node merging preserves total representatives and live slots. -/
theorem mergeNode_live (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (total : UnionFind.Total before.representatives) (live : LiveRoots before)
    (success : Success (mergeNode graph fuel uv node scs) before () after) :
    LiveRoots after ∧ UnionFind.Total after.representatives ∧
      (∀ other, IsRoot after.representatives other ↔ IsRoot before.representatives other) ∧
      (∀ left right, UnionFind.SameClass after.representatives left right ↔ UnionFind.SameClass before.representatives left right) ∧
      (∀ held, ¬UnionFind.SameClass before.representatives held uv → after.values[held]? = before.values[held]?) ∧
      after.counter = before.counter ∧
      (StorageValid before → uv < before.counter → (∀ sc ∈ scs, sc.var < before.counter) → StorageValid after) := by
  cases lookup : UnionFind.findRoot fuel before.representatives uv with
  | none =>
      simp [Success, mergeNode, representative, lookup, EnumerationState.failure, bind, get, getThe, MonadStateOf.get,
        pure, StateT.bind, StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
  | some found =>
      cases stored : before.values[found.representative]? with
      | none =>
          simp [Success, mergeNode, representative, lookup, rawValue, stored, EnumerationState.failure,
            bind, get, getThe, MonadStateOf.get, set, pure, StateT.bind, StateT.pure, StateT.get, StateT.set,
            ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
      | some previous =>
          cases intersection : intersectValues graph (.unenumerated (some node) scs) previous with
          | none =>
              simp [Success, mergeNode, representative, lookup, rawValue, stored, intersection, EnumerationState.failure,
                bind, get, getThe, MonadStateOf.get, set, pure, StateT.bind, StateT.pure, StateT.get, StateT.set,
                ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
          | some merged =>
              cases empty : hasEmptyContents graph merged with
              | true =>
                  simp [Success, mergeNode, representative, lookup, rawValue, stored, intersection, empty, require, reject,
                    setValue, inheritAncestry, bind, get, getThe, MonadStateOf.get, set, pure, modify, modifyGet,
                    MonadStateOf.modifyGet, StateT.bind, StateT.pure, StateT.get, StateT.set, StateT.modifyGet,
                    ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run] at success
              | false =>
                  have execution := mergeNode_exact graph before fuel uv node scs found previous merged lookup stored intersection empty
                  have same : after = nodeMerged before found merged := by
                    simpa [Success, execution, ExceptT.run] using success
                  subst after
                  obtain ⟨mergedNode, mergedScs, rfl⟩ := intersection_pending graph _ previous merged intersection
                  exact ⟨nodeMerged_live before total live fuel uv found lookup mergedNode mergedScs,
                    UnionFind.findRoot_total total lookup,
                    findRoot_isRoot before.representatives total fuel uv found lookup,
                    UnionFind.findRoot_classes total lookup,
                    (fun held separate => mergeNode_frame before fuel uv held found (.unenumerated mergedNode mergedScs) separate lookup),
                    rfl, fun storage inside bounded => mergeNode_storage graph before storage fuel uv node inside scs bounded
                      found previous (.unenumerated mergedNode mergedScs) lookup stored intersection⟩

/-- The terminal branch of the actual node action is exactly the recorded merge followed by its node restriction. -/
theorem terminal_branch (graph : Graph Symbol Guard) (fuel node : Nat) (scs : List Suspended)
    (first : Suspended) (rest : List Suspended)
    (nonempty : graph.node node ≠ .empty)
    (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest) :
    enumerateNode graph (fuel + 1) scs node = (do
      let root ← mergeTerminal graph (fuel + 1) first rest
      mergeNode graph (fuel + 1) root node (scs.filter fun sc => !EqualityTrie.isTerminal sc.trie)
      pure (.hole root)) := by
  cases view : graph.node node with
  | empty => exact (nonempty view).elim
  | alternatives _ | recursive _ | unresolved _ =>
      simp [enumerateNode, view, terminal, mergeTerminal, bind_assoc]

/-- Every successful actual terminal node branch restores live representatives after adding its node restriction. -/
theorem enumerateNode_terminal_live (graph : Graph Symbol Guard) (fuel node : Nat) (scs : List Suspended)
    (first : Suspended) (rest : List Suspended) (before after : State Symbol Guard) (fragment : Fragment Symbol)
    (nonempty : graph.node node ≠ .empty)
    (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest)
    (total : UnionFind.Total before.representatives) (live : LiveRoots before)
    (success : Success (enumerateNode graph (fuel + 1) scs node) before fragment after) :
    LiveRoots after ∧ UnionFind.Total after.representatives := by
  rw [terminal_branch graph fuel node scs first rest nonempty terminal] at success
  obtain ⟨root, merged, mergeSuccess, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨liveMerged, totalMerged⟩ := mergeTerminal_valid graph (fuel + 1) first rest before merged root total live mergeSuccess
  obtain ⟨ignored, restricted, restriction, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨_, same⟩ := (success_pure (.hole root) fragment restricted after).mp final
  subst after
  have result := mergeNode_live graph (fuel + 1) root node _ merged restricted totalMerged liveMerged restriction
  exact ⟨result.1, result.2.1⟩

/-- The entire concrete assimilation loop leaves every separate protected slot unchanged. -/
theorem terminal_assimilations_frame (graph : Graph Symbol Guard) (target held : Nat) (sources : List Nat)
    (before after : State Symbol Guard) (notTarget : held ≠ target) (notSource : held ∉ sources)
    (success : Success (sources.forM (EnumerationState.assimilate graph target)) before () after) :
    after.values[held]? = before.values[held]? := by
  induction sources generalizing before with
  | nil =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      rfl
  | cons source rest ih =>
      change Success (EnumerationState.assimilate graph target source >>= fun _ =>
        rest.forM (EnumerationState.assimilate graph target)) before () after at success
      obtain ⟨ignored, middle, firstSuccess, continued⟩ := (success_bind _ _ _ _ _).mp success
      cases ignored
      have firstFrame := (assimilate_effect graph before middle target source firstSuccess).2.2.2.1
      have remaining : held ∉ rest := fun member => notSource (List.mem_cons_of_mem source member)
      have different : held ≠ source := fun same => notSource (by simp [same])
      exact (ih middle remaining continued).trans (firstFrame held notTarget different)

/-- The actual terminal merge retains an unrelated expanding root and all of its aliases. -/
theorem mergeTerminal_protected (graph : Graph Symbol Guard) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (held : Nat) (before after : State Symbol Guard) (target : Nat)
    (total : UnionFind.Total before.representatives) (heldRoot : IsRoot before.representatives held)
    (avoids : Avoids before.representatives held (first :: rest))
    (success : Success (mergeTerminal graph fuel first rest) before target after) :
    after.values[held]? = before.values[held]? ∧ IsRoot after.representatives held ∧
      ¬UnionFind.SameClass after.representatives held target ∧
      (∀ uv, UnionFind.SameClass after.representatives held uv ↔ UnionFind.SameClass before.representatives held uv) := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  have heldFixed := (root_iff before.representatives roots paths held).mp heldRoot
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, preScan, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨scanValid, recordedSame⟩ := representatives_scan before.values roots fuel (first :: rest)
    before scanned recorded ⟨rfl, paths⟩ preScan
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  let selected := rest.foldl (fun selected sc => roots sc.var :: selected) [roots first.var]
  have joined : Merging before.values roots selected united :=
    terminal_unions before.values roots [roots first.var] fuel first.var rest scanned united
      (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resolvedValid, count, path⟩ := merging_representative before.values roots selected fuel first.var winner
    united resolved joined resolution
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨targetSame, stateSame⟩ := (success_pure winner target assimilated after).mp final
  subst target
  subst after
  have sameSelected (uv : Nat) : uv ∈ recorded ↔ uv ∈ selected := by
    rw [recordedSame, resolve_members roots rest [roots first.var] uv]
    simp [List.mem_map]
  have firstSelected : roots first.var ∈ selected :=
    (resolve_members roots rest [roots first.var] (roots first.var)).mpr (Or.inl (by simp))
  have notRecorded : held ∉ recorded := by
    intro member
    rw [recordedSame] at member
    obtain ⟨sc, present, same⟩ := List.mem_map.mp member
    exact avoids sc present ((class_iff before.representatives roots paths held sc.var).mpr (heldFixed.trans same.symm))
  have notSelected : held ∉ selected := fun member => notRecorded ((sameSelected held).mpr member)
  have heldRootResolved := (joined_root_set before.values roots selected resolved resolvedValid first.var winner count
    firstSelected path held).mpr ⟨heldFixed, Or.inl notSelected⟩
  have winnerRoot : IsRoot resolved.representatives winner := ⟨count, .root (UnionFind.reaches_terminal path)⟩
  have winnerFixed := resolvedValid.oldRoots winner winnerRoot
  have winnerSelected : winner ∈ selected := by
    have related := (resolvedValid.joined first.var winner).mp (UnionFind.sameClass_root path)
    rcases related with same | both
    · simpa [winnerFixed, same] using firstSelected
    · simpa [winnerFixed] using both.2
  have different : held ≠ winner := fun same => notSelected (by simpa [same] using winnerSelected)
  have forestSame := (terminal_assimilations graph winner recorded resolved assimilated assimilation).1
  have preserved := terminal_assimilations_frame graph winner held recorded resolved assimilated different notRecorded assimilation
  refine ⟨preserved.trans (by rw [resolvedValid.values]), by simpa [forestSame] using heldRootResolved, ?_, ?_⟩
  · rw [forestSame]
    obtain ⟨heldCount, heldPath⟩ := heldRootResolved
    intro same
    exact different ((UnionFind.sameClass_iff_roots heldPath (.root (UnionFind.reaches_terminal path))).mp same)
  · intro uv
    rw [forestSame, resolvedValid.joined held uv, class_iff before.representatives roots paths held uv, heldFixed]
    simp [notSelected]

/-- The actual terminal node branch preserves the expanding root through its final node restriction. -/
theorem enumerateNode_terminal_protected (graph : Graph Symbol Guard) (fuel node : Nat) (scs : List Suspended)
    (first : Suspended) (rest : List Suspended) (held : Nat) (before after : State Symbol Guard)
    (fragment : Fragment Symbol) (nonempty : graph.node node ≠ .empty)
    (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest)
    (total : UnionFind.Total before.representatives) (live : LiveRoots before)
    (heldRoot : IsRoot before.representatives held) (avoids : Avoids before.representatives held scs)
    (success : Success (enumerateNode graph (fuel + 1) scs node) before fragment after) :
    after.values[held]? = before.values[held]? ∧ IsRoot after.representatives held ∧
      (∀ uv, UnionFind.SameClass after.representatives held uv ↔ UnionFind.SameClass before.representatives held uv) ∧
      ∃ root, fragment = .hole root ∧ ¬UnionFind.SameClass after.representatives held root := by
  have selectedAvoid : Avoids before.representatives held (first :: rest) := by
    intro sc member
    rw [← terminal] at member
    exact avoids sc (List.mem_filter.mp member).1
  rw [terminal_branch graph fuel node scs first rest nonempty terminal] at success
  obtain ⟨root, merged, mergeSuccess, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨liveMerged, totalMerged⟩ := mergeTerminal_valid graph (fuel + 1) first rest before merged root total live mergeSuccess
  obtain ⟨mergeFrame, heldMerged, separated, mergeClasses⟩ :=
    mergeTerminal_protected graph (fuel + 1) first rest held before merged root total heldRoot selectedAvoid mergeSuccess
  obtain ⟨ignored, restricted, restriction, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨fragmentSame, stateSame⟩ := (success_pure (.hole root) fragment restricted after).mp final
  subst fragment
  subst after
  obtain ⟨_, _, rootPreserved, classPreserved, frame, _, _⟩ :=
    mergeNode_live graph (fuel + 1) root node _ merged restricted totalMerged liveMerged restriction
  exact ⟨(frame held separated).trans mergeFrame, (rootPreserved held).mpr heldMerged,
    fun uv => (classPreserved held uv).trans (mergeClasses uv),
    root, rfl, fun same => separated ((classPreserved held root).mp same)⟩

/-- The terminal operations retain one fixed allocation domain. -/
def Stable (limit : Nat) (state : State Symbol Guard) : Prop := StorageValid state ∧ state.counter = limit

/-- An actual bounded representative lookup retains storage safety and returns an allocated root. -/
theorem representative_stable (limit fuel uv root : Nat) (before after : State Symbol Guard)
    (valid : Stable limit before) (inside : uv < limit)
    (success : Success (representative fuel uv) before root after) : Stable limit after ∧ root < limit := by
  obtain ⟨found, lookup, rfl, rfl⟩ := (representative_success fuel uv before after root).mp success
  have uvBound : uv < before.counter := by simpa [valid.2] using inside
  refine ⟨⟨representative_storage before valid.1 fuel uv uvBound found lookup, valid.2⟩, ?_⟩
  simpa [valid.2] using (findRoot_bounded fuel before.representatives before.counter uv valid.1.forest uvBound found lookup).1

/-- Actual terminal union retains the fixed allocation domain. -/
theorem union_stable (limit fuel left right : Nat) (before after : State Symbol Guard)
    (valid : Stable limit before) (leftInside : left < limit) (rightInside : right < limit)
    (success : Success (unionVariables fuel left right) before () after) : Stable limit after := by
  obtain ⟨forest, result, rfl⟩ := (unionVariables_success fuel left right before after).mp success
  exact ⟨union_storage before valid.1 fuel left right (by simpa [valid.2] using leftInside)
    (by simpa [valid.2] using rightInside) forest result, valid.2⟩

/-- Actual assimilation retains all storage bounds without allocation. -/
theorem assimilation_stable (graph : Graph Symbol Guard) (limit target source : Nat)
    (before after : State Symbol Guard) (valid : Stable limit before)
    (success : Success (EnumerationState.assimilate graph target source) before () after) : Stable limit after := by
  have effect := assimilate_effect graph before after target source success
  exact ⟨effect.2.2.2.2.2 valid.1, effect.2.2.2.2.1.trans valid.2⟩

/-- A source `forM` loop composes its verified invariant at each actual element. -/
theorem forM_invariant (action : α → EnumerateM Symbol Guard Unit) (invariant : State Symbol Guard → Prop)
    (inputs : List α)
    (step : ∀ input ∈ inputs, ∀ before after, invariant before → Success (action input) before () after → invariant after)
    (before after : State Symbol Guard) (valid : invariant before)
    (success : Success (inputs.forM action) before () after) : invariant after := by
  induction inputs generalizing before with
  | nil =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact valid
  | cons input rest ih =>
      change Success (action input >>= fun _ => rest.forM action) before () after at success
      obtain ⟨ignored, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      cases ignored
      have validMiddle := step input (by simp) before middle valid first
      exact ih (fun input member => step input (List.mem_cons_of_mem _ member)) middle validMiddle continued

/-- A source `mapM` loop composes an invariant with element membership available to each local proof. -/
theorem mapM_invariant (action : α → EnumerateM Symbol Guard β) (invariant : State Symbol Guard → Prop)
    (inputs : List α)
    (step : ∀ input ∈ inputs, ∀ before output after, invariant before → Success (action input) before output after → invariant after)
    (before after : State Symbol Guard) (outputs : List β) (valid : invariant before)
    (success : Success (inputs.mapM action) before outputs after) : invariant after := by
  induction inputs generalizing before outputs with
  | nil =>
      obtain ⟨rfl, rfl⟩ := (success_pure [] outputs before after).mp success
      exact valid
  | cons input rest ih =>
      rw [List.mapM_cons] at success
      obtain ⟨output, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      have validMiddle := step input (by simp) before output middle valid first
      obtain ⟨tail, last, remaining, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨_, lastSame⟩ := (success_pure (output :: tail) outputs last after).mp final
      subst after
      exact ih (fun input member => step input (List.mem_cons_of_mem _ member)) middle tail validMiddle remaining

/-- The complete terminal merge preserves bounded storage and returns an allocated variable. -/
theorem mergeTerminal_storage (graph : Graph Symbol Guard) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat) (storage : StorageValid before)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.counter)
    (success : Success (mergeTerminal graph fuel first rest) before target after) :
    StorageValid after ∧ after.counter = before.counter ∧ target < after.counter := by
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, preScan, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scanStable := mapM_invariant (fun sc => representative fuel sc.var) (Stable before.counter) (first :: rest)
    (fun sc member before root after valid success =>
      (representative_stable _ fuel sc.var root before after valid (bounded sc member) success).1)
    before scanned recorded ⟨storage, rfl⟩ preScan
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unitedStable := forM_invariant (fun sc => unionVariables fuel first.var sc.var) (Stable before.counter) rest
    (fun sc member before after valid success => union_stable _ fuel first.var sc.var before after valid
      (bounded first (by simp)) (bounded sc (List.mem_cons_of_mem _ member)) success)
    scanned united scanStable unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resolvedStable, winnerBound⟩ := representative_stable before.counter fuel first.var winner united resolved unitedStable
    (bounded first (by simp)) resolution
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have assimilatedStable := forM_invariant (EnumerationState.assimilate graph winner) (Stable before.counter) recorded
    (fun source _ before after valid success => assimilation_stable graph _ winner source before after valid success)
    resolved assimilated resolvedStable assimilation
  obtain ⟨targetSame, stateSame⟩ := (success_pure winner target assimilated after).mp final
  subst target
  subst after
  exact ⟨assimilatedStable.1, assimilatedStable.2, by simpa [assimilatedStable.2] using winnerBound⟩

/-- Storage bounds and the live-representative invariant at a completed local action. -/
def Safe (state : State Symbol Guard) : Prop := StorageValid state ∧ LiveRoots state

/-- A successful terminal node branch preserves all local safety facts without allocation. -/
theorem enumerateNode_terminal_safe (graph : Graph Symbol Guard) (fuel node : Nat) (scs : List Suspended)
    (first : Suspended) (rest : List Suspended) (before after : State Symbol Guard) (fragment : Fragment Symbol)
    (nonempty : graph.node node ≠ .empty)
    (terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest)
    (safe : Safe before) (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (success : Success (enumerateNode graph (fuel + 1) scs node) before fragment after) :
    Safe after ∧ after.counter = before.counter ∧ FragmentBound after.counter fragment := by
  have selectedBound : ∀ sc ∈ first :: rest, sc.var < before.counter := by
    intro sc member
    rw [← terminal] at member
    exact bounded sc (List.mem_filter.mp member).1
  rw [terminal_branch graph fuel node scs first rest nonempty terminal] at success
  obtain ⟨root, merged, mergeSuccess, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨liveMerged, totalMerged⟩ := mergeTerminal_valid graph (fuel + 1) first rest before merged root safe.1.total safe.2 mergeSuccess
  obtain ⟨storageMerged, counterMerged, rootBound⟩ :=
    mergeTerminal_storage graph (fuel + 1) first rest before merged root safe.1 selectedBound mergeSuccess
  obtain ⟨ignored, restricted, restriction, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨fragmentSame, stateSame⟩ := (success_pure (.hole root) fragment restricted after).mp final
  subst fragment
  subst after
  obtain ⟨liveAfter, _, _, _, _, counterAfter, storageAfter⟩ :=
    mergeNode_live graph (fuel + 1) root node _ merged restricted totalMerged liveMerged restriction
  have descendants : ∀ sc ∈ scs.filter (fun sc => !EqualityTrie.isTerminal sc.trie), sc.var < merged.counter := by
    intro sc member
    rw [counterMerged]
    exact bounded sc (List.mem_filter.mp member).1
  refine ⟨⟨storageAfter storageMerged rootBound descendants, liveAfter⟩, counterAfter.trans counterMerged, ?_⟩
  simpa [FragmentBound, counterAfter] using rootBound

/-- Constraint descent retains the variable bounds of its input list. -/
theorem descend_bounded (limit index : Nat) (scs : List Suspended) (bounded : ∀ sc ∈ scs, sc.var < limit) :
    ∀ sc ∈ descendScs index scs, sc.var < limit := by
  intro sc member
  simp only [descendScs, EqualityTrie.descendScs, List.mem_filter, List.mem_map] at member
  obtain ⟨⟨original, present, rfl⟩, _⟩ := member
  exact bounded original present

/-- The actual class-allocation traversal increases the supply by its list length. -/
theorem suspended_counter (count : Nat) (state : State Symbol Guard) :
    (suspendedState count state).counter = state.counter + count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simpa [suspendedState, allocated, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (allocated none state)

/-- All consecutive suspended variables lie inside the extended allocation domain. -/
theorem suspended_bounded (start : Nat) (tries : List EqualityTrie.Trie) :
    ∀ sc ∈ suspendedVars start tries, sc.var < start + tries.length := by
  intro sc member
  have listed : sc.var ∈ (suspendedVars start tries).map EqualityTrie.Suspended.var := List.mem_map.mpr ⟨sc, member, rfl⟩
  rw [suspendedVars_variables] at listed
  obtain ⟨index, inside, same⟩ := List.mem_range'.mp listed
  omega

/-- Actual class allocation preserves both local invariants. -/
theorem suspension_safe (count : Nat) (state : State Symbol Guard) (safe : Safe state) : Safe (suspendedState count state) := by
  induction count generalizing state with
  | zero => exact safe
  | succ count ih => exact ih (allocated none state) ⟨allocation_storage none state safe.1, allocation_live none state safe.1 safe.2⟩

/-- A successful source guard only accepts its true condition and leaves the state unchanged. -/
theorem require_success (condition : Bool) (before after : State Symbol Guard) :
    Success (require condition) before () after ↔ condition = true ∧ after = before := by
  cases condition <;> simp [Success, require, reject, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

/-- A source alternative choice returns a listed edge with the original state. -/
theorem choose_success (values : List α) (before after : State Symbol Guard) (value : α) :
    Success (choose values) before value after ↔ value ∈ values ∧ after = before := by
  simp only [Success, choose, ExceptT.run, List.mem_map]
  constructor
  · rintro ⟨chosen, member, same⟩
    cases same
    exact ⟨member, rfl⟩
  · rintro ⟨member, rfl⟩
    exact ⟨value, member, rfl⟩

/-- A rejecting action has no successful branch. -/
theorem reject_unsuccessful (before after : State Symbol Guard) (value : α) : ¬Success reject before value after := by
  simp [Success, reject, ExceptT.run]

/-- The residual-recording clause of actual edge enumeration. -/
def recordResidual (residual : Option Guard) (fragment : Fragment Symbol) : EnumerateM Symbol Guard Unit :=
  match residual with
  | none => pure ()
  | some guard => modify fun state => {state with obligations := (guard, fragment) :: state.obligations}

/-- Residual recording preserves safety when the guarded fragment refers only to allocated variables. -/
theorem recordResidual_safe (residual : Option Guard) (fragment : Fragment Symbol)
    (before after : State Symbol Guard) (safe : Safe before) (bounded : FragmentBound before.counter fragment)
    (success : Success (recordResidual residual fragment) before () after) : Safe after ∧ after.counter = before.counter := by
  cases residual with
  | none =>
      obtain ⟨_, same⟩ := (success_pure () () before after).mp success
      subst after
      exact ⟨safe, rfl⟩
  | some guard =>
      have same : after = {before with obligations := (guard, fragment) :: before.obligations} := by
        simpa [Success, recordResidual, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using success
      subst after
      exact ⟨⟨guard_storage before safe.1 guard fragment bounded, safe.2⟩, rfl⟩

/-- Growing child traversal retains each fragment bound through later allocations. -/
theorem mapM_growing (action : α → EnumerateM Symbol Guard (Fragment Symbol)) (inputs : List α) (limit : Nat)
    (step : ∀ input ∈ inputs, ∀ before after fragment, Safe before → limit ≤ before.counter →
      Success (action input) before fragment after → Safe after ∧ before.counter ≤ after.counter ∧ FragmentBound after.counter fragment)
    (before after : State Symbol Guard) (fragments : List (Fragment Symbol))
    (safe : Safe before) (initialBound : limit ≤ before.counter)
    (success : Success (inputs.mapM action) before fragments after) :
    Safe after ∧ before.counter ≤ after.counter ∧ FragmentsBound after.counter fragments := by
  induction inputs generalizing before fragments with
  | nil =>
      obtain ⟨rfl, rfl⟩ := (success_pure [] fragments before after).mp success
      exact ⟨safe, Nat.le_refl _, trivial⟩
  | cons input rest ih =>
      rw [List.mapM_cons] at success
      obtain ⟨fragment, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨safeMiddle, growthMiddle, boundedFragment⟩ := step input (by simp) before middle fragment safe initialBound first
      obtain ⟨tail, last, remaining, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨fragmentsSame, afterSame⟩ := (success_pure (fragment :: tail) fragments last after).mp final
      subst fragments
      subst after
      obtain ⟨safeLast, growthLast, boundedTail⟩ := ih (fun input member => step input (List.mem_cons_of_mem _ member))
        middle tail safeMiddle (Nat.le_trans initialBound growthMiddle) remaining
      exact ⟨safeLast, Nat.le_trans growthMiddle growthLast,
        fragmentBound_mono middle.counter last.counter growthLast fragment boundedFragment, boundedTail⟩

/-- The source edge equation exposes its common residual-recording action. -/
theorem edge_action (graph : Graph Symbol Guard) (fuel : Nat) (scs : List Suspended) (edge : EnumerationState.Edge Symbol Guard) :
    enumerateEdge graph (fuel + 1) scs edge = (do
      require (arityAllows edge.children.length scs)
      let added ← edge.equalities.mapM suspend
      let children ← edge.children.zipIdx.mapM fun entry => enumerateNode graph fuel (descendScs entry.2 (scs ++ added)) entry.1
      let fragment := Fragment.node edge.symbol children
      recordResidual edge.residual fragment
      pure fragment) := by
  cases residual : edge.residual <;> simp [enumerateEdge, recordResidual, residual]

/-- Every successful node or edge traversal preserves reachable-state safety and bounds its returned holes. -/
theorem enumeration_safety (graph : Graph Symbol Guard) (fuel : Nat) :
    (∀ scs node (before after : State Symbol Guard) fragment, Safe before →
      (∀ sc ∈ scs, sc.var < before.counter) →
      Success (enumerateNode graph fuel scs node) before fragment after →
      Safe after ∧ before.counter ≤ after.counter ∧ FragmentBound after.counter fragment) ∧
    (∀ scs edge (before after : State Symbol Guard) fragment, Safe before →
      (∀ sc ∈ scs, sc.var < before.counter) →
      Success (enumerateEdge graph fuel scs edge) before fragment after →
      Safe after ∧ before.counter ≤ after.counter ∧ FragmentBound after.counter fragment) := by
  induction fuel with
  | zero =>
      constructor
      · intro scs node before after fragment _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
      · intro scs edge before after fragment _ _ success
        exact (success_failure .fuelExhausted before after fragment success).elim
  | succ fuel ih =>
      constructor
      · intro scs node before after fragment safe bounded success
        cases view : graph.node node with
        | empty =>
            have impossible : Success reject before fragment after := by simpa [enumerateNode, view] using success
            exact (reject_unsuccessful before after fragment impossible).elim
        | alternatives edges | recursive body | unresolved reference =>
            cases terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) with
            | cons first rest =>
                have nonempty : graph.node node ≠ .empty := by simp [view]
                obtain ⟨safeAfter, sameCounter, boundedFragment⟩ := enumerateNode_terminal_safe graph fuel node scs first rest
                  before after fragment nonempty terminal safe bounded success
                exact ⟨safeAfter, Nat.le_of_eq sameCounter.symm, boundedFragment⟩
            | nil =>
                simp only [enumerateNode, view, terminal] at success
                first
                | exact (success_failure .unresolvedReference before after fragment success).elim
                | (obtain ⟨edge, middle, choice, continued⟩ := (success_bind _ _ _ _ _).mp success
                   obtain ⟨_, same⟩ := (choose_success _ before middle edge).mp choice
                   subst middle
                   exact ih.2 scs edge before after fragment safe bounded continued)
                | (obtain ⟨uv, middle, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
                   have allocatedExact : uv = before.counter ∧ middle = allocated (some node) before := by
                     simpa [Success, allocate_exact, ExceptT.run] using allocation
                   obtain ⟨uvSame, middleSame⟩ := allocatedExact
                   subst uv
                   subst middle
                   obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.hole before.counter) fragment (allocated (some node) before) after).mp final
                   subst fragment
                   subst after
                   exact ⟨⟨allocation_storage (some node) before safe.1, allocation_live (some node) before safe.1 safe.2⟩,
                     by simp [allocated], by simp [allocated, FragmentBound]⟩)
      · intro scs edge before after fragment safe bounded success
        rw [edge_action graph fuel scs edge] at success
        obtain ⟨ignored, checked, required, continued⟩ := (success_bind _ _ _ _ _).mp success
        cases ignored
        obtain ⟨_, same⟩ := (require_success _ before checked).mp required
        subst checked
        obtain ⟨added, suspended, suspension, continued⟩ := (success_bind _ _ _ _ _).mp continued
        have suspensionExact : added = suspendedVars before.counter edge.equalities ∧
            suspended = suspendedState edge.equalities.length before := by
          simpa [Success, suspendMany_exact, ExceptT.run] using suspension
        obtain ⟨addedSame, suspendedSame⟩ := suspensionExact
        subst added
        subst suspended
        let start := suspendedState edge.equalities.length before
        have startSafe : Safe start := suspension_safe edge.equalities.length before safe
        have startGrowth : before.counter ≤ start.counter := by simp [start, suspended_counter]
        have scsBound : ∀ sc ∈ scs ++ suspendedVars before.counter edge.equalities, sc.var < start.counter := by
          intro sc member
          rcases List.mem_append.mp member with old | fresh
          · exact Nat.lt_of_lt_of_le (bounded sc old) startGrowth
          · simpa [start, suspended_counter] using suspended_bounded before.counter edge.equalities sc fresh
        obtain ⟨children, expanded, traversed, continued⟩ := (success_bind _ _ _ _ _).mp continued
        have childStep : ∀ entry ∈ edge.children.zipIdx, ∀ previous next child, Safe previous → start.counter ≤ previous.counter →
            Success (enumerateNode graph fuel (descendScs entry.2 (scs ++ suspendedVars before.counter edge.equalities)) entry.1) previous child next →
            Safe next ∧ previous.counter ≤ next.counter ∧ FragmentBound next.counter child := by
          intro entry member previous next child safePrevious initialBound childSuccess
          apply ih.1 _ entry.1 previous next child safePrevious
          · apply descend_bounded previous.counter entry.2 (scs ++ suspendedVars before.counter edge.equalities)
            intro sc scMember
            exact Nat.lt_of_lt_of_le (scsBound sc scMember) initialBound
          · exact childSuccess
        obtain ⟨expandedSafe, expandedGrowth, childrenBound⟩ := mapM_growing
          (fun entry => enumerateNode graph fuel (descendScs entry.2 (scs ++ suspendedVars before.counter edge.equalities)) entry.1)
          edge.children.zipIdx start.counter childStep start expanded children startSafe (Nat.le_refl _) traversed
        obtain ⟨ignored, guarded, guardedSuccess, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have termBound : FragmentBound expanded.counter (.node edge.symbol children) := childrenBound
        obtain ⟨guardedSafe, guardedCounter⟩ := recordResidual_safe edge.residual (.node edge.symbol children)
          expanded guarded expandedSafe termBound guardedSuccess
        obtain ⟨fragmentSame, afterSame⟩ := (success_pure (.node edge.symbol children) fragment guarded after).mp final
        subst fragment
        subst after
        exact ⟨guardedSafe, by rw [guardedCounter]; exact Nat.le_trans startGrowth expandedGrowth,
          by simpa [guardedCounter] using termBound⟩

end MicroCFTA.EnumerationSchedule
