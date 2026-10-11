import MicroCFTA.Minimization
import MicroCFTA.Productivity

/-!
# Similarity inference and the complete finite minimization schedule

Finite lists represent ordered maps and sets. Transition addresses retain the
input table's ordinals while the schedule changes its rows. Guard payloads
use identifiers; the source's read classification depends only on guard shape
and paths. Final guard-structure validation is an explicit callback boundary.
-/
namespace MicroCFTA.MinimizeSchedule

open Language

abbrev Path := List Nat

/-- Source guard shapes needed by the minimizer's read classification. -/
inductive Guard where
  | top | bottom
  | same (left right : Path)
  | entails (left right : Path)
  | satisfies (path : Path) (formula : Nat)
  | holds (paths : List Path) (formula : Nat)
  | structural (paths : List Path) (scope : Nat)
  | not (inner : Guard)
  | and (left right : Guard)
  | or (left right : Guard)
  deriving DecidableEq, Repr

/-- Positive equality classes and a residual guard. -/
structure Constraint where
  equalities : List (List Path)
  guard : Guard
  deriving DecidableEq, Repr

/-- The exact syntactic unconstrained value. -/
def noConstraint : Constraint := ⟨[], .top⟩

/-- An explicit transition. Symbol and refinement identifiers preserve label equality. -/
structure Transition where
  symbol : Nat
  refinement : Nat
  children : List Nat
  constraint : Constraint
  deriving DecidableEq, Repr

abbrev Rows := List (Nat × List Transition)

/-- Stable transition address in the original table. -/
structure Address where
  node : Nat
  ordinal : Nat
  deriving DecidableEq, Repr

/-- A directed subtype-to-supertype pair. -/
structure Pair where
  low : Address
  high : Address
  deriving DecidableEq, Repr

/-- A selected supertype transition and its transitive representative. -/
structure Replacement where
  removed : Address
  retained : Address
  deriving DecidableEq, Repr

/-- Read one row, returning no alternatives for an absent state. -/
def row (rows : Rows) (state : Nat) : List Transition :=
  ((rows.find? fun entry => entry.1 == state).map Prod.snd).getD []

/-- Look up an original transition by its stable address. -/
def transitionAt (rows : Rows) (address : Address) : Option Transition := (row rows address.node)[address.ordinal]?

/-- Update an existing table row. -/
def adjust (rows : Rows) (state : Nat) (update : List Transition → List Transition) : Rows :=
  rows.map fun (name, transitions) => (name, if name = state then update transitions else transitions)

/-- The paths inspected by a guard. Structural scopes include all nested read paths. -/
def guardPaths : Guard → List Path
  | .top | .bottom => []
  | .same left right | .entails left right => [left, right]
  | .satisfies path _ => [path]
  | .holds paths _ | .structural paths _ => paths
  | .not inner => guardPaths inner
  | .and left right | .or left right => guardPaths left ++ guardPaths right

/-- Every path inspected by either constraint component. -/
def constraintPaths (constraint : Constraint) : List Path :=
  (constraint.equalities.flatten ++ guardPaths constraint.guard).eraseDups

/-- Monotone, sensitive, and whole-subtree reads. -/
structure Reads where
  monotone : List Path := []
  sensitive : List Path := []
  structural : List Path := []
  deriving DecidableEq, Repr

/-- Union read sets. Duplicates have no semantic effect on membership tests. -/
def Reads.union (left right : Reads) : Reads :=
  ⟨(left.monotone ++ right.monotone).eraseDups, (left.sensitive ++ right.sensitive).eraseDups,
    (left.structural ++ right.structural).eraseDups⟩

/-- The source's polarity-sensitive guard read classification. -/
def guardReads : Bool → Guard → Reads
  | _, .satisfies path _ => ⟨[path], [], []⟩
  | _, .holds paths _ => ⟨paths.eraseDups, [], []⟩
  | true, .entails left right => ⟨[left], [right], []⟩
  | false, .entails left right => ⟨[], [left, right], []⟩
  | positive, .not inner => guardReads (!positive) inner
  | positive, .and left right | positive, .or left right =>
      (guardReads positive left).union (guardReads positive right)
  | _, other => ⟨[], [], (guardPaths other).eraseDups⟩

/-- Sort and deduplicate a finite state set. -/
def stateSet (states : List Nat) : List Nat := states.eraseDups.mergeSort (· ≤ ·)

/-- Fixed-point iteration on a finite graph. The caller supplies a sufficient finite bound. -/
def grow (step : List Nat → List Nat) : Nat → List Nat → List Nat
  | 0, known => known
  | fuel + 1, known =>
      let next := stateSet (step known)
      if next = known then known else grow step fuel next

/-- States with a finite structural derivation. Guards are not evaluated. -/
def productiveStates (rows : Rows) : List Nat :=
  grow (fun known => rows.filterMap fun (state, transitions) =>
    if transitions.any (fun edge => edge.children.all (· ∈ known)) then some state else none)
    (rows.length + 1) []

/-- Forward reachability through transition children and optional redirect dependencies. -/
def reachable (rows : Rows) (redirects : List (Nat × Nat)) (start : List Nat) : List Nat :=
  grow (fun known => known ++ known.flatMap fun state =>
    (redirects.filterMap fun (source, destination) => if source = state then some destination else none) ++
      (row rows state).flatMap Transition.children) (rows.length + 1) (stateSet start)

/-- No transition at or below the representative may retain a constraint. -/
def unconstrainedBelow (rows : Rows) (transition : Transition) : Bool :=
  (transition :: (reachable rows [] transition.children).flatMap (row rows)).all
    fun edge => decide (edge.constraint = noConstraint)

/-- States whose terms can contain the changed state. -/
def containingStates (rows : Rows) (state : Nat) : List Nat :=
  grow (fun known => known ++ rows.filterMap fun (name, transitions) =>
    if transitions.any (fun edge => edge.children.any (· ∈ known)) then some name else none)
    (rows.length + 1) [state]

/-- Project one child index from a set of graph states. -/
def descend (rows : Rows) (states : List Nat) (index : Nat) : List Nat :=
  stateSet (states.flatMap fun state => (row rows state).filterMap fun edge => edge.children[index]?)

/-- States reached at every nonempty prefix of an observation path. -/
def statesAlong (rows : Rows) (edge : Transition) : Path → List (List Nat)
  | [] => []
  | index :: rest => rest.scanl (descend rows) ((edge.children[index]?).toList)

/-- The complete graph check for reads affected by replacing one state. -/
def keepsGuards (rows : Rows) (state : Nat) : Bool :=
  let containing := containingStates rows state
  rows.all fun (_, transitions) => transitions.all fun transition =>
    let reads := guardReads true transition.constraint.guard
    let structural := reads.structural ++ transition.constraint.equalities.flatten
    (constraintPaths transition.constraint).all fun target =>
      let levels := statesAlong rows transition target
      let last := (levels.getLast?).getD []
      let subterm := if levels.isEmpty then transition.children else last
      !(state ∈ (levels.reverse.drop 1).flatten) &&
        (!(state ∈ last) || (target ∈ reads.monotone && !(target ∈ reads.sensitive) && !(target ∈ structural))) &&
        (!(target ∈ structural) || subterm.all (fun child => !(child ∈ containing)))

/-- Redirect every occurrence of one child state together. -/
def redirectTransition (source destination : Nat) (transition : Transition) : Transition :=
  {transition with children := transition.children.map fun child => if child = source then destination else child}

/-- Keep old alternatives and add their redirected copies, then deduplicate. -/
def copyAlternatives (redirect : Nat × Nat) (transitions : List Transition) : List Transition :=
  (transitions ++ transitions.map (redirectTransition redirect.1 redirect.2)).eraseDups

/-- One source schedule step, including every skip condition. -/
def historicalApplyStep (original current : Rows) (applied : List (Nat × Nat)) (replacement : Replacement) :
    Rows × List (Nat × Nat) :=
  match transitionAt original replacement.removed, transitionAt original replacement.retained with
  | some removed, some retained =>
      let source := replacement.removed.node
      let destination := replacement.retained.node
      if source = destination ∧ removed = retained then
        (adjust current source List.eraseDups, applied)
      else if source ≠ destination ∧ row original destination ≠ [retained] then (current, applied)
      else if removed ∉ row current source then (current, applied)
      else if retained ∉ row current destination then (current, applied)
      else if !keepsGuards current source then (current, applied)
      else if !unconstrainedBelow current retained then (current, applied)
      else
        (adjust (current.map fun (state, transitions) =>
            (state, copyAlternatives (source, destination) transitions)) source
            (List.filter fun transition => transition != removed),
          applied ++ [(source, destination)])
  | _, _ => (current, applied)

/-- Every unordered pair, in first-seen order. -/
def unorderedPairs : List α → List (α × α)
  | [] => []
  | first :: rest => rest.map (first, ·) ++ unorderedPairs rest

/-- Similarity reports the direction of the first unresolved query. -/
inductive Error where
  | stale
  | unknown (left right : Address)
  | cyclic (addresses : List Address)
  | invalid
  | resolutionFuel
  deriving DecidableEq, Repr

/-- Prefer the first known direction. Never discard an unresolved possible direction. -/
def inferDirection (oracle : Address → Address → Guards.Verdict) (left right : Address) :
    Except Error (Option Pair) :=
  match oracle left right with
  | .yes => .ok (some ⟨left, right⟩)
  | .no => match oracle right left with
    | .yes => .ok (some ⟨right, left⟩)
    | .no => .ok none
    | .unknown => .error (.unknown right left)
  | .unknown => match oracle right left with
    | .yes => .ok (some ⟨right, left⟩)
    | _ => .error (.unknown left right)

/-- Infer every unordered transition pair and stop at the first unresolved direction. -/
def inferPairs (oracle : Address → Address → Guards.Verdict) :
    List (Address × Address) → Except Error (List Pair)
  | [] => .ok []
  | (left, right) :: rest => do
      let selected ← inferDirection oracle left right
      let further ← inferPairs oracle rest
      pure (selected.toList ++ further)

/-- Retain the first inferred dominator of each supertype transition. -/
def dominators (pairs : List Pair) : List (Address × Address) :=
  pairs.foldl (fun known pair =>
    if known.any (fun entry => decide (entry.1 = pair.high)) then known else known ++ [(pair.high, pair.low)]) []

/-- Lexicographic order of stable node and transition-index addresses. -/
def addressLe (left right : Address) : Bool :=
  decide (left.node < right.node ∨ (left.node = right.node ∧ left.ordinal ≤ right.ordinal))

/-- Follow transitive dominators, with the source's visited-set cycle error. -/
def resolve (dominators : List (Address × Address)) :
    Nat → List Address → Address → Except Error Address
  | 0, _, _ => .error .resolutionFuel
  | fuel + 1, visited, address =>
      if address ∈ visited then .error (.cyclic ((address :: visited).eraseDups.mergeSort addressLe))
      else match dominators.find? (fun entry => decide (entry.1 = address)) with
        | none => .ok address
        | some (_, representative) => resolve dominators fuel (address :: visited) representative

/-- Resolve each removed address before applying any graph mutation. -/
def replacements (pairs : List Pair) : Except Error (List Replacement) :=
  let known := dominators pairs
  (known.map Prod.fst |>.mergeSort addressLe).mapM fun removed => do
    pure ⟨removed, ← resolve known (known.length + 1) [] removed⟩

/-- The finite deterministic schedule records only redirects that were applied. -/
def historicalSchedule (original : Rows) (steps : List Replacement) : Rows × List (Nat × Nat) :=
  steps.foldl (fun (current, applied) step => historicalApplyStep original current applied step) (original, [])

/-- Final validation can reject guard references into a recursive node. -/
inductive Validation where
  | valid | cyclicGuard | invalid
  deriving DecidableEq, Repr

/-- Required structural checks for the explicit FTA table. -/
def structurallyValid (initial : Nat) (rows : Rows) : Bool :=
  let names := rows.map Prod.fst
  decide names.Nodup && initial ∈ names &&
    rows.all (fun (_, transitions) => transitions.all fun edge => edge.children.all (· ∈ names))

/-- The complete source schedule, including dependency, representative, and root fallbacks. -/
def historicalMinimize (snapshot originalSnapshot initial : Nat) (rows : Rows) (pairs : List Pair)
    (validate : Rows → Validation) : Except Error Rows := do
  if snapshot ≠ originalSnapshot then throw .stale
  if !structurallyValid initial rows then throw .invalid
  if !(pairs.all fun pair => (transitionAt rows pair.low).isSome && (transitionAt rows pair.high).isSome) then throw .stale
  let resolved ← replacements pairs
  let redirects := resolved.map fun replacement => (replacement.removed.node, replacement.retained.node)
  let (rewritten, applied) := historicalSchedule rows resolved
  let productive := productiveStates rewritten
  let finite := fun transition : Transition => transition.children.all (· ∈ productive)
  let hasFinite := fun chosen : Address => match transitionAt rows chosen with
    | none => false
    | some original =>
        (applied.foldl (fun alternatives redirect => copyAlternatives redirect alternatives) [original]).any
          fun transition => transition ∈ row rewritten chosen.node && finite transition
  let representatives := (resolved.map Replacement.retained).eraseDups
  let losesFinal := initial ∈ productiveStates rows && !(initial ∈ productive)
  let depends := resolved.any fun replacement => match transitionAt rows replacement.retained with
    | none => false
    | some retained => replacement.removed.node ∈ reachable rows redirects retained.children
  if depends || !(representatives.all hasFinite) || losesFinal then pure rows
  else
    let pruned := rewritten.map fun (state, transitions) => (state, transitions.filter finite)
    if !structurallyValid initial pruned then throw .invalid
    match validate pruned with
    | .cyclicGuard => pure rows
    | .invalid => throw .invalid
    | .valid => pure pruned

/-- Redirect copies retain all original alternatives. -/
theorem copyAlternatives_contains_original (redirect : Nat × Nat) (transitions : List Transition)
    (transition : Transition) (member : transition ∈ transitions) :
    transition ∈ copyAlternatives redirect transitions := by
  simp only [copyAlternatives, List.mem_eraseDups, List.mem_append, List.mem_map]
  exact Or.inl member

/-- Every added copy changes all occurrences of the selected child state together. -/
theorem redirected_child (source destination : Nat) (transition : Transition)
    (index child : Nat) (found : transition.children[index]? = some child) :
    (redirectTransition source destination transition).children[index]? =
      some (if child = source then destination else child) := by
  simp [redirectTransition, found]

/-- Redirecting a state to itself changes no transition. -/
theorem redirect_self (state : Nat) (transition : Transition) :
    redirectTransition state state transition = transition := by
  cases transition with
  | mk symbol refinement children constraint =>
      simp only [redirectTransition, Transition.mk.injEq, true_and, and_true]
      have pointwise : (fun child => if child = state then state else child) = id := by
        funext child
        split <;> simp_all
      simp [pointwise]

/-- A known first direction is used without requiring any converse verdict. -/
theorem first_direction_wins (oracle : Address → Address → Guards.Verdict)
    (left right : Address) (yes : oracle left right = .yes) :
    inferDirection oracle left right = .ok (some ⟨left, right⟩) := by
  simp [inferDirection, yes]

/-- A known converse remains usable when the first direction is unknown. -/
theorem known_converse_usable (oracle : Address → Address → Guards.Verdict)
    (left right : Address) (unknown : oracle left right = .unknown)
    (yes : oracle right left = .yes) :
    inferDirection oracle left right = .ok (some ⟨right, left⟩) := by
  simp [inferDirection, unknown, yes]

/-- Two unknown directions report the first direction. They are not treated as false. -/
theorem unknown_is_error (oracle : Address → Address → Guards.Verdict)
    (left right : Address) (forward : oracle left right = .unknown)
    (backward : oracle right left = .unknown) :
    inferDirection oracle left right = .error (.unknown left right) := by
  simp [inferDirection, forward, backward]

/-- A completed resolution cannot have stopped at an already visited address. -/
theorem resolve_cycle_detected (dominators : List (Address × Address))
    (fuel : Nat) (visited : List Address) (address : Address) (repeated : address ∈ visited) :
    resolve dominators (fuel + 1) visited address =
      .error (.cyclic ((address :: visited).eraseDups.mergeSort addressLe)) := by
  simp [resolve, repeated]

/-- Existing dominators keep the first inferred representative. -/
theorem first_dominator_example :
    dominators [⟨⟨0, 0⟩, ⟨2, 0⟩⟩, ⟨⟨1, 0⟩, ⟨2, 0⟩⟩] = [(⟨2, 0⟩, ⟨0, 0⟩)] := by
  cbv

/-- The schedule resolves an entire transitive chain before rewriting. -/
theorem transitive_resolution_example :
    replacements [⟨⟨0, 0⟩, ⟨1, 0⟩⟩, ⟨⟨1, 0⟩, ⟨2, 0⟩⟩] =
      .ok [⟨⟨1, 0⟩, ⟨0, 0⟩⟩, ⟨⟨2, 0⟩, ⟨0, 0⟩⟩] := by
  cbv

/-- A non-transitive oracle can still produce a longer directed cycle. -/
theorem three_cycle_rejected :
    replacements [⟨⟨0, 0⟩, ⟨1, 0⟩⟩, ⟨⟨1, 0⟩, ⟨2, 0⟩⟩, ⟨⟨2, 0⟩, ⟨0, 0⟩⟩] =
      .error (.cyclic [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩]) := by
  cbv

/-- A transition without children or constraints. -/
def leaf (symbol : Nat) : Transition := ⟨symbol, 0, [], noConstraint⟩

/-- Two distinct terms are accepted by one node before similarity minimization. -/
def twoLeaves : Rows := [(0, [leaf 0, leaf 1])]

/-- One same-node similarity relation selects the first term as representative. -/
def leafSimilarity : List Pair := [⟨⟨0, 0⟩, ⟨0, 1⟩⟩]

/-- The complete schedule removes the selected valid alternative. -/
theorem minimization_changes_exact_language :
    historicalMinimize 7 7 0 twoLeaves leafSimilarity (fun _ => .valid) = .ok [(0, [leaf 0])] := by
  cbv

/-- Interpret the shape language to inspect an unconstrained schedule's actual terms. -/
def shapeLanguage (rows : Rows) : Automaton Nat Nat := fun state =>
  (row rows state).map fun transition => ⟨transition.symbol, transition.children, fun _ => true⟩

/-- The removed term had an accepting run before the complete schedule. -/
theorem removed_term_was_accepted : Accepts (shapeLanguage twoLeaves) 0 (.node 1 []) := by
  exact .node ⟨1, [], fun _ => true⟩ [] (by simp [shapeLanguage, twoLeaves, row, leaf]) .nil rfl

/-- The removed term has no accepting run after the complete schedule. -/
theorem removed_term_no_longer_accepted :
    ¬ Accepts (shapeLanguage [(0, [leaf 0])]) 0 (.node 1 []) := by
  rw [accepts_node_iff]
  simp [shapeLanguage, row, leaf]

/-- The full minimizer is not an exact-language optimization, by its source contract. -/
theorem full_schedule_not_language_equivalent :
    ∃ output, historicalMinimize 7 7 0 twoLeaves leafSimilarity (fun _ => .valid) = .ok output ∧
      Accepts (shapeLanguage twoLeaves) 0 (.node 1 []) ∧
      ¬ Accepts (shapeLanguage output) 0 (.node 1 []) :=
  ⟨[(0, [leaf 0])], minimization_changes_exact_language,
    removed_term_was_accepted, removed_term_no_longer_accepted⟩

/-- A root removal without an incoming copy must preserve the original root. -/
def rootRemoval : Rows := [(0, [leaf 1]), (1, [leaf 0])]

/-- The final-root productivity check restores the original table. -/
theorem root_fallback_example :
    historicalMinimize 7 7 0 rootRemoval [⟨⟨1, 0⟩, ⟨0, 0⟩⟩] (fun _ => .valid) = .ok rootRemoval := by
  cbv

/-- Structural subtree observations forbid changing a compared state. -/
def structuralGuardRows : Rows :=
  [(0, [⟨2, 0, [1, 2], ⟨[], .not (.same [0] [1])⟩⟩]),
    (1, [leaf 1, leaf 0]), (2, [leaf 0])]

/-- The full guarded schedule skips the replacement rejected by the read check. -/
theorem structural_guard_preserved_example :
    historicalMinimize 7 7 0 structuralGuardRows [⟨⟨2, 0⟩, ⟨1, 0⟩⟩] (fun _ => .valid) = .ok structuralGuardRows := by
  cbv

/-- A representative with a residual guard cannot establish accepted nonemptiness. -/
def guardedRepresentativeRows : Rows :=
  [(0, [⟨2, 0, [1], noConstraint⟩]), (1, [leaf 1]),
    (2, [⟨0, 0, [], ⟨[], .bottom⟩⟩])]

/-- The full schedule retains the original when the representative is constrained. -/
theorem guarded_representative_skipped :
    historicalMinimize 7 7 0 guardedRepresentativeRows [⟨⟨2, 0⟩, ⟨1, 0⟩⟩] (fun _ => .valid) =
      .ok guardedRepresentativeRows := by
  cbv

/-- A final cyclic guard reference restores the original table. -/
theorem cyclic_guard_fallback_example :
    historicalMinimize 7 7 0 twoLeaves leafSimilarity (fun _ => .cyclicGuard) = .ok twoLeaves := by
  cbv

/-- A different automaton snapshot rejects an otherwise valid similarity set. -/
theorem stale_snapshot_example :
    historicalMinimize 8 7 0 twoLeaves leafSimilarity (fun _ => .valid) = .error .stale := by
  cbv

/-- The surviving root alternative has the rejecting guard `Satisfies [] false`. -/
def rejectingRoot : Transition := ⟨0, 0, [1], ⟨[], .satisfies [] 0⟩⟩

/-- The only accepted root term is `b`. Its representative `a` is a descendant state. -/
def rootCounterexampleBefore : Rows := [(0, [leaf 2, rejectingRoot]), (1, [leaf 1])]

/-- The rejected root alternative remains structurally productive after deleting `b`. -/
def rootCounterexampleAfter : Rows := [(0, [rejectingRoot]), (1, [leaf 1])]

/-- The actual complete schedule performs the root-language-emptying rewrite. -/
theorem complete_schedule_root_deletion :
    historicalMinimize 7 7 0 rootCounterexampleBefore [⟨⟨1, 0⟩, ⟨0, 0⟩⟩] (fun _ => .valid) =
      .ok rootCounterexampleAfter := by
  cbv

/-- Concrete semantics for the fixture's unconstrained and rejecting transitions. -/
def rootCounterexampleLanguage (rows : Rows) : Automaton Nat Nat := fun state =>
  (row rows state).map fun transition =>
    ⟨transition.symbol, transition.children,
      fun _ => decide (transition.constraint.guard = .top)⟩

/-- The root accepts `b` before running the complete minimization schedule. -/
theorem root_before_accepts :
    Accepts (rootCounterexampleLanguage rootCounterexampleBefore) 0 (.node 2 []) := by
  exact .node ⟨2, [], fun _ => true⟩ []
    (by simp [rootCounterexampleLanguage, rootCounterexampleBefore, row, leaf, noConstraint]) .nil rfl

/-- The retained representative remains accepted at its descendant state. -/
theorem root_after_representative_accepts :
    Accepts (rootCounterexampleLanguage rootCounterexampleAfter) 1 (.node 1 []) := by
  exact .node ⟨1, [], fun _ => true⟩ []
    (by simp [rootCounterexampleLanguage, rootCounterexampleAfter, row, leaf, noConstraint]) .nil rfl

/-- No finite root term survives the complete schedule. -/
theorem root_after_rejects (term : Term Nat) :
    ¬ Accepts (rootCounterexampleLanguage rootCounterexampleAfter) 0 term := by
  intro accepted
  cases accepted with
  | node edge children member runs guard =>
      have same : edge = ⟨0, [1], fun _ => false⟩ := by
        simpa [rootCounterexampleLanguage, rootCounterexampleAfter, rejectingRoot, row] using member
      subst edge
      cases guard

/-- Structural productivity passes despite total loss of accepted root terms. -/
theorem root_after_structurally_productive : 0 ∈ productiveStates rootCounterexampleAfter := by
  cbv
  exact .head _

/-- The executable complete schedule violates even accepted-root nonemptiness preservation. -/
theorem full_schedule_loses_all_root_terms :
    historicalMinimize 7 7 0 rootCounterexampleBefore [⟨⟨1, 0⟩, ⟨0, 0⟩⟩] (fun _ => .valid) =
        .ok rootCounterexampleAfter ∧
      (∃ term, Accepts (rootCounterexampleLanguage rootCounterexampleBefore) 0 term) ∧
      (∃ term, Accepts (rootCounterexampleLanguage rootCounterexampleAfter) 1 term) ∧
      0 ∈ productiveStates rootCounterexampleAfter ∧
      ¬ (∃ term, Accepts (rootCounterexampleLanguage rootCounterexampleAfter) 0 term) := by
  exact ⟨complete_schedule_root_deletion, ⟨_, root_before_accepts⟩,
    ⟨_, root_after_representative_accepts⟩, root_after_structurally_productive,
    fun ⟨term, accepted⟩ => root_after_rejects term accepted⟩

/-- The current schedule records representatives installed at the initial state. -/
structure ScheduleState where
  rows : Rows
  applied : List (Nat × Nat)
  rootRepresentatives : List Address
  deriving DecidableEq, Repr

/-- Install the selected representative when a root alternative is removed. -/
def applyStep (initial : Nat) (original : Rows) (state : ScheduleState)
    (replacement : Replacement) : ScheduleState :=
  match transitionAt original replacement.removed, transitionAt original replacement.retained with
  | some removed, some retained =>
      let source := replacement.removed.node
      let destination := replacement.retained.node
      if source = destination ∧ removed = retained then
        {state with rows := adjust state.rows source List.eraseDups}
      else if source ≠ destination ∧ row original destination ≠ [retained] then state
      else if removed ∉ row state.rows source then state
      else if retained ∉ row state.rows destination then state
      else if !keepsGuards state.rows source then state
      else if !unconstrainedBelow state.rows retained then state
      else
        {rows := adjust (state.rows.map fun (name, transitions) =>
            (name, copyAlternatives (source, destination) transitions)) source fun transitions =>
              let remaining := transitions.filter (· != removed)
              if source = initial then (retained :: remaining).eraseDups else remaining
         applied := state.applied ++ [(source, destination)]
         rootRepresentatives := if source = initial then
             (state.rootRepresentatives ++ [replacement.retained]).eraseDups
           else state.rootRepresentatives}
  | _, _ => state

/-- Apply the finite source schedule to one immutable transition snapshot. -/
def schedule (initial : Nat) (original : Rows) (steps : List Replacement) : ScheduleState :=
  steps.foldl (applyStep initial original) ⟨original, [], []⟩

/-- Remove transitions without productive children. -/
def pruneFinite (rows : Rows) : Rows :=
  let productive := productiveStates rows
  rows.map fun (state, transitions) =>
    (state, transitions.filter fun transition => transition.children.all (· ∈ productive))

/-- Retain only transitions whose guards and equality classes are empty. -/
def clearRows (rows : Rows) : Rows :=
  rows.map fun (state, transitions) =>
    (state, transitions.filter fun transition => decide (transition.constraint = noConstraint))

/-- Every original and redirected copy of one selected representative. -/
def representativeCopies (original : Rows) (applied : List (Nat × Nat)) (chosen : Address) : List Transition :=
  match transitionAt original chosen with
  | none => []
  | some transition => applied.foldl (fun alternatives redirect => copyAlternatives redirect alternatives) [transition]

/-- Check the selected representative against the final pruned root. -/
def rootRepresentativeSafe (initial : Nat) (original finalRows : Rows)
    (applied : List (Nat × Nat)) (chosen : Address) : Bool :=
  (representativeCopies original applied chosen).any fun transition =>
    transition ∈ row finalRows initial && decide (transition.constraint = noConstraint) &&
      transition.children.all (· ∈ productiveStates (clearRows finalRows))

/-- The gate applies to every root representative from every applied step. -/
def rootGate (initial : Nat) (original : Rows) (state : ScheduleState) : Bool :=
  state.rootRepresentatives.all
    (rootRepresentativeSafe initial original (pruneFinite state.rows) state.applied)

/-- Final source checks and validation. A failed root certificate restores the input. -/
def finish (initial : Nat) (rows : Rows) (resolved : List Replacement)
    (state : ScheduleState) (validate : Rows → Validation) : Except Error Rows :=
  let productive := productiveStates state.rows
  let finite := fun transition : Transition => transition.children.all (· ∈ productive)
  let hasFinite := fun chosen : Address =>
    (representativeCopies rows state.applied chosen).any fun transition =>
      transition ∈ row state.rows chosen.node && finite transition
  let representatives := (resolved.map Replacement.retained).eraseDups
  let losesFinal := initial ∈ productiveStates rows && !(initial ∈ productive)
  let redirects := resolved.map fun replacement => (replacement.removed.node, replacement.retained.node)
  let depends := resolved.any fun replacement => match transitionAt rows replacement.retained with
    | none => false
    | some retained => replacement.removed.node ∈ reachable rows redirects retained.children
  if depends || !(representatives.all hasFinite) || !(rootGate initial rows state) || losesFinal then .ok rows
  else
    let pruned := pruneFinite state.rows
    if !structurallyValid initial pruned then .error .invalid
    else match validate pruned with
      | .cyclicGuard => .ok rows
      | .invalid => .error .invalid
      | .valid => .ok pruned

/-- The current minimizer adds and rechecks accepted representatives at the root. -/
def minimize (snapshot originalSnapshot initial : Nat) (rows : Rows) (pairs : List Pair)
    (validate : Rows → Validation) : Except Error Rows := do
  if snapshot ≠ originalSnapshot then throw .stale
  if !structurallyValid initial rows then throw .invalid
  if !(pairs.all fun pair => (transitionAt rows pair.low).isSome && (transitionAt rows pair.high).isSome) then throw .stale
  let resolved ← replacements pairs
  finish initial rows resolved (schedule initial rows resolved) validate

/-- A final root certificate identifies a surviving clear copy with productive clear children. -/
theorem rootRepresentativeSafe_spec (initial : Nat) (original finalRows : Rows)
    (applied : List (Nat × Nat)) (chosen : Address)
    (safe : rootRepresentativeSafe initial original finalRows applied chosen = true) :
    ∃ transition, transition ∈ representativeCopies original applied chosen ∧
      transition ∈ row finalRows initial ∧ transition.constraint = noConstraint ∧
      ∀ child ∈ transition.children, child ∈ productiveStates (clearRows finalRows) := by
  simpa only [rootRepresentativeSafe, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, and_assoc] using safe

/-- Every applied root replacement must pass the gate after all later steps. -/
theorem rootGate_checks_every_applied (initial : Nat) (original : Rows) (state : ScheduleState)
    (gate : rootGate initial original state = true) (chosen : Address)
    (applied : chosen ∈ state.rootRepresentatives) :
    rootRepresentativeSafe initial original (pruneFinite state.rows) state.applied chosen = true :=
  List.all_eq_true.mp gate chosen applied

/-- A changed successful output passed the final gate and is the checked snapshot. -/
theorem finish_changed_has_certificate (initial : Nat) (original : Rows)
    (resolved : List Replacement) (state : ScheduleState) (validate : Rows → Validation)
    (output : Rows) (success : finish initial original resolved state validate = .ok output)
    (changed : output ≠ original) :
    output = pruneFinite state.rows ∧ rootGate initial original state = true := by
  unfold finish at success
  dsimp only at success
  split at success
  · cases success
    exact False.elim (changed rfl)
  · rename_i checks
    have gate : rootGate initial original state = true := by
      cases h : rootGate initial original state <;> simp_all
    split at success
    · cases success
    · split at success
      · cases success
        exact False.elim (changed rfl)
      · cases success
      · cases success
        exact ⟨rfl, gate⟩

/-- Interpret every named table row. A source map has only one row for each name. -/
def rowsLanguage (interpret : Constraint → Term (Nat × Nat) → Bool) (rows : Rows) : Automaton Nat (Nat × Nat) :=
  fun state => rows.flatMap fun (name, transitions) =>
    if name = state then transitions.map fun transition =>
      ⟨(transition.symbol, transition.refinement), transition.children, interpret transition.constraint⟩
    else []

/-- A transition in the selected row belongs to the table language. -/
theorem row_member_language (interpret : Constraint → Term (Nat × Nat) → Bool)
    (rows : Rows) (state : Nat) (transition : Transition) (member : transition ∈ row rows state) :
    ⟨(transition.symbol, transition.refinement), transition.children, interpret transition.constraint⟩ ∈
      rowsLanguage interpret rows state := by
  induction rows with
  | nil => simp [row] at member
  | cons entry rows ih =>
      rcases entry with ⟨name, transitions⟩
      by_cases same : name = state
      · subst name
        simp [row] at member
        simp only [rowsLanguage, List.flatMap_cons, ↓reduceIte, List.mem_append, List.mem_map]
        exact Or.inl ⟨transition, member, rfl⟩
      · have rest : transition ∈ row rows state := by simpa [row, same] using member
        simpa [rowsLanguage, same] using ih rest

/-- Sorting and deduplication do not change set membership. -/
theorem mem_stateSet (state : Nat) (states : List Nat) : state ∈ stateSet states ↔ state ∈ states := by
  simp [stateSet]

/-- Every bounded fixed-point iteration preserves a state predicate closed under its step. -/
theorem grow_invariant (step : List Nat → List Nat) (invariant : Nat → Prop)
    (closed : ∀ known, (∀ state ∈ known, invariant state) → ∀ state ∈ step known, invariant state)
    (fuel : Nat) (known : List Nat) (starts : ∀ state ∈ known, invariant state) :
    ∀ state ∈ grow step fuel known, invariant state := by
  induction fuel generalizing known with
  | zero => exact starts
  | succ fuel ih =>
      simp only [grow]
      split
      · exact starts
      · exact ih _ (fun state member => closed known starts state ((mem_stateSet state _).mp member))

/-- A productive clear state has an accepted term in the same final table. -/
theorem clear_productive_sound (interpret : Constraint → Term (Nat × Nat) → Bool)
    (clearSound : ∀ term, interpret noConstraint term = true) (rows : Rows)
    (state : Nat) (productive : state ∈ productiveStates (clearRows rows)) :
    ∃ term, Accepts (rowsLanguage interpret rows) state term := by
  apply grow_invariant
    (fun known => (clearRows rows).filterMap fun (state, transitions) =>
      if transitions.any (fun edge => edge.children.all (· ∈ known)) then some state else none)
    (fun state => ∃ term, Accepts (rowsLanguage interpret rows) state term) ?_
    ((clearRows rows).length + 1) [] (by simp) state productive
  intro known accepted target added
  obtain ⟨⟨name, transitions⟩, member, found⟩ := List.mem_filterMap.mp added
  by_cases anyChild : transitions.any (fun edge => edge.children.all (· ∈ known)) = true
  · simp only [anyChild, ↓reduceIte, Option.some.injEq] at found
    subst name
    obtain ⟨edge, edgeMember, children⟩ := List.any_eq_true.mp anyChild
    obtain ⟨⟨name, originals⟩, originalMember, same⟩ := List.mem_map.mp member
    simp only [Prod.mk.injEq] at same
    rcases same with ⟨rfl, rfl⟩
    have originalEdge : edge ∈ originals ∧ edge.constraint = noConstraint := by simpa using edgeMember
    obtain ⟨terms, runs⟩ := Productivity.all₂_witnesses (Accepts (rowsLanguage interpret rows)) edge.children
      (fun child member => accepted child (of_decide_eq_true (List.all_eq_true.mp children child member)))
    refine ⟨.node (edge.symbol, edge.refinement) terms,
      .node ⟨(edge.symbol, edge.refinement), edge.children, interpret edge.constraint⟩ terms ?_ runs ?_⟩
    · simp only [rowsLanguage, List.mem_flatMap]
      refine ⟨(_, originals), originalMember, ?_⟩
      simp only [↓reduceIte, List.mem_map]
      exact ⟨edge, originalEdge.1, rfl⟩
    · simpa only [originalEdge.2] using clearSound (.node (edge.symbol, edge.refinement) terms)
  · simp [anyChild] at found

/-- The final root certificate gives an accepted term rooted at the chosen representative copy. -/
theorem root_certificate_accepts (interpret : Constraint → Term (Nat × Nat) → Bool)
    (clearSound : ∀ term, interpret noConstraint term = true)
    (initial : Nat) (original finalRows : Rows) (applied : List (Nat × Nat)) (chosen : Address)
    (safe : rootRepresentativeSafe initial original finalRows applied chosen = true) :
    ∃ transition ∈ representativeCopies original applied chosen, ∃ children,
      Accepts (rowsLanguage interpret finalRows) initial (.node (transition.symbol, transition.refinement) children) := by
  obtain ⟨transition, copy, member, clear, children⟩ :=
    rootRepresentativeSafe_spec initial original finalRows applied chosen safe
  obtain ⟨terms, runs⟩ := Productivity.all₂_witnesses (Accepts (rowsLanguage interpret finalRows)) transition.children
    (fun child member => clear_productive_sound interpret clearSound finalRows child (children child member))
  exact ⟨transition, copy, terms, .node _ terms (row_member_language interpret finalRows initial transition member)
    runs (by simpa only [clear] using clearSound (.node (transition.symbol, transition.refinement) terms))⟩

/-- Repeated scheduled rewrites cannot silently discard an installed root representative. -/
theorem changed_schedule_keeps_root_representatives
    (interpret : Constraint → Term (Nat × Nat) → Bool)
    (clearSound : ∀ term, interpret noConstraint term = true)
    (initial : Nat) (original : Rows) (resolved : List Replacement)
    (state : ScheduleState) (validate : Rows → Validation) (output : Rows)
    (success : finish initial original resolved state validate = .ok output) (changed : output ≠ original)
    (chosen : Address) (installed : chosen ∈ state.rootRepresentatives) :
    ∃ transition ∈ representativeCopies original state.applied chosen, ∃ children,
      Accepts (rowsLanguage interpret output) initial (.node (transition.symbol, transition.refinement) children) := by
  obtain ⟨rfl, gate⟩ := finish_changed_has_certificate initial original resolved state validate output success changed
  exact root_certificate_accepts interpret clearSound initial original (pruneFinite state.rows) state.applied chosen
    (rootGate_checks_every_applied initial original state gate chosen installed)

/-- The exact source conditions for a root removal that reaches the mutation branch. -/
def RootRemovalApplied (initial : Nat) (original : Rows) (state : ScheduleState)
    (replacement : Replacement) : Prop :=
  ∃ removed retained,
    transitionAt original replacement.removed = some removed ∧
    transitionAt original replacement.retained = some retained ∧
    replacement.removed.node = initial ∧
    ¬(replacement.removed.node = replacement.retained.node ∧ removed = retained) ∧
    ¬(replacement.removed.node ≠ replacement.retained.node ∧ row original replacement.retained.node ≠ [retained]) ∧
    removed ∈ row state.rows replacement.removed.node ∧
    retained ∈ row state.rows replacement.retained.node ∧
    keepsGuards state.rows replacement.removed.node = true ∧
    unconstrainedBelow state.rows retained = true

/-- Every actual root removal enters its selected representative in the ledger. -/
theorem root_removal_recorded (initial : Nat) (original : Rows) (state : ScheduleState)
    (replacement : Replacement) (applied : RootRemovalApplied initial original state replacement) :
    replacement.retained ∈ (applyStep initial original state replacement).rootRepresentatives := by
  obtain ⟨removed, retained, removedFound, retainedFound, root, different, singleton,
    removedMember, retainedMember, guards, clear⟩ := applied
  subst initial
  simp [applyStep, removedFound, retainedFound, different, singleton, removedMember, retainedMember,
    guards, clear]

/-- A later rewrite never removes a recorded root obligation. -/
theorem applyStep_retains_ledger (initial : Nat) (original : Rows) (state : ScheduleState)
    (replacement : Replacement) (chosen : Address) (recorded : chosen ∈ state.rootRepresentatives) :
    chosen ∈ (applyStep initial original state replacement).rootRepresentatives := by
  unfold applyStep
  split
  · dsimp only
    split
    · exact recorded
    · split
      · exact recorded
      · split
        · exact recorded
        · split
          · exact recorded
          · split
            · exact recorded
            · split
              · exact recorded
              · dsimp only
                split
                · simp [recorded]
                · exact recorded
  · exact recorded

/-- Every remaining suffix preserves earlier root obligations. -/
theorem schedule_retains_ledger (initial : Nat) (original : Rows) (steps : List Replacement)
    (state : ScheduleState) (chosen : Address) (recorded : chosen ∈ state.rootRepresentatives) :
    chosen ∈ (steps.foldl (applyStep initial original) state).rootRepresentatives := by
  induction steps generalizing state with
  | nil => exact recorded
  | cons step rest ih =>
      exact ih _ (applyStep_retains_ledger initial original state step chosen recorded)

/-- An applied root removal remains represented after every later scheduled rewrite. -/
theorem complete_schedule_records_root_removal (initial : Nat) (original : Rows)
    (before after : List Replacement) (replacement : Replacement)
    (applied : RootRemovalApplied initial original (schedule initial original before) replacement) :
    replacement.retained ∈ (schedule initial original (before ++ replacement :: after)).rootRepresentatives := by
  simp only [schedule, List.foldl_append, List.foldl_cons]
  exact schedule_retains_ledger initial original after _ replacement.retained
    (root_removal_recorded initial original (schedule initial original before) replacement applied)

/-- A successful entry point runs final checks on the resolved complete schedule. -/
theorem minimize_success_finish (snapshot originalSnapshot initial : Nat) (rows : Rows)
    (pairs : List Pair) (validate : Rows → Validation) (resolved : List Replacement)
    (resolution : replacements pairs = .ok resolved) (output : Rows)
    (success : minimize snapshot originalSnapshot initial rows pairs validate = .ok output) :
    finish initial rows resolved (schedule initial rows resolved) validate = .ok output := by
  unfold minimize at success
  simp only [resolution] at success
  split at success
  · cases success
  · split at success
    · cases success
    · split at success
      · cases success
      · exact success

/-- Each deleted accepted root transition keeps its original term or an accepted selected representative. -/
theorem minimize_preserves_root_representative
    (interpret : Constraint → Term (Nat × Nat) → Bool)
    (clearSound : ∀ term, interpret noConstraint term = true)
    (snapshot originalSnapshot initial : Nat) (rows : Rows) (pairs : List Pair)
    (validate : Rows → Validation) (before after : List Replacement) (replacement : Replacement)
    (resolution : replacements pairs = .ok (before ++ replacement :: after))
    (applied : RootRemovalApplied initial rows (schedule initial rows before) replacement)
    (term : Term (Nat × Nat)) (accepted : Accepts (rowsLanguage interpret rows) initial term)
    (output : Rows) (success : minimize snapshot originalSnapshot initial rows pairs validate = .ok output) :
    Accepts (rowsLanguage interpret output) initial term ∨
      ∃ transition ∈ representativeCopies rows
        (schedule initial rows (before ++ replacement :: after)).applied replacement.retained,
        ∃ children, Accepts (rowsLanguage interpret output) initial
          (.node (transition.symbol, transition.refinement) children) := by
  by_cases same : output = rows
  · exact Or.inl (same ▸ accepted)
  · exact Or.inr (changed_schedule_keeps_root_representatives interpret clearSound initial rows
      (before ++ replacement :: after) (schedule initial rows (before ++ replacement :: after)) validate output
      (minimize_success_finish snapshot originalSnapshot initial rows pairs validate _ resolution output success)
      same replacement.retained
      (complete_schedule_records_root_removal initial rows before after replacement applied))

/-- The fixed schedule installs the representative when the other root guard rejects every term. -/
theorem repaired_root_counterexample :
    minimize 7 7 0 rootCounterexampleBefore [⟨⟨1, 0⟩, ⟨0, 0⟩⟩] (fun _ => .valid) =
      .ok [(0, [leaf 1, rejectingRoot]), (1, [leaf 1])] := by
  cbv

/-- The current schedule installs the representative instead of restoring the old root. -/
theorem repaired_only_root_alternative :
    minimize 7 7 0 rootRemoval [⟨⟨1, 0⟩, ⟨0, 0⟩⟩] (fun _ => .valid) =
      .ok [(0, [leaf 0]), (1, [leaf 0])] := by
  cbv

/-- Representative minimization still intentionally changes the exact term language. -/
theorem repaired_same_node_replacement :
    minimize 7 7 0 twoLeaves leafSimilarity (fun _ => .valid) = .ok [(0, [leaf 0])] := by
  cbv

end MicroCFTA.MinimizeSchedule
