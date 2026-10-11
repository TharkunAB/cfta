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
def applyStep (original current : Rows) (applied : List (Nat × Nat)) (replacement : Replacement) :
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
def schedule (original : Rows) (steps : List Replacement) : Rows × List (Nat × Nat) :=
  steps.foldl (fun (current, applied) step => applyStep original current applied step) (original, [])

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
def minimize (snapshot originalSnapshot initial : Nat) (rows : Rows) (pairs : List Pair)
    (validate : Rows → Validation) : Except Error Rows := do
  if snapshot ≠ originalSnapshot then throw .stale
  if !structurallyValid initial rows then throw .invalid
  if !(pairs.all fun pair => (transitionAt rows pair.low).isSome && (transitionAt rows pair.high).isSome) then throw .stale
  let resolved ← replacements pairs
  let redirects := resolved.map fun replacement => (replacement.removed.node, replacement.retained.node)
  let (rewritten, applied) := schedule rows resolved
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
    minimize 7 7 0 twoLeaves leafSimilarity (fun _ => .valid) = .ok [(0, [leaf 0])] := by
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
    ∃ output, minimize 7 7 0 twoLeaves leafSimilarity (fun _ => .valid) = .ok output ∧
      Accepts (shapeLanguage twoLeaves) 0 (.node 1 []) ∧
      ¬ Accepts (shapeLanguage output) 0 (.node 1 []) :=
  ⟨[(0, [leaf 0])], minimization_changes_exact_language,
    removed_term_was_accepted, removed_term_no_longer_accepted⟩

/-- A root removal without an incoming copy must preserve the original root. -/
def rootRemoval : Rows := [(0, [leaf 1]), (1, [leaf 0])]

/-- The final-root productivity check restores the original table. -/
theorem root_fallback_example :
    minimize 7 7 0 rootRemoval [⟨⟨1, 0⟩, ⟨0, 0⟩⟩] (fun _ => .valid) = .ok rootRemoval := by
  cbv

/-- Structural subtree observations forbid changing a compared state. -/
def structuralGuardRows : Rows :=
  [(0, [⟨2, 0, [1, 2], ⟨[], .not (.same [0] [1])⟩⟩]),
    (1, [leaf 1, leaf 0]), (2, [leaf 0])]

/-- The full guarded schedule skips the replacement rejected by the read check. -/
theorem structural_guard_preserved_example :
    minimize 7 7 0 structuralGuardRows [⟨⟨2, 0⟩, ⟨1, 0⟩⟩] (fun _ => .valid) = .ok structuralGuardRows := by
  cbv

/-- A representative with a residual guard cannot establish accepted nonemptiness. -/
def guardedRepresentativeRows : Rows :=
  [(0, [⟨2, 0, [1], noConstraint⟩]), (1, [leaf 1]),
    (2, [⟨0, 0, [], ⟨[], .bottom⟩⟩])]

/-- The full schedule retains the original when the representative is constrained. -/
theorem guarded_representative_skipped :
    minimize 7 7 0 guardedRepresentativeRows [⟨⟨2, 0⟩, ⟨1, 0⟩⟩] (fun _ => .valid) =
      .ok guardedRepresentativeRows := by
  cbv

/-- A final cyclic guard reference restores the original table. -/
theorem cyclic_guard_fallback_example :
    minimize 7 7 0 twoLeaves leafSimilarity (fun _ => .cyclicGuard) = .ok twoLeaves := by
  cbv

/-- A different automaton snapshot rejects an otherwise valid similarity set. -/
theorem stale_snapshot_example :
    minimize 8 7 0 twoLeaves leafSimilarity (fun _ => .valid) = .error .stale := by
  cbv

/-- The surviving root alternative has the rejecting guard `Satisfies [] false`. -/
def rejectingRoot : Transition := ⟨0, 0, [1], ⟨[], .satisfies [] 0⟩⟩

/-- The only accepted root term is `b`. Its representative `a` is a descendant state. -/
def rootCounterexampleBefore : Rows := [(0, [leaf 2, rejectingRoot]), (1, [leaf 1])]

/-- The rejected root alternative remains structurally productive after deleting `b`. -/
def rootCounterexampleAfter : Rows := [(0, [rejectingRoot]), (1, [leaf 1])]

/-- The actual complete schedule performs the root-language-emptying rewrite. -/
theorem complete_schedule_root_deletion :
    minimize 7 7 0 rootCounterexampleBefore [⟨⟨1, 0⟩, ⟨0, 0⟩⟩] (fun _ => .valid) =
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
    minimize 7 7 0 rootCounterexampleBefore [⟨⟨1, 0⟩, ⟨0, 0⟩⟩] (fun _ => .valid) =
        .ok rootCounterexampleAfter ∧
      (∃ term, Accepts (rootCounterexampleLanguage rootCounterexampleBefore) 0 term) ∧
      (∃ term, Accepts (rootCounterexampleLanguage rootCounterexampleAfter) 1 term) ∧
      0 ∈ productiveStates rootCounterexampleAfter ∧
      ¬ (∃ term, Accepts (rootCounterexampleLanguage rootCounterexampleAfter) 0 term) := by
  exact ⟨complete_schedule_root_deletion, ⟨_, root_before_accepts⟩,
    ⟨_, root_after_representative_accepts⟩, root_after_structurally_productive,
    fun ⟨term, accepted⟩ => root_after_rejects term accepted⟩

end MicroCFTA.MinimizeSchedule
