import MicroCFTA.Language
import MicroCFTA.Guards

/-!
# Sparse observation plans and homogeneous refinement groups

The path plan follows `Refinement.Prune`: each trie node has an optional read
and finitely many indexed children. Insertion combines repeated requests.
Observation follows only children that exist in both the plan and the term.

The finite partition below operates on explicit candidate terms. It proves
coverage and homogeneity from the concrete observation implementation. The
Haskell graph specialization, interning, recursive binders, and memo tables
are separate correspondence obligations.
-/

namespace MicroCFTA.Observation
open MicroCFTA.Language

abbrev Path := List Nat

/-- Read only the refinement, or the complete root symbol and shape. -/
inductive Need where
  | refinement | symbol
  deriving DecidableEq, Repr

/-- A symbol-sensitive read includes every refinement-only read. -/
def combineNeed : Need → Need → Need
  | .refinement, .refinement => .refinement
  | _, _ => .symbol

/-- Insert the first request, or strengthen an existing request. -/
def addNeed (old : Option Need) (new : Need) : Option Need :=
  some (match old with | none => new | some previous => combineNeed previous new)

/-- A finite sparse trie. Child lookup uses the first matching index. -/
inductive Plan where
  | node (observation : Option Need) (children : List (Nat × Plan))

/-- The plan with no observed positions. -/
def emptyPlan : Plan := .node none []

/-- Read one indexed child of a sparse trie. -/
def childAt (index : Nat) : List (Nat × Plan) → Option Plan
  | [] => none
  | (key, child) :: rest => if index = key then some child else childAt index rest

/-- Replace or insert one indexed child. -/
def setChild (index : Nat) (child : Plan) : List (Nat × Plan) → List (Nat × Plan)
  | [] => [(index, child)]
  | (key, previous) :: rest =>
      if index = key then (key, child) :: rest else (key, previous) :: setChild index child rest

/-- Updating a sparse child changes exactly that lookup. -/
theorem childAt_setChild (index query : Nat) (child : Plan) (children : List (Nat × Plan)) :
    childAt query (setChild index child children) =
      if query = index then some child else childAt query children := by
  induction children with
  | nil => simp [setChild, childAt]
  | cons entry rest ih =>
      obtain ⟨key, previous⟩ := entry
      by_cases hi : index = key <;> by_cases hq : query = key <;>
        simp_all [setChild, childAt, eq_comm]

/-- The requested information at one path. Traversal is bounded by the path. -/
def lookup : Plan → Path → Option Need
  | .node observation _, [] => observation
  | .node _ children, index :: rest => (childAt index children).bind (fun child => lookup child rest)

/-- The empty plan has no requests, including below the root. -/
theorem lookup_empty (path : Path) : lookup emptyPlan path = none := by
  cases path <;> rfl

/-- Add one read, sharing every existing prefix and preserving other paths. -/
def insert (path : Path) (need : Need) : Plan → Plan
  | .node observation children => match path with
      | [] => .node (addNeed observation need) children
      | index :: rest => .node observation
          (setChild index (insert rest need ((childAt index children).getD emptyPlan)) children)

/-- Insertion changes precisely one requested path. It creates no prefix observations. -/
theorem lookup_insert (target query : Path) (need : Need) (plan : Plan) :
    lookup (insert target need plan) query =
      if query = target then addNeed (lookup plan query) need else lookup plan query := by
  induction target generalizing query plan with
  | nil => cases query <;> cases plan <;> simp [insert, lookup]
  | cons index rest ih =>
      cases plan with
      | node observation children =>
          cases query with
          | nil => simp [insert, lookup]
          | cons query suffix =>
              simp only [insert, lookup, childAt_setChild]
              by_cases same : query = index
              · subst query
                simp only [↓reduceIte, Option.bind_some]
                rw [ih]
                cases present : childAt index children <;>
                  simp [lookup_empty]
              · simp [same]

/-- Build a plan in the same left-to-right insertion order as the pruner. -/
def buildFrom (requests : List (Path × Need)) (initial : Plan) : Plan :=
  requests.foldl (fun plan request => insert request.1 request.2 plan) initial

/-- The direct path-local specification of repeated requests. -/
def requestedAt (requests : List (Path × Need)) (path : Path) (initial : Option Need) : Option Need :=
  requests.foldl (fun old request => if path = request.1 then addNeed old request.2 else old) initial

/-- Trie construction agrees with the path-local specification of every request. -/
theorem lookup_buildFrom (requests : List (Path × Need)) (initial : Plan) (path : Path) :
    lookup (buildFrom requests initial) path = requestedAt requests path (lookup initial path) := by
  induction requests generalizing initial with
  | nil => rfl
  | cons request rest ih =>
      simp only [buildFrom, requestedAt, List.foldl_cons] at *
      rw [ih, lookup_insert]

/-- Repeating an identical request does not strengthen it further. -/
theorem addNeed_idempotent (initial : Option Need) (need : Need) :
    addNeed (addNeed initial need) need = addNeed initial need := by
  cases initial with
  | none => cases need <;> rfl
  | some previous => cases previous <;> cases need <;> rfl

/-- A list of identical kinds requests exactly that kind at its member paths. -/
theorem requestedAt_uniform (paths : List Path) (path : Path) (need : Need) (initial : Option Need) :
    requestedAt (paths.map (fun target => (target, need))) path initial =
      if path ∈ paths then addNeed initial need else initial := by
  induction paths generalizing initial with
  | nil => simp [requestedAt]
  | cons target paths ih =>
      simp only [List.map_cons, requestedAt, List.foldl_cons] at *
      rw [ih]
      by_cases head : path = target <;> by_cases tail : path ∈ paths <;>
        simp [head, tail, addNeed_idempotent]

/-- Build the observation plan from its finite read requests. -/
def buildPlan (requests : List (Path × Need)) : Plan := buildFrom requests emptyPlan

/-- A requested position is present if it was present initially or occurs in the list. -/
theorem requestedAt_present (requests : List (Path × Need)) (path : Path) (initial : Option Need) :
    (requestedAt requests path initial).isSome = true ↔
      initial.isSome = true ∨ ∃ need, (path, need) ∈ requests := by
  induction requests generalizing initial with
  | nil => simp [requestedAt]
  | cons request rest ih =>
      obtain ⟨target, need⟩ := request
      simp only [requestedAt, List.foldl_cons] at *
      rw [ih]
      by_cases same : path = target
      · subst path
        simp [addNeed]
      · simp [same]

/-- The trie contains exactly the requested paths, not their unrequested prefixes. -/
theorem buildPlan_coverage (requests : List (Path × Need)) (path : Path) :
    (lookup (buildPlan requests) path).isSome = true ↔ ∃ need, (path, need) ∈ requests := by
  rw [buildPlan, lookup_buildFrom, requestedAt_present, lookup_empty]
  simp

/-- A term symbol contains a constructor name and a refinement annotation. -/
structure Label (Symbol Refinement : Type) where
  symbol : Symbol
  refinement : Refinement
  deriving DecidableEq

/-- One exact root observation. True leafness means no children. -/
structure Observed (Symbol Refinement : Type) where
  label : Label Symbol Refinement
  leaf : Bool
  deriving DecidableEq

/-- The information retained in a partition signature. -/
inductive Entry (Symbol Refinement : Type) where
  | refinement : Refinement → Entry Symbol Refinement
  | symbol : Observed Symbol Refinement → Entry Symbol Refinement
  deriving DecidableEq

/-- Inspect the symbol and leafness of one existing subtree. -/
def rootObservation : Term (Label Symbol Refinement) → Observed Symbol Refinement
  | .node label children => ⟨label, children.isEmpty⟩

/-- Project exactly the information requested at one position. -/
def signatureEntry (need : Need) (term : Term (Label Symbol Refinement)) : Entry Symbol Refinement :=
  match need with
  | .refinement => .refinement (rootObservation term).label.refinement
  | .symbol => .symbol (rootObservation term)

/-- Read a sparse tree plan without inventing absent child positions. -/
def readWith (inspect : Need → Term LabelType → Value) : Plan → Term LabelType → Path → Option Value
  | .node observation _, term, [] => observation.map (fun need => inspect need term)
  | .node _ planned, .node _ children, index :: rest => do
      let childPlan ← childAt index planned
      let childTerm ← children[index]?
      readWith inspect childPlan childTerm rest

/-- Sparse traversal agrees with independent plan and complete-term path lookup. -/
theorem readWith_correct (inspect : Need → Term LabelType → Value)
    (plan : Plan) (term : Term LabelType) (path : Path) :
    readWith inspect plan term path = (lookup plan path).bind
      (fun need => (term.atPath path).map (inspect need)) := by
  induction path generalizing plan term with
  | nil =>
      cases plan with
      | node observation children => cases observation <;> rfl
  | cons index rest ih =>
      cases plan with
      | node observation planned =>
          cases term with
          | node label children =>
              simp only [readWith, lookup, Term.atPath]
              cases hp : childAt index planned <;> cases ht : children[index]? <;>
                simp [ih]

/-- The full observations retained beside a partition signature. -/
def observations (plan : Plan) (term : Term (Label Symbol Refinement)) : Path → Option (Observed Symbol Refinement) :=
  readWith (fun _ => rootObservation) plan term

/-- The signature used to group candidates. -/
def signature (plan : Plan) (term : Term (Label Symbol Refinement)) : Path → Option (Entry Symbol Refinement) :=
  readWith signatureEntry plan term

/-- A sparse observation is present exactly when the path is requested and exists. -/
theorem observations_present (plan : Plan) (term : Term (Label Symbol Refinement)) (path : Path) :
    (observations plan term path).isSome = true ↔
      (lookup plan path).isSome = true ∧ (term.atPath path).isSome = true := by
  rw [observations, readWith_correct]
  cases lookup plan path <;> cases term.atPath path <;> simp

/-- At a requested path, sparse observation equals direct full-term observation. -/
theorem observations_exact (plan : Plan) (term : Term (Label Symbol Refinement))
    (path : Path) (need : Need) (requested : lookup plan path = some need) :
    observations plan term path = (term.atPath path).map rootObservation := by
  simp [observations, readWith_correct, requested]

/-- Read only the refinement at a complete-term position. -/
def refinementAt (term : Term (Label Symbol Refinement)) (path : Path) : Option Refinement :=
  (term.atPath path).map (fun term => (rootObservation term).label.refinement)

/-- Equal signatures preserve the refinement and missing-path status of every requested read. -/
theorem signature_preserves_refinement (plan : Plan)
    (left right : Term (Label Symbol Refinement)) (path : Path) (need : Need)
    (requested : lookup plan path = some need)
    (same : signature plan left path = signature plan right path) :
    refinementAt left path = refinementAt right path := by
  simp only [signature, readWith_correct, requested, Option.bind_some] at same
  cases hl : left.atPath path <;> cases hr : right.atPath path <;>
    cases need <;> simp_all [refinementAt, signatureEntry]

/-- Symbol-sensitive signatures preserve the full sparse observation. -/
theorem signature_preserves_observation (plan : Plan)
    (left right : Term (Label Symbol Refinement)) (path : Path)
    (requested : lookup plan path = some .symbol)
    (same : signature plan left path = signature plan right path) :
    observations plan left path = observations plan right path := by
  simp only [signature, readWith_correct, requested, Option.bind_some] at same
  simp only [observations, readWith_correct, requested, Option.bind_some]
  cases hl : left.atPath path <;> cases hr : right.atPath path <;>
    simp_all [signatureEntry]

/-- Refinement-only atoms discharged by semantic pruning. -/
inductive Atom (Refinement : Type) where
  | entails (left right : Path)
  | satisfies (target : Path) (formula : Refinement)
  | holds (targets : List Path) (formula : Refinement)

/-- The fixed formula operations and solver results used by atomic queries. -/
structure Queries (Refinement : Type) where
  entails : Refinement → Refinement → Guards.Verdict
  negateFormula : Refinement → Refinement
  contract : List Path → List Refinement → Refinement → Guards.Verdict

/-- The positions read by one refinement atom, including repeated contract paths. -/
def atomPaths : Atom Refinement → List Path
  | .entails left right => [left, right]
  | .satisfies target _ => [target]
  | .holds targets _ => targets

/-- Read a complete tuple of refinements. One missing position rejects the tuple. -/
def gather (view : Path → Option Refinement) : List Path → Option (List Refinement)
  | [] => some []
  | path :: rest => do
      let value ← view path
      let values ← gather view rest
      pure (value :: values)

/-- Gathering depends only on the named positions, including absence. -/
theorem gather_ext (left right : Path → Option Refinement) (paths : List Path)
    (same : ∀ path, path ∈ paths → left path = right path) :
    gather left paths = gather right paths := by
  induction paths with
  | nil => rfl
  | cons path paths ih =>
      simp only [gather]
      rw [same path (by simp), ih (fun other member => same other (by simp [member]))]

/-- Apply the evaluator's polarity and missing-path rules to an atomic query. -/
def atomQuery (queries : Queries Refinement) (view : Path → Option Refinement)
    (atom : Atom Refinement) (positive : Bool) : Guards.Verdict :=
  match atom with
  | .entails left right =>
      let result := match view left, view right with
        | some low, some high => queries.entails low high
        | _, _ => .no
      if positive then result else Guards.negate result
  | .satisfies target formula => match view target with
      | some refinement => queries.entails refinement
          (if positive then formula else queries.negateFormula formula)
      | none => if positive then .no else .yes
  | .holds targets formula => match gather view targets with
      | some refinements => queries.contract targets refinements
          (if positive then formula else queries.negateFormula formula)
      | none => if positive then .no else .yes

/-- Atomic evaluation is determined by its concrete refinement observations. -/
theorem atomQuery_ext (queries : Queries Refinement) (left right : Path → Option Refinement)
    (atom : Atom Refinement) (positive : Bool)
    (same : ∀ path, path ∈ atomPaths atom → left path = right path) :
    atomQuery queries left atom positive = atomQuery queries right atom positive := by
  cases atom with
  | entails p q => simp [atomQuery, same p (by simp [atomPaths]), same q (by simp [atomPaths])]
  | satisfies p formula => simp [atomQuery, same p (by simp [atomPaths])]
  | holds paths formula => rw [atomQuery, atomQuery, gather_ext left right paths same]

/-- All paths read by the Boolean semantic guard. -/
def guardPaths : Guards.Guard (Atom Refinement) → List Path
  | .top | .bottom => []
  | .atom atom => atomPaths atom
  | .not guard => guardPaths guard
  | .and left right | .or left right => guardPaths left ++ guardPaths right

/-- Refinement-only guards request refinement observations at every named position. -/
def guardPlan (guard : Guards.Guard (Atom Refinement)) : Plan :=
  buildPlan ((guardPaths guard).map (fun path => (path, Need.refinement)))

/-- A semantic guard's trie requests only refinements, at exactly its read paths. -/
theorem lookup_guardPlan (guard : Guards.Guard (Atom Refinement)) (path : Path) :
    lookup (guardPlan guard) path =
      if path ∈ guardPaths guard then some .refinement else none := by
  simp [guardPlan, buildPlan, lookup_buildFrom, lookup_empty, requestedAt_uniform, addNeed]

/-- Every path read by a guard is requested by its concrete trie. -/
theorem guardPlan_covers (guard : Guards.Guard (Atom Refinement)) (path : Path)
    (member : path ∈ guardPaths guard) : ∃ need, lookup (guardPlan guard) path = some need := by
  have requested : (lookup (guardPlan guard) path).isSome = true :=
    (buildPlan_coverage _ path).mpr ⟨.refinement, List.mem_map.mpr ⟨path, member, rfl⟩⟩
  cases found : lookup (guardPlan guard) path with
  | none => simp [found] at requested
  | some need => exact ⟨need, rfl⟩

/-- Boolean evaluation depends only on the paths collected from the actual guard. -/
theorem guardQuery_ext (queries : Queries Refinement) (left right : Path → Option Refinement)
    (guard : Guards.Guard (Atom Refinement)) (positive : Bool)
    (same : ∀ path, path ∈ guardPaths guard → left path = right path) :
    Guards.evaluate (atomQuery queries left) positive guard =
      Guards.evaluate (atomQuery queries right) positive guard := by
  induction guard generalizing positive with
  | top => rfl
  | bottom => rfl
  | atom atom => exact atomQuery_ext queries left right atom positive same
  | not guard ih => exact ih (!positive) same
  | and leftGuard rightGuard ihl ihr =>
      have hl := fun p => ihl p (fun path member => same path (List.mem_append_left _ member))
      have hr := fun p => ihr p (fun path member => same path (List.mem_append_right _ member))
      simp only [Guards.evaluate, hl, hr]
  | or leftGuard rightGuard ihl ihr =>
      have hl := fun p => ihl p (fun path member => same path (List.mem_append_left _ member))
      have hr := fun p => ihr p (fun path member => same path (List.mem_append_right _ member))
      simp only [Guards.evaluate, hl, hr]

/-- A finite key records the signature at each requested guard position. -/
def key (guard : Guards.Guard (Atom Refinement)) (term : Term (Label Symbol Refinement)) :
    List (Option (Entry Symbol Refinement)) :=
  (guardPaths guard).map (signature (guardPlan guard) term)

/-- Unrequested positions are absent from the complete sparse signature. -/
theorem signature_outside_guard (guard : Guards.Guard (Atom Refinement))
    (term : Term (Label Symbol Refinement)) (path : Path) (absent : path ∉ guardPaths guard) :
    signature (guardPlan guard) term path = none := by
  have noRequest : (lookup (guardPlan guard) path).isSome = false := by
    cases found : lookup (guardPlan guard) path with
    | none => rfl
    | some need =>
        have present : (lookup (guardPlan guard) path).isSome = true := by simp [found]
        obtain ⟨needed, member⟩ := (buildPlan_coverage _ path).mp present
        obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
        cases same
        exact False.elim (absent originalMember)
  simp only [signature, readWith_correct]
  cases found : lookup (guardPlan guard) path <;> simp_all

/-- The finite key is exactly the whole sparse signature, with missing entries explicit. -/
theorem key_eq_iff_signature_eq (guard : Guards.Guard (Atom Refinement))
    (left right : Term (Label Symbol Refinement)) :
    key guard left = key guard right ↔ signature (guardPlan guard) left = signature (guardPlan guard) right := by
  constructor
  · intro same
    funext path
    by_cases member : path ∈ guardPaths guard
    · exact List.map_eq_map_iff.mp same path member
    · rw [signature_outside_guard guard left path member, signature_outside_guard guard right path member]
  · intro same
    simp only [key, same]

/-- A refinement request projects precisely the optional refinement at that path. -/
theorem signature_refinement (plan : Plan) (term : Term (Label Symbol Refinement))
    (path : Path) (requested : lookup plan path = some .refinement) :
    signature plan term path = (refinementAt term path).map Entry.refinement := by
  simp only [signature, readWith_correct, requested, Option.bind_some, refinementAt, Option.map_map]
  rfl

/-- The concrete semantic key ignores constructor names and shape at refinement reads. -/
theorem key_eq_iff_refinements_eq (guard : Guards.Guard (Atom Refinement))
    (left right : Term (Label Symbol Refinement)) :
    key guard left = key guard right ↔
      ∀ path, path ∈ guardPaths guard → refinementAt left path = refinementAt right path := by
  constructor
  · intro same path member
    obtain ⟨need, requested⟩ := guardPlan_covers guard path member
    exact signature_preserves_refinement (guardPlan guard) left right path need requested
      (List.map_eq_map_iff.mp same path member)
  · intro same
    apply List.map_eq_map_iff.mpr
    intro path member
    have requested : lookup (guardPlan guard) path = some .refinement := by
      simp [lookup_guardPlan, member]
    rw [signature_refinement _ left _ requested, signature_refinement _ right _ requested,
      same path member]

/-- The complete-term guard decision used for each candidate. -/
def verdict (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (term : Term (Label Symbol Refinement)) (positive : Bool := true) : Guards.Verdict :=
  Guards.evaluate (atomQuery queries (refinementAt term)) positive guard

/-- Equal concrete keys imply equal complete-term guard decisions. -/
theorem key_homogeneous (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (left right : Term (Label Symbol Refinement)) (same : key guard left = key guard right)
    (positive : Bool) : verdict queries guard left positive = verdict queries guard right positive := by
  apply guardQuery_ext
  intro path member
  have observed := List.map_eq_map_iff.mp same path member
  obtain ⟨need, requested⟩ := guardPlan_covers guard path member
  exact signature_preserves_refinement (guardPlan guard) left right path need requested observed

/-- A concrete group contains exactly candidates with one observation key. -/
def group [DecidableEq Symbol] [DecidableEq Refinement]
    (guard : Guards.Guard (Atom Refinement)) (terms : List (Term (Label Symbol Refinement)))
    (wanted : List (Option (Entry Symbol Refinement))) : List (Term (Label Symbol Refinement)) :=
  Guards.groupByKey (key guard) terms wanted

/-- Enumerate each live observation key once, in first-seen order. -/
def groupKeys [DecidableEq Symbol] [DecidableEq Refinement]
    (guard : Guards.Guard (Atom Refinement)) (terms : List (Term (Label Symbol Refinement))) :
    List (List (Option (Entry Symbol Refinement))) :=
  (terms.map (key guard)).eraseDups

/-- Materialize the finite observation partition. -/
def specializedGroups [DecidableEq Symbol] [DecidableEq Refinement]
    (guard : Guards.Guard (Atom Refinement)) (terms : List (Term (Label Symbol Refinement))) :
    List (List (Term (Label Symbol Refinement))) :=
  (groupKeys guard terms).map (group guard terms)

/-- Every actual member places its key in the finite partition. -/
theorem groupKey_of_member [DecidableEq Symbol] [DecidableEq Refinement]
    (guard : Guards.Guard (Atom Refinement)) (terms : List (Term (Label Symbol Refinement)))
    (wanted : List (Option (Entry Symbol Refinement))) (term : Term (Label Symbol Refinement))
    (member : term ∈ group guard terms wanted) : wanted ∈ groupKeys guard terms := by
  obtain ⟨original, same⟩ := (Guards.mem_groupByKey (key guard) terms wanted term).mp member
  exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨term, original, same⟩)

/-- The executable finite partition covers exactly the candidate term language. -/
theorem specializedGroups_cover [DecidableEq Symbol] [DecidableEq Refinement]
    (guard : Guards.Guard (Atom Refinement)) (terms : List (Term (Label Symbol Refinement)))
    (term : Term (Label Symbol Refinement)) :
    term ∈ (specializedGroups guard terms).flatten ↔ term ∈ terms := by
  constructor
  · intro member
    obtain ⟨members, known, inside⟩ := List.mem_flatten.mp member
    obtain ⟨wanted, _, same⟩ := List.mem_map.mp known
    subst members
    exact ((Guards.mem_groupByKey (key guard) terms wanted term).mp inside).1
  · intro member
    have inside : term ∈ group guard terms (key guard term) :=
      (Guards.mem_groupByKey (key guard) terms (key guard term) term).mpr ⟨member, rfl⟩
    exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr
      ⟨key guard term, groupKey_of_member guard terms _ term inside, rfl⟩, inside⟩

/-- Decide a group from its first member. Empty groups impose no obligations. -/
def groupDecision [DecidableEq Symbol] [DecidableEq Refinement] (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (terms : List (Term (Label Symbol Refinement)))
    (wanted : List (Option (Entry Symbol Refinement))) : Guards.Verdict :=
  match (group guard terms wanted).head? with
  | none => .unknown
  | some representative => verdict queries guard representative

/-- Every member has the decision computed from the first member of its actual group. -/
theorem groupDecision_of_member [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (terms : List (Term (Label Symbol Refinement))) (wanted : List (Option (Entry Symbol Refinement)))
    (term : Term (Label Symbol Refinement)) (member : term ∈ group guard terms wanted) :
    groupDecision queries guard terms wanted = verdict queries guard term := by
  have targetKey := ((Guards.mem_groupByKey (key guard) terms wanted term).mp member).2
  cases members : group guard terms wanted with
  | nil => simp [members] at member
  | cons representative rest =>
      have firstMember : representative ∈ group guard terms wanted := by simp [members]
      have firstKey := ((Guards.mem_groupByKey (key guard) terms wanted representative).mp firstMember).2
      simp only [groupDecision, members, List.head?_cons]
      exact key_homogeneous queries guard representative term (firstKey.trans targetKey.symm) true

/-- Concrete grouping and guard discharge preserve exactly the filtered candidate language. -/
theorem grouped_discharge_exact [DecidableEq Symbol] [DecidableEq Refinement]
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (terms : List (Term (Label Symbol Refinement))) (residual : Term (Label Symbol Refinement) → Prop)
    (term : Term (Label Symbol Refinement)) :
    Guards.AfterPartition (fun wanted candidate => candidate ∈ group guard terms wanted)
      (groupDecision queries guard terms) (fun candidate => verdict queries guard candidate = .yes)
      residual term ↔
        term ∈ terms ∧ verdict queries guard term = .yes ∧ residual term := by
  rw [Guards.partition_discharge_preserves]
  · apply Guards.partition_cover_preserves
    intro candidate
    exact Guards.groupByKey_cover (key guard) terms candidate
  · intro wanted candidate member
    rw [groupDecision_of_member queries guard terms wanted candidate member]
    cases verdict queries guard candidate <;> simp [Guards.Supports]

/-- Concrete sparse grouping covers exactly the bounded accepted candidate language. -/
theorem bounded_grouped_discharge_exact [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (fuel : Nat) (state : State)
    (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (residual : Term (Label Symbol Refinement) → Prop) (term : Term (Label Symbol Refinement)) :
    Guards.AfterPartition
      (fun wanted candidate => candidate ∈ group guard (enumerate automaton fuel state) wanted)
      (groupDecision queries guard (enumerate automaton fuel state))
      (fun candidate => verdict queries guard candidate = .yes) residual term ↔
        Accepts automaton state term ∧ term.height ≤ fuel ∧
          verdict queries guard term = .yes ∧ residual term := by
  rw [grouped_discharge_exact, mem_enumerate_iff]
  simp only [and_assoc]

end MicroCFTA.Observation
