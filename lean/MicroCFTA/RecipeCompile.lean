import MicroCFTA.PublicResult
import MicroCFTA.SizeMass
import MicroCFTA.LatticeSelect

/-!
# Refinement recipe compilation control and metadata

The control model follows `Gen/Refinement/Internal/Compile.hs`. Recipe values,
Haskell functions, and automata are erased where control does not inspect them.
The model retains source status, recursive status, root counts, integer-leaf
routing, requested paths, error precedence, and per-size metadata. It does not
assume that an abstract compiler preserves an unspecified language.
-/

namespace MicroCFTA.RecipeCompile

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error

/-- Source error categories used by the compile driver. -/
inductive Error where
  | requiresCompilation | empty | unbounded | opaque | solverUnknown
  | childNotOneTerm | missingRoot | relationalEquality | syntacticEquality
  | integerRead | uncountable (cause : Nat) | other (cause : Nat)
  deriving DecidableEq, Repr

/-- A known number of surface roots, or a heterogeneous/unknown root count. -/
inductive RootCount where
  | known (count : Nat)
  | unknown
  deriving DecidableEq, Repr

/-- The source-language information that the compile driver reads. -/
inductive Source where
  | finite (result : Except Error RootCount)
  | cyclic (result : Except Error Unit)
  | opaque
  deriving Repr

mutual
/-- A generator's recipe and independently stored source-language status. -/
inductive Generator where
  | mk (source : Source) (recipe : Recipe)
  deriving Repr

/-- All source recipe cases. Values and uninterpreted callbacks are erased. -/
inductive Recipe where
  | built | lifted
  | mapped (inner : Generator)
  | paid (inner : Generator)
  | applied (functions arguments : Generator)
  | chosen (alternatives : List (Int × Generator))
  | uniform (alternatives : List Generator)
  | closed (child : Generator)
  | closedBy (child : Generator)
  | imported | integers
  deriving Repr
end

/-- Read the recorded source state. -/
def source : Generator → Source
  | .mk state _ => state

/-- Read the construction recipe. -/
def recipe : Generator → Recipe
  | .mk _ description => description

/-- Only the designated finite-source failure requests refinement compilation. -/
def deferred (generator : Generator) : Bool :=
  match source generator with
  | .finite (.error .requiresCompilation) => true
  | _ => false

/-- Combine root counts for an applicative product. -/
def addRoots : RootCount → RootCount → RootCount
  | .known left, .known right => .known (left + right)
  | _, _ => .unknown

/-- The source uses one root for an empty choice and requires agreement otherwise. -/
def commonRoots : List RootCount → RootCount
  | [] => .known 1
  | first :: rest => if rest.all (· == first) then first else .unknown

mutual
/-- The exact root-count cases read by spine alignment and node leafness. -/
def rootCount : Generator → RootCount
  | .mk _ .lifted => .known 0
  | .mk _ (.mapped inner) | .mk _ (.paid inner) => rootCount inner
  | .mk _ (.applied left right) => addRoots (rootCount left) (rootCount right)
  | .mk _ (.chosen alternatives) => commonRoots (weightedRootCounts alternatives)
  | .mk _ (.uniform alternatives) => commonRoots (rootCounts alternatives)
  | .mk _ (.closed _) | .mk _ (.closedBy _) | .mk _ .imported | .mk _ .integers => .known 1
  | .mk (.finite (.ok roots)) .built => roots
  | .mk (.finite (.error _)) .built | .mk (.cyclic (.error _)) .built => .known 1
  | .mk _ .built => .unknown
termination_by g => sizeOf g

/-- Root counts of weighted alternatives ignore their choice weights. -/
def weightedRootCounts : List (Int × Generator) → List RootCount
  | [] => []
  | (_, generator) :: rest => rootCount generator :: weightedRootCounts rest
termination_by gs => sizeOf gs

/-- Root counts of uniformly chosen alternatives. -/
def rootCounts : List Generator → List RootCount
  | [] => []
  | generator :: rest => rootCount generator :: rootCounts rest
termination_by gs => sizeOf gs
end

/-- Applicative positions flatten maps and pays but treat choices as one position. -/
def spineRoots : Generator → List RootCount
  | .mk _ .lifted => []
  | .mk _ (.mapped inner) | .mk _ (.paid inner) => spineRoots inner
  | .mk _ (.applied left right) => spineRoots left ++ spineRoots right
  | generator => [rootCount generator]
termination_by g => sizeOf g

/-- The source arity counts applicative positions, not the roots they contribute. -/
def spineArity (generator : Generator) : Nat := (spineRoots generator).length

/-- Every observed applicative position must contribute exactly one root. -/
def alignedSpine (generator : Generator) : Bool := (spineRoots generator).all (· == .known 1)

/-- A product can forward observations only from its unique one-root position. -/
def oneTermPart (requested : Bool) (generator : Generator) : Option Nat :=
  let counts := spineRoots generator
  if requested && counts.all (fun count => count == .known 0 || count == .known 1) then
    match (counts.zipIdx.filter fun entry => entry.1 == .known 1).map Prod.snd with
    | [position] => some position
    | _ => none
  else none

mutual
/-- Detect integer leaves in recipes. Built and imported automata stop the traversal. -/
def containsIntegers : Generator → Bool
  | .mk _ .integers => true
  | .mk _ (.mapped inner) | .mk _ (.paid inner) | .mk _ (.closed inner) | .mk _ (.closedBy inner) =>
      containsIntegers inner
  | .mk _ (.applied left right) => containsIntegers left || containsIntegers right
  | .mk _ (.chosen alternatives) => weightedContains alternatives
  | .mk _ (.uniform alternatives) => anyContains alternatives
  | _ => false
termination_by g => sizeOf g

/-- Integer-leaf detection visits every weighted alternative, including zero weights. -/
def weightedContains : List (Int × Generator) → Bool
  | [] => false
  | (_, generator) :: rest => containsIntegers generator || weightedContains rest
termination_by gs => sizeOf gs

/-- Integer-leaf detection visits every uniform alternative. -/
def anyContains : List Generator → Bool
  | [] => false
  | generator :: rest => containsIntegers generator || anyContains rest
termination_by gs => sizeOf gs
end

/-- The externally visible entry path selected by `compile`. -/
inductive EntryRoute where
  | unchanged | closed | openThenClose
  deriving DecidableEq, Repr

/-- Top-level compile returns every already-built language unchanged, including errors. -/
def entryRoute (generator : Generator) : EntryRoute :=
  if !deferred generator then .unchanged
  else if containsIntegers generator then .openThenClose else .closed

/-- The exact work branch of `compileGenOnce`. -/
inductive ClosedRoute where
  | unchangedKey | built | lifted | mapped | paid | weightedChoice | uniformChoice
  | spine (forwardedPosition : Option Nat) | node | computedNode | imported | impossibleInteger
  deriving DecidableEq, Repr

/-- Route a closed recipe with the source's no-observation shortcut. -/
def closedRoute (requested : Bool) (generator : Generator) : ClosedRoute :=
  if !deferred generator && !requested then .unchangedKey
  else match recipe generator with
    | .built => .built
    | .lifted => .lifted
    | .mapped _ => .mapped
    | .paid _ => .paid
    | .applied _ _ => .spine (oneTermPart requested generator)
    | .chosen _ => .weightedChoice
    | .uniform _ => .uniformChoice
    | .closed _ => .node
    | .closedBy _ => .computedNode
    | .imported => .imported
    | .integers => .impossibleInteger

/-- The exact work branch of `compileOpen`. -/
inductive OpenRoute where
  | closedAdapter | integer | mapped | paid | weightedChoice | uniformChoice
  | spine (forwardedPosition : Option Nat) | node | computedNode | impossible
  deriving DecidableEq, Repr

/-- Route an open recipe, or adapt a closed generator to an empty-variable reader. -/
def openRoute (requested : Bool) (generator : Generator) : OpenRoute :=
  if !containsIntegers generator then .closedAdapter
  else match recipe generator with
    | .integers => .integer
    | .mapped _ => .mapped
    | .paid _ => .paid
    | .applied _ _ => .spine (oneTermPart requested generator)
    | .chosen _ => .weightedChoice
    | .uniform _ => .uniformChoice
    | .closed _ => .node
    | .closedBy _ => .computedNode
    | _ => .impossible

/-- Integer detection prevents the source's unreachable closed-integer branch. -/
theorem closed_integer_unreachable (requested : Bool) (generator : Generator)
    (closed : containsIntegers generator = false) :
    closedRoute requested generator ≠ .impossibleInteger := by
  cases generator with
  | mk state description =>
      cases description <;> simp [closedRoute, recipe, containsIntegers] at closed ⊢
      all_goals split <;> simp_all

/-- Integer detection prevents every impossible open-path recipe branch. -/
theorem open_impossible_unreachable (requested : Bool) (generator : Generator) :
    openRoute requested generator ≠ .impossible := by
  cases generator with
  | mk state description =>
      cases description <;> simp [openRoute, recipe, containsIntegers]
      all_goals split <;> simp_all

/-- An imported automaton never enters the integer-hole compilation path. -/
theorem imported_is_closed (state : Source) : containsIntegers (.mk state .imported) = false := by
  simp [containsIntegers]

/-- A successful recursive import is returned unchanged by top-level compilation. -/
theorem recursive_passthrough (description : Recipe) :
    entryRoute (.mk (.cyclic (.ok ())) description) = .unchanged := by
  simp [entryRoute, deferred, source]

/-- The compile API does not unwrap an existing source error other than the deferred marker. -/
theorem failed_source_passthrough (description : Recipe) (error : Error)
    (different : error ≠ .requiresCompilation) :
    entryRoute (.mk (.finite (.error error)) description) = .unchanged := by
  cases error <;> simp_all [entryRoute, deferred, source]

/-- A child shape fails before child compilation only when a path is observed. -/
def shapeCheck (requestedBelow : Bool) (child : Generator) : Except Error Unit :=
  if requestedBelow && !alignedSpine child then .error .childNotOneTerm else .ok ()

/-- Unobserved children impose no one-term requirement. -/
theorem unobserved_shape (child : Generator) : shapeCheck false child = .ok () := by
  simp [shapeCheck]

/-- Observed children pass shape validation exactly when their spine is aligned. -/
theorem observed_shape (child : Generator) :
    shapeCheck true child = .ok () ↔ alignedSpine child = true := by
  cases h : alignedSpine child <;> simp [shapeCheck, h]

/-- The grouped cardinality result used by choices and spine short-circuiting. -/
inductive Groups where
  | finite (counts : Except Error (List Nat))
  | cyclic (result : Except Error Unit)
  deriving Repr

/-- A grouped recursive source is not a finite count table. -/
def cardinalities : Groups → Except Error (List Nat)
  | .finite counts => counts
  | .cyclic (.error error) => .error error
  | .cyclic (.ok _) => .error .unbounded

/-- The source recognizes the empty error and zero counts as empty; other errors stay live. -/
def emptyGroups (groups : Groups) : Bool :=
  match cardinalities groups with
  | .error .empty => true
  | .ok counts => counts.all (· == 0)
  | .error _ => false

/-- Every cyclic representation selects recursive uniform-choice behavior, even when it contains an error. -/
def recursiveGroups : Groups → Bool
  | .cyclic _ => true
  | _ => false

/-- Uniform choices use finite member counts unless any alternative is recursive. -/
def uniformWeights (groups : List Groups) : List Nat :=
  if groups.any recursiveGroups then groups.map (fun _ => 1)
  else groups.map fun group => match cardinalities group with
    | .error _ => 1
    | .ok counts => counts.sum

/-- Choices retain original alternative indices when they remove empty alternatives. -/
def chooseGroups (weighted : List (Int × Groups)) : List (Nat × Int × Groups) :=
  (weighted.zipIdx.filter fun entry => !emptyGroups entry.1.2).map
    fun ((weight, group), index) => (index, weight, group)

/-- Empty filtering retains exactly the source alternatives that are not known empty. -/
theorem chooseGroups_member (weighted : List (Int × Groups)) (index : Nat) (weight : Int) (group : Groups) :
    (index, weight, group) ∈ chooseGroups weighted ↔
      ((weight, group), index) ∈ weighted.zipIdx ∧ emptyGroups group = false := by
  simp only [chooseGroups, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨⟨w, g⟩, i⟩, member, equal⟩
    simp only [Prod.mk.injEq] at equal
    rcases equal with ⟨rfl, rfl, rfl⟩
    simpa using member
  · rintro ⟨member, kept⟩
    exact ⟨((weight, group), index), by simpa [kept] using member, rfl⟩

/-- Recursive alternatives force equal branch weights before empty alternatives are removed. -/
theorem recursive_uniform_weights (groups : List Groups)
    (recursive : groups.any recursiveGroups = true) :
    uniformWeights groups = groups.map (fun _ => 1) := by
  simp [uniformWeights, recursive]

/-- A nonempty construction error is retained by choice compilation. -/
theorem choice_retains_error (error : Error) (different : error ≠ .empty) :
    emptyGroups (.finite (.error error)) = false := by
  cases error <;> simp_all [emptyGroups, cardinalities]

/-- Execute the source spine product with an explicit delayed right compilation. -/
def compileProduct (left : Except Error Groups) (right : Unit → Except Error Groups)
    (join : Groups → Groups → Groups) : Except Error Groups := do
  let functions ← left
  if emptyGroups functions then pure (.finite (.error .empty))
  else do
    let arguments ← right ()
    pure (join functions arguments)

/-- A failed function side prevents every request to the argument compiler. -/
theorem product_error (error : Error) (right : Unit → Except Error Groups)
    (join : Groups → Groups → Groups) :
    compileProduct (.error error) right join = .error error := rfl

/-- An empty function side prevents an argument-side failure from escaping. -/
theorem product_empty (left : Groups) (empty : emptyGroups left = true)
    (right : Unit → Except Error Groups) (join : Groups → Groups → Groups) :
    compileProduct (.ok left) right join = .ok (.finite (.error .empty)) := by
  simp [compileProduct, empty] <;> rfl

/-- Classify a sparse result only after actual identities are known. -/
def constraintDecision (ambiguous : Bool) (actual semantic allYes allNo : Guards.Verdict)
    (mixedLeaf equalities same : Bool) : Except Error Bool :=
  if ambiguous then .error .solverUnknown else
  match actual with
  | .yes => .ok true
  | .no => .ok false
  | .unknown =>
      if semantic = .unknown then .error .solverUnknown
      else if allYes ≠ .unknown ∧ allNo ≠ .unknown then .error .solverUnknown
      else if mixedLeaf then .error .childNotOneTerm
      else if equalities then .error .relationalEquality
      else if same then .error .syntacticEquality
      else .error .solverUnknown

/-- Successful retention requires known actual identities and a sparse Yes. -/
theorem constraintDecision_accept (ambiguous : Bool) (actual semantic allYes allNo : Guards.Verdict)
    (mixedLeaf equalities same : Bool) :
    constraintDecision ambiguous actual semantic allYes allNo mixedLeaf equalities same = .ok true ↔
      ambiguous = false ∧ actual = .yes := by
  cases ambiguous <;> cases actual <;> cases semantic <;> cases allYes <;> cases allNo <;>
    cases mixedLeaf <;> cases equalities <;> cases same <;> simp [constraintDecision]

/-- Unresolved identities cannot become either a retained or an empty group. -/
theorem ambiguous_solver_unknown (actual semantic allYes allNo : Guards.Verdict)
    (mixedLeaf equalities same : Bool) :
    constraintDecision true actual semantic allYes allNo mixedLeaf equalities same = .error .solverUnknown := rfl

/-- An unknown guard never becomes successful rejection or acceptance. -/
theorem constraintDecision_unknown (ambiguous : Bool) (semantic allYes allNo : Guards.Verdict)
    (mixedLeaf equalities same : Bool) (answer : Bool) :
    constraintDecision ambiguous .unknown semantic allYes allNo mixedLeaf equalities same ≠ .ok answer := by
  cases ambiguous <;> cases semantic <;> cases allYes <;> cases allNo <;>
    cases mixedLeaf <;> cases equalities <;> cases same <;> simp [constraintDecision]

/-- Semantic uncertainty takes precedence over unavailable structural observations. -/
theorem semantic_unknown_first (ambiguous : Bool) (allYes allNo : Guards.Verdict) (mixedLeaf equalities same : Bool) :
    constraintDecision ambiguous .unknown .unknown allYes allNo mixedLeaf equalities same = .error .solverUnknown := by
  cases ambiguous <;> simp [constraintDecision]

/-- User labels, integer placeholders, and the engine's private labels. -/
inductive FillLabel (Symbol : Type) where
  | user (symbol : Symbol)
  | placeholder
  | internal (tag : Nat)

mutual
/-- Fill placeholders in source order and specialize each user label before its children. -/
def fillTerm (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) : Language.Term (FillLabel Symbol) → List Int × Language.Term (FillLabel Symbol)
  | .node .placeholder children => match point with
      | value :: rest => (rest, .node (.user (literal value)) [])
      | [] => let filled := fillForest literal exactLabel [] children
              (filled.1, .node .placeholder filled.2)
  | .node (.user symbol) children =>
      let filled := fillForest literal exactLabel point children
      (filled.1, .node (.user (exactLabel point symbol)) filled.2)
  | .node (.internal tag) children =>
      let filled := fillForest literal exactLabel point children
      (filled.1, .node (.internal tag) filled.2)
termination_by term => sizeOf term

/-- Fill successive child subtrees with successive suffixes of the integer point. -/
def fillForest (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) : List (Language.Term (FillLabel Symbol)) →
      List Int × List (Language.Term (FillLabel Symbol))
  | [] => (point, [])
  | term :: rest =>
      let first := fillTerm literal exactLabel point term
      let others := fillForest literal exactLabel first.1 rest
      (others.1, first.2 :: others.2)
termination_by terms => sizeOf terms
end

mutual
/-- Count the placeholder positions consumed by the source filler. -/
def holes : Language.Term (FillLabel Symbol) → Nat
  | .node .placeholder _ => 1
  | .node _ children => forestHoles children
termination_by term => sizeOf term

/-- Count placeholder positions in an ordered forest. -/
def forestHoles : List (Language.Term (FillLabel Symbol)) → Nat
  | [] => 0
  | term :: rest => holes term + forestHoles rest
termination_by terms => sizeOf terms
end

mutual
/-- Filling consumes exactly the available prefix for the term's placeholder positions. -/
theorem fillTerm_remaining (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (term : Language.Term (FillLabel Symbol)) :
    (fillTerm literal exactLabel point term).1 = point.drop (holes term) := by
  cases term with
  | node label children =>
      cases label with
      | placeholder => cases point <;> simp [fillTerm, holes, fillForest_remaining literal exactLabel [] children]
      | user symbol => simp [fillTerm, holes, fillForest_remaining literal exactLabel point children]
      | internal tag => simp [fillTerm, holes, fillForest_remaining literal exactLabel point children]
termination_by sizeOf term

/-- Consecutive subtrees consume consecutive prefixes without skipping or reusing values. -/
theorem fillForest_remaining (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (terms : List (Language.Term (FillLabel Symbol))) :
    (fillForest literal exactLabel point terms).1 = point.drop (forestHoles terms) := by
  cases terms with
  | nil => simp [fillForest, forestHoles]
  | cons term rest =>
      simp only [fillForest]
      rw [fillForest_remaining literal exactLabel _ rest, fillTerm_remaining literal exactLabel point term]
      simp [forestHoles, List.drop_drop, Nat.add_comm]
termination_by sizeOf terms
end

mutual
/-- The only placeholders left unfilled are those for which no coordinate was supplied. -/
theorem fillTerm_holes (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (term : Language.Term (FillLabel Symbol)) :
    holes (fillTerm literal exactLabel point term).2 = holes term - point.length := by
  cases term with
  | node label children =>
      cases label with
      | placeholder => cases point <;> simp [fillTerm, holes, forestHoles]
      | user symbol => simp [fillTerm, holes, fillForest_holes literal exactLabel point children]
      | internal tag => simp [fillTerm, holes, fillForest_holes literal exactLabel point children]
termination_by sizeOf term

/-- The forest filler removes one placeholder per supplied coordinate until either list ends. -/
theorem fillForest_holes (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (terms : List (Language.Term (FillLabel Symbol))) :
    forestHoles (fillForest literal exactLabel point terms).2 = forestHoles terms - point.length := by
  cases terms with
  | nil => simp [fillForest, forestHoles]
  | cons term rest =>
      simp only [fillForest, forestHoles]
      rw [fillTerm_holes literal exactLabel point term, fillForest_holes literal exactLabel _ rest,
        fillTerm_remaining literal exactLabel point term, List.length_drop]
      omega
termination_by sizeOf terms
end

/-- A point of the declared hole count fills every placeholder and consumes every coordinate. -/
theorem fillTerm_exact (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (term : Language.Term (FillLabel Symbol)) (dimension : point.length = holes term) :
    (fillTerm literal exactLabel point term).1 = [] ∧ holes (fillTerm literal exactLabel point term).2 = 0 := by
  rw [fillTerm_remaining, fillTerm_holes, ← dimension]
  simp

/-- The number and known cardinality of variables carried by an open key. -/
structure OpenInfo where
  variables : Nat
  points : Option Nat
  deriving DecidableEq, Repr

/-- Results from the actual integer counter, including an unbounded integer domain. -/
inductive IntegerCount where
  | finite (count : Nat)
  | unbounded
  | failed (cause : Nat)
  deriving DecidableEq, Repr

/-- An integer leaf may remain unbounded for a parent contract to constrain it. -/
def integerGroup : IntegerCount → Except Error (Option OpenInfo)
  | .finite 0 => .ok none
  | .finite (count + 1) => .ok (some ⟨1, some (count + 1)⟩)
  | .unbounded => .ok (some ⟨1, none⟩)
  | .failed cause => .error (.uncountable cause)

/-- Only an empty counted integer domain removes the leaf group. -/
theorem integerGroup_empty (result : IntegerCount) :
    integerGroup result = .ok none ↔ result = .finite 0 := by
  cases result with
  | finite count => cases count <;> simp [integerGroup]
  | unbounded => simp [integerGroup]
  | failed cause => simp [integerGroup]

/-- An unbounded integer leaf is retained on the open path. -/
theorem integerGroup_unbounded : integerGroup .unbounded = .ok (some ⟨1, none⟩) := rfl

/-- The source settlement choice after it has counted the combined constraint. -/
inductive Settlement where
  | drop
  | open (variables points : Nat) (share : Rat)
  | closed (closeWith : Option Nat) (share : Rat)
  deriving DecidableEq, Repr

/-- The source divides accepted points by the known child point counts, using one for unbounded children. -/
def retainedShare (found : Nat) (children : List OpenInfo) : Rat :=
  (found : Rat) / ((children.map (fun key => key.points.getD 1)).prod : Nat)

/-- Settle a tuple by dropping it, retaining its variables, or closing its finite points. -/
def settle (symbolic : Bool) (children : List OpenInfo) (found : Nat) : Settlement :=
  if found = 0 then .drop
  else if symbolic then .open (children.map OpenInfo.variables |>.sum) found (retainedShare found children)
  else .closed (if (children.map OpenInfo.variables).sum = 0 then none else some found)
    (retainedShare found children)

/-- Settlement drops a tuple exactly when the counter found no integer points. -/
theorem settle_drop (symbolic : Bool) (children : List OpenInfo) (found : Nat) :
    settle symbolic children found = .drop ↔ found = 0 := by
  cases symbolic <;> by_cases empty : found = 0 <;> simp [settle, empty]

/-- A constructor with no open variables does not select an artificial integer point. -/
theorem settle_zero_variables (children : List OpenInfo) (found : Nat)
    (nonempty : found ≠ 0) (closed : (children.map OpenInfo.variables).sum = 0) :
    settle false children found = .closed none (retainedShare found children) := by
  simp [settle, nonempty, closed]

/-- Dispatch the error shell of `closeOpen` to its finite worker. -/
def closeGroupedState (finiteWorker : List Nat → Except Error Groups) : Groups → Except Error Groups
  | .cyclic _ => .ok (.finite (.error .unbounded))
  | .finite (.error error) => .ok (.finite (.error error))
  | .finite (.ok counts) => finiteWorker counts

/-- An existing group error remains nested inside a successful compile result. -/
theorem close_preserves_stored_error (finiteWorker : List Nat → Except Error Groups) (error : Error) :
    closeGroupedState finiteWorker (.finite (.error error)) = .ok (.finite (.error error)) := rfl

/-- The open closing path rejects every cyclic group, including cyclic groups with another stored error. -/
theorem close_recursive (finiteWorker : List Nat → Except Error Groups) (result : Except Error Unit) :
    closeGroupedState finiteWorker (.cyclic result) = .ok (.finite (.error .unbounded)) := rfl

/-- Metadata retained for one source outcome before observation grouping. -/
structure Member (Value : Type) where
  mass : Rat
  size : Nat
  value : Value
  sizeWeight : Option Rat

/-- The per-size fields relevant to the source's bucket observation and product path. -/
structure BucketMeta where
  mass : Rat
  size : Nat
  count : Nat
  atomic : Bool
  sizeMass : Option Rat
  deriving DecidableEq, Repr

/-- Rebuild one observed member with its original size and the source's metadata rule. -/
def observedMember (atomicSource : Bool) (member : Member Value) : BucketMeta :=
  ⟨member.mass, member.size, 1, atomicSource,
    if atomicSource then none else member.sizeWeight⟩

/-- Observation reconstruction retains each member's exact source mass and size. -/
theorem observedMember_preserves (atomicSource : Bool) (member : Member Value) :
    (observedMember atomicSource member).mass = member.mass ∧
      (observedMember atomicSource member).size = member.size ∧
      (observedMember atomicSource member).count = 1 := by
  simp [observedMember]

/-- An atomic source deliberately does not attach its per-member weight to the bucket mass index. -/
theorem observed_atomic_no_sizeMass (member : Member Value) :
    (observedMember true member).sizeMass = none := rfl

/-- A non-atomic source carries any available source within-size weight into its singleton bucket. -/
theorem observed_nonatomic_sizeMass (member : Member Value) :
    (observedMember false member).sizeMass = member.sizeWeight := rfl

/-- `bucketMassIndex` uses structural member count when no explicit size mass exists. -/
def bucketSizeMass (bucket : BucketMeta) : Rat := bucket.sizeMass.getD (bucket.count : Rat)

/-- The metadata branch of `Grouped.pairBucket`, for one size class on each side. -/
def pairBucket (left right : BucketMeta) : BucketMeta :=
  ⟨left.mass * right.mass, left.size + right.size, left.count * right.count, false,
    if left.sizeMass.isSome || right.sizeMass.isSome then
      some (bucketSizeMass left * bucketSizeMass right)
    else none⟩

/-- Pairing keeps exact unbounded mass, additive size, and multiplicative member count. -/
theorem pairBucket_metadata (left right : BucketMeta) :
    (pairBucket left right).mass = left.mass * right.mass ∧
      (pairBucket left right).size = left.size + right.size ∧
      (pairBucket left right).count = left.count * right.count := by
  simp [pairBucket]

/-- Without explicit metadata on either side, pairing leaves no per-size mass information. -/
theorem pairBucket_no_sizeMass (left right : BucketMeta)
    (hl : left.sizeMass = none) (hr : right.sizeMass = none) :
    (pairBucket left right).sizeMass = none ∧ (pairBucket left right).atomic = false := by
  simp [pairBucket, hl, hr]

/-- A constructor pays one source choice and shifts any stored mass to that size. -/
def payBucket (bucket : BucketMeta) : BucketMeta := { bucket with size := bucket.size + 1 }

/-- At one common size, a merge retains all-atomic mass or falls back to size-class weights. -/
def mergedSizeMasses (buckets : List BucketMeta) : List Rat :=
  if buckets.any (fun bucket => bucket.sizeMass.isSome) then buckets.map bucketSizeMass
  else if buckets.all (fun bucket => bucket.atomic) then buckets.map BucketMeta.mass
  else buckets.map (fun bucket => (bucket.count : Rat))

/-- Normalize the first branch mass as a finite exact-choice probability. -/
def firstProbability : List Rat → Rat
  | [] => 0
  | first :: rest => first / (first + rest.sum)

/-- Metadata of the source's observed 9:1 atomic child paired with one ordinary leaf. -/
def observedAtomicPair : List BucketMeta :=
  let left : List (Member Bool) := [⟨9 / 10, 1, true, some (9 / 5)⟩, ⟨1 / 10, 1, false, some (1 / 5)⟩]
  let right : BucketMeta := ⟨1, 1, 1, false, none⟩
  left.map fun member => payBucket (pairBucket (observedMember true member) right)

/-- The actual metadata branches preserve sizes and unbounded probability but change bounded probability. -/
theorem atomic_pair_metadata_counterexample :
    observedAtomicPair.map BucketMeta.size = [3, 3] ∧
      observedAtomicPair.map BucketMeta.sizeMass = [none, none] ∧
      firstProbability (observedAtomicPair.map BucketMeta.mass) = 9 / 10 ∧
      firstProbability (mergedSizeMasses observedAtomicPair) = 1 / 2 ∧
      (9 / 10 : Rat) ≠ 1 / 2 := by
  decide +kernel

/-- Closing points preserves outer mass and multiplies cardinalities and per-size weights. -/
def closeBucket (variables points : Nat) (bucket : BucketMeta) : BucketMeta :=
  ⟨bucket.mass, bucket.size + variables, bucket.count * points, false,
    bucket.sizeMass.map (fun mass => mass * (points : Rat))⟩

/-- Settlement without point closure changes only the tuple's outer retained mass. -/
def retainBucket (share : Rat) (bucket : BucketMeta) : BucketMeta :=
  { bucket with mass := bucket.mass * share }

/-- The metadata passed to `closedMasses` agrees with finite Cartesian point closure. -/
theorem closeBucket_metadata (variables points : Nat) (bucket : BucketMeta) :
    (closeBucket variables points bucket).mass = bucket.mass ∧
      (closeBucket variables points bucket).size = bucket.size + variables ∧
      (closeBucket variables points bucket).count = bucket.count * points ∧
      (closeBucket variables points bucket).sizeMass =
        bucket.sizeMass.map (fun mass => mass * (points : Rat)) := by
  simp [closeBucket]

/-- An observation regrouping with complete retained per-size metadata preserves event probability. -/
theorem observation_grouping_probability [DecidableEq Key]
    (key : Rat × (Nat × Value) → Key) (members : Probability.Distribution (Nat × Value))
    (positive : ∀ entry ∈ members, 0 < entry.1) (event : Nat × Value → Bool) :
    Probability.eventMass event (SizeMass.classSampler (SizeMass.splitClass key members)) =
      Probability.eventMass event (Probability.normalize members) := by
  exact SizeMass.split_merge_probability key members positive event

/-- The common positive-denominator scaling used for observation choices does not change their distribution. -/
theorem observation_scale_probability (scale : Rat) (nonzero : scale ≠ 0)
    (members : Probability.Distribution Value) (event : Value → Bool) :
    Probability.eventMass event (Probability.normalize (Probability.scale scale members)) =
      Probability.eventMass event (Probability.normalize members) := by
  rw [Probability.normalize_scale scale members nonzero]

/-- Finite point closure in the recipe compiler uses the proved actual lattice decoder. -/
theorem integer_closure_exact {Value : Type} (names : List FullSyntax.Name) (formula : FullSyntax.Formula)
    (compiled : LatticeSigned.Checked)
    (parsed : FullSyntax.signed (LatticeInput.variableOf names) true formula = .ok compiled)
    (levels : List (List LatticePiece.Piece))
    (built : LatticeLevels.buildLevels names.length (LatticeInput.initial compiled)
      (LatticeInput.initial_valid compiled) = .ok levels)
    (sources : List (ZeroSize.OpenOutcome names.length Value)) (size : Nat) (value : Value) :
    (size, value) ∈ ZeroSize.closePoints (LatticeSelect.compiledPoints names.length levels) sources ↔
      ∃ source, source ∈ sources ∧ ∃ tuple,
        FullSyntax.Holds FullSyntax.integerModel
          (LatticeInput.nameValues names (LatticeSelect.assignTuple (fun _ => 0) 0 (List.ofFn tuple))) formula ∧
        size = source.1 + names.length ∧ value = source.2 tuple := by
  exact LatticeSelect.closePoints_exact names formula compiled parsed levels built sources size value

end MicroCFTA.RecipeCompile
