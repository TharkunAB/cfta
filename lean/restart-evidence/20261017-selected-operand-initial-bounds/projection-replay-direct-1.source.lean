import MicroCFTA.SourceEqualityProjectionWorkerComplete

/-!
# Static projection worker fuel and shared exact read certificates

The worker bound depends only on the signed path length. The certificates
record shared row-read fuel at the exact sites of a completed physical graph.
They impose no global closedness condition on unselected source operands.
-/
namespace MicroCFTA.SourceCurrentProjectionNumericReplay
open InternedConstructorTemplates
open SourceEqualityProjectionGraph (Project ProjectRows Forest select)
open SourceEqualityProjectionRead (Read)
open SourceEqualityProjectionUnion (ReadAll Union)
open SourceEqualityRequiredHead (Head)
open SourceEqualityRequiredCache (Ordinary)
open SourceEqualityRequiredGraph (Recursive)
open SourceEqualityProjectionWorker (readAll union rows project forest)
open SourceEqualityRequiredWorker (Result work head)
variable {Symbol Guard : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every path step pays for one head exposure and one ordinary selected step. -/
def workFuel (path : List Int) : Nat := 2 * path.length + 1

/-- A demanded row read returns its exact rows and full heap at the shared fuel. -/
abbrev ReadReady (shared : Nat) {value : Value Symbol Guard} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)} (_actual : Read value before edges after) : Prop :=
  MergedFreshOrdinaryExposure.nodeEdges shared value before = .done edges after

/-- Ordered operand reads use one shared row-read fuel. -/
inductive ReadAllReady (shared : Nat) :
    {values : List (Value Symbol Guard)} → {before : State Symbol Guard} → {edges : List (EdgeValue Symbol Guard)} →
      {after : State Symbol Guard} → ReadAll values before edges after → Prop where
  /-- The empty scan performs no read. -/
  | nil (state : State Symbol Guard) : ReadAllReady shared (.nil (state := state))
  /-- Each actual read precedes the exact remaining scan. -/
  | cons {first : Read value before edges middle} {rest : ReadAll values middle more after}
      (firstReady : ReadReady shared first) (restReady : ReadAllReady shared rest) :
      ReadAllReady shared (.cons first rest)

/-- A source union keeps its actual final node construction. -/
inductive UnionReady (shared : Nat) :
    {values : List (Value Symbol Guard)} → {before : State Symbol Guard} → {result : Value Symbol Guard} →
      {after : State Symbol Guard} → Union values before result after → Prop where
  /-- The actual ordered row reads precede the literal constructor. -/
  | node {read : ReadAll values before edges middle} {built : run (makeNode edges) middle = (result, after)}
      (ready : ReadAllReady shared read) : UnionReady shared (.node read built)

/-- A recursive exposure reads exact rows and returns an ordinary value. -/
inductive HeadReady (shared : Nat) :
    {value : Value Symbol Guard} → {before : State Symbol Guard} → {result : Value Symbol Guard} →
      {after : State Symbol Guard} → Head value before result after → Prop where
  /-- Ordinary exposure prevents another same-path recursive head step. -/
  | read {oldFuel : Nat} {edges : List (EdgeValue Symbol Guard)} {middle : State Symbol Guard}
      {exposed : MergedFreshOrdinaryExposure.nodeEdges oldFuel value before = .done edges middle}
      {rebuilt : run (makeNode edges) middle = (result, after)}
      (ready : ReadReady shared (.done oldFuel exposed)) (ordinary : Ordinary result) :
      HeadReady shared (.read oldFuel edges middle exposed rebuilt)

mutual
/-- Projection certificates retain every demanded branch at its exact heap. -/
inductive ProjectReady (shared : Nat) :
    {path : List Int} → {value : Value Symbol Guard} → {before : State Symbol Guard} →
      {result : Value Symbol Guard} → {after : State Symbol Guard} → Project path value before result after → Prop where
  /-- Empty paths return without row reads. -/
  | root (value : Value Symbol Guard) (state : State Symbol Guard) : ProjectReady shared (.root (value := value) (state := state))
  /-- Empty values return without row reads. -/
  | empty (index : Int) (path : List Int) (state : State Symbol Guard) :
      ProjectReady shared (.empty (index := index) (path := path) (state := state))
  /-- The actual signed row scan precedes the actual union. -/
  | ordinary {rowGraph : ProjectRows path index edges before values middle}
      {unionGraph : Union values middle result after}
      (rowsReady : RowsReady shared rowGraph) (unionReady : UnionReady shared unionGraph) :
      ProjectReady shared (.ordinary (entry := entry) (depth := depth) (free := free) rowGraph unionGraph)
  /-- The same-path body starts at the actual ordinary exposed value. -/
  | recursive (recursive : Recursive original) {headGraph : Head original before exposed middle}
      {bodyGraph : Project (index :: path) exposed middle result after}
      (headReady : HeadReady shared headGraph) (bodyReady : ProjectReady shared bodyGraph) :
      ProjectReady shared (.recursive recursive headGraph bodyGraph)

/-- Row scans retain missing signed positions and literal selected-child order. -/
inductive RowsReady (shared : Nat) :
    {path : List Int} → {index : Int} → {edges : List (EdgeValue Symbol Guard)} → {before : State Symbol Guard} →
      {values : List (Value Symbol Guard)} → {after : State Symbol Guard} → ProjectRows path index edges before values after → Prop where
  /-- The empty row scan returns the empty list. -/
  | nil (path : List Int) (index : Int) (state : State Symbol Guard) :
      RowsReady shared (.nil (path := path) (index := index) (state := state))
  /-- A missing child performs no recursive projection. -/
  | missing (absent : select edge.children index = none) {rest : ProjectRows path index edges before values after}
      (restReady : RowsReady shared rest) : RowsReady shared (.missing absent rest)
  /-- A selected child returns before the remaining row scan starts. -/
  | selected (found : select edge.children index = some child)
      {first : Project path child before result middle} {rest : ProjectRows path index edges middle values after}
      (firstReady : ProjectReady shared first) (restReady : RowsReady shared rest) :
      RowsReady shared (.selected found first rest)
end

/-- Forest certificates keep root union, missing, and selected branches distinct. -/
inductive ForestReady (shared : Nat) :
    {path : List Int} → {values : List (Value Symbol Guard)} → {before : State Symbol Guard} →
      {result : Value Symbol Guard} → {after : State Symbol Guard} → Forest path values before result after → Prop where
  /-- A root forest request executes the actual source union. -/
  | root {actual : Union values before result after} (ready : UnionReady shared actual) : ForestReady shared (.root actual)
  /-- A missing signed root position returns Empty. -/
  | missing (absent : select values index = none) (path : List Int) (state : State Symbol Guard) :
      ForestReady shared (.missing (path := path) (state := state) absent)
  /-- A selected root retains the exact child projection. -/
  | selected (found : select values index = some value) {actual : Project path value before result after}
      (ready : ProjectReady shared actual) : ForestReady shared (.selected found actual)

/-- More shared read fuel retains the same rows and full heap. -/
theorem ReadReady.mono {first last : Nat} {value : Value Symbol Guard} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)} {actual : Read value before edges after}
    (ready : ReadReady first actual) (increase : first ≤ last) : ReadReady last actual := by
  have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable first (last - first) value before (by rw [ready]; trivial)
  rw [show first + (last - first) = last by omega] at stable
  exact stable.trans ready

/-- More shared read fuel retains the exact ordered operand scan. -/
theorem ReadAllReady.mono {first last : Nat} {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)} {actual : ReadAll values before edges after}
    (ready : ReadAllReady first actual) (increase : first ≤ last) : ReadAllReady last actual := by
  induction ready with
  | nil state => exact .nil state
  | cons firstReady restReady ih => exact .cons (ReadReady.mono firstReady increase) ih

/-- More shared read fuel retains the actual union constructor. -/
theorem UnionReady.mono {first last : Nat} {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {result : Value Symbol Guard} {actual : Union values before result after}
    (ready : UnionReady first actual) (increase : first ≤ last) : UnionReady last actual := by
  cases ready with
  | node readReady => exact .node (readReady.mono increase)

/-- More shared read fuel retains the exact ordinary exposed value. -/
theorem HeadReady.mono {first last : Nat} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    {actual : Head value before result after} (ready : HeadReady first actual) (increase : first ≤ last) :
    HeadReady last actual := by
  cases ready with
  | read readReady ordinary => exact .read (ReadReady.mono readReady increase) ordinary

/-- Recursive exposure has the recorded ordinary result. -/
theorem HeadReady.ordinary {shared : Nat} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    {actual : Head value before result after} (ready : HeadReady shared actual) : Ordinary result := by
  cases ready with
  | read readReady ordinary => exact ordinary

/-- More shared read fuel retains every actual projection branch. -/
theorem ProjectReady.mono {first last : Nat} {path : List Int} {value result : Value Symbol Guard}
    {before after : State Symbol Guard} {actual : Project path value before result after}
    (ready : ProjectReady first actual) (increase : first ≤ last) : ProjectReady last actual := by
  induction ready using ProjectReady.rec
      (motive_2 := fun {path index edges before values after} actual _ => RowsReady last actual) with
  | root value state => exact .root value state
  | empty index path state => exact .empty index path state
  | ordinary rowsReady unionReady ih => exact .ordinary ih (unionReady.mono increase)
  | recursive recursive headReady bodyReady ih => exact .recursive recursive (headReady.mono increase) ih
  | nil path index state => exact .nil path index state
  | missing absent restReady ih => exact .missing absent ih
  | selected found firstReady restReady firstIH restIH => exact .selected found firstIH restIH

/-- More shared read fuel retains signed row selection and source order. -/
theorem RowsReady.mono {first last : Nat} {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} {values : List (Value Symbol Guard)}
    {actual : ProjectRows path index edges before values after}
    (ready : RowsReady first actual) (increase : first ≤ last) : RowsReady last actual := by
  induction ready using RowsReady.rec
      (motive_1 := fun {path value before result after} actual _ => ProjectReady last actual) with
  | root value state => exact .root value state
  | empty index path state => exact .empty index path state
  | ordinary rowsReady unionReady ih => exact .ordinary ih (unionReady.mono increase)
  | recursive recursive headReady bodyReady ih => exact .recursive recursive (headReady.mono increase) ih
  | nil path index state => exact .nil path index state
  | missing absent restReady ih => exact .missing absent ih
  | selected found firstReady restReady firstIH restIH => exact .selected found firstIH restIH

/-- More shared read fuel retains each actual forest branch. -/
theorem ForestReady.mono {first last : Nat} {path : List Int} {values : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {result : Value Symbol Guard} {actual : Forest path values before result after}
    (ready : ForestReady first actual) (increase : first ≤ last) : ForestReady last actual := by
  cases ready with
  | root unionReady => exact .root (unionReady.mono increase)
  | missing absent path state => exact .missing absent path state
  | selected found projectReady => exact .selected found (projectReady.mono increase)

/-- A demanded row read replays at every larger shared read fuel. -/
theorem read_replay {shared : Nat} {value : Value Symbol Guard} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)} {actual : Read value before edges after}
    (ready : ReadReady shared actual) (readFuel : Nat) (enough : shared ≤ readFuel) :
    MergedFreshOrdinaryExposure.nodeEdges readFuel value before = .done edges after := ReadReady.mono ready enough

/-- Ordered row reads replay with their exact concatenation and full heaps. -/
theorem readAll_replay {shared : Nat} {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)} {actual : ReadAll values before edges after}
    (ready : ReadAllReady shared actual) (readFuel : Nat) (enough : shared ≤ readFuel) :
    readAll readFuel values before = .done edges after := by
  induction ready with
  | nil state => rfl
  | cons firstReady restReady ih => simp only [readAll, read_replay firstReady readFuel enough, ih, Result.bind]

/-- Source union replay retains the exact actual final node and heap. -/
theorem union_replay {shared : Nat} {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {result : Value Symbol Guard} {actual : Union values before result after}
    (ready : UnionReady shared actual) (readFuel : Nat) (enough : shared ≤ readFuel) :
    union readFuel values before = .done result after := by
  cases actual with
  | node read built =>
      cases ready with
      | node readReady => simp only [union, readAll_replay readReady readFuel enough, Result.bind, work, built]

/-- Recursive head replay retains the exact exposed ordinary value and heap. -/
theorem head_replay {shared : Nat} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    {actual : Head value before result after} (ready : HeadReady shared actual)
    (readFuel : Nat) (enough : shared ≤ readFuel) : head readFuel value before = .done result after := by
  cases actual with
  | read oldFuel edges middle exposed rebuilt =>
      cases ready with
      | read readReady ordinary => simp only [head, read_replay readReady readFuel enough, work, rebuilt]

end MicroCFTA.SourceCurrentProjectionNumericReplay

#check @MicroCFTA.SourceCurrentProjectionNumericReplay.ProjectReady.rec
