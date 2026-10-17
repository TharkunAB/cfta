import MicroCFTA.SourceCurrentConstrainedCapGuardDepth
import MicroCFTA.InternedFreshOrdinaryDepthHeap
import MicroCFTA.InternedFreshOrdinaryReplay

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

namespace MicroCFTA.CapWriteExperiments
open Cache InternedConstructorTemplates InternedNestedConstruction
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapGuardDepth (join raise Within)
private abbrev S := Syntax Nat Bool
private abbrev V := Value Nat Bool
private abbrev Heap := State Nat Bool

/-- This executable audit checker specializes the frozen GuardDepth equations to Boolean guards. -/
private def profileFuel : Nat → V → Option Nat
  | 0, _ => none
  | _ + 1, .empty | _ + 1, .reference _ => some 0
  | fuel + 1, .node _ edges _ _ => edges.foldr (fun edge tail =>
      let children := edge.children.foldr (fun value rest => join (profileFuel fuel value) rest) (some 0)
      join (join (some (if edge.entry.key.constraint then 0 else 1)) (raise children)) tail) (some 0)
  | fuel + 1, .union _ members _ _ => members.foldr (fun value rest => join (profileFuel fuel value) rest) (some 0)
  | fuel + 1, .mu _ body _ _ => if profileFuel fuel body == some 0 then some 0 else none

private def profile (value : V) := profileFuel 128 value
private def within (depth : Nat) : Option Nat → Bool
  | none => false
  | some required => decide (required ≤ depth)

private def constant (guard : Bool) : S := .node [.mk 0 guard []]
private def unary (guard : Bool) (child : S) : S := .node [.mk 1 guard [child]]
private def atoms : List S := [.empty, .var 0, .var 1, .var 2, constant false, constant true]
private def bodies : List S :=
  atoms ++
  atoms.flatMap (fun child => [unary false child, unary true child, .union [.var 0, child],
    .union [child, .var 0], .union [.var 1, child], .binder false child, .binder true child]) ++
  atoms.flatMap (fun child => [unary false (.binder false child), unary true (.binder false child),
    unary false (.binder true child), unary true (.binder true child),
    .union [.var 0, unary false child], .union [.var 0, unary true child],
    .union [.var 0, .binder false child], .union [.var 0, .binder true child]]) ++
  [.union [.var 0, unary false (.var 1)], .union [.var 0, unary true (.var 1)],
    .node [.mk 1 false [.var 0], .mk 1 true [.empty]],
    .node [.mk 1 false [.empty], .mk 1 true [.var 0]],
    .node [.mk 1 false [.var 0, .var 1], .mk 1 true [constant true]],
    .union [.var 0, .var 1, unary false (.var 2)]]

private def fullFixtures : List S := bodies.flatMap fun body =>
  [.binder false body, .binder true body,
    .binder false (.binder false body), .binder false (.binder true body),
    .binder true (.binder false body), .binder true (.binder true body),
    .binder false (unary false (.binder false body)), .binder false (unary true (.binder true body)),
    .binder true (unary false (.binder false body)), .binder true (unary true (.binder true body)),
    .binder false (.union [.var 0, .binder false body]), .binder false (.union [.var 0, .binder true body]),
    .binder true (.union [.var 0, .binder false body]), .binder true (.union [.var 0, .binder true body]),
    .union [.binder false body, .binder true body], .union [.binder true body, .binder false body]]

private def fixtures : List S :=
  [ .binder false (constant false),
    .binder true (constant false),
    .binder false (.union [.var 0, constant false]),
    .binder true (.union [.var 0, constant false]),
    .binder false (unary false (.var 0)),
    .binder true (unary false (.var 0)),
    .binder false (unary false (constant false)),
    .binder true (unary false (constant false)),
    .binder false (.union [.var 0, unary false (.var 0)]),
    .binder true (.union [.var 0, unary false (.var 0)]),
    .binder false (.binder false (unary false (.var 1))),
    .binder false (.binder true (unary false (.var 1))),
    .binder true (.binder false (unary false (.var 1))),
    .binder true (.binder true (unary false (.var 1))),
    .binder false (.binder false (.union [.var 0, unary false (.var 1)])),
    .binder false (.binder true (.union [.var 0, unary false (.var 1)])),
    .binder true (.binder false (.union [.var 0, unary false (.var 1)])),
    .binder true (.binder true (.union [.var 0, unary false (.var 1)])),
    .binder false (.node [.mk 1 false [.empty], .mk 1 true [.var 0]]),
    .binder false (.node [.mk 1 false [.var 0], .mk 1 true [.empty]]),
    .binder false (.binder false (unary false (constant false))),
    .binder false (.binder true (unary false (constant false))),
    .binder true (.binder false (unary false (constant false))),
    .binder true (.binder true (unary false (constant false))),
    .union [.binder false (constant false), .binder true (constant false)],
    .union [.binder true (constant false), .binder false (constant false)],
    .union [.binder false (.union [.var 0, constant false]), .binder true (.union [.var 0, constant false])],
    .union [.binder true (.union [.var 0, constant false]), .binder false (.union [.var 0, constant false])],
    .binder false (.node [.mk 1 false [.var 0, .var 1], .mk 1 true [constant true]]),
    .binder false (.binder false (.binder false (unary false (.var 2)))),
    .binder false (.binder true (.binder false (.union [.var 0, unary false (.var 2)]))),
    .binder true (.binder false (.binder true (.union [.var 0, unary false (.var 2)]))) ]

private def completeFuel : Nat → V → Bool
  | 0, _ => false
  | _ + 1, .empty | _ + 1, .reference _ => true
  | fuel + 1, .node _ edges _ _ => edges.all fun edge => edge.children.all (completeFuel fuel)
  | fuel + 1, .union _ members _ _ => members.all (completeFuel fuel)
  | fuel + 1, .mu _ body _ _ => completeFuel fuel body

private structure CellObservation where
  fixture : Nat
  phase : Nat
  identity : Nat
  bodyProfile : Option Nat
  depthProfile : Option Nat
  ordinaryProfile : Option Nat
  unused : Bool
  complete : Bool
  failedDepths : List Nat
  deriving Repr

private def cells (fixture phase : Nat) (heap : Heap) : List CellObservation :=
  (List.range heap.nodes.next).filterMap fun identity =>
    match heap.nodes.issued identity with
    | none => none
    | some key => match heap.nodeRecords key with
      | some (.mu _ body depth ordinary) =>
          let bodyProfile := profile body
          let depthProfile := profile depth
          let ordinaryProfile := profile ordinary
          let unused := !InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary
          let failures := (List.range 9).filter fun bound =>
            within bound depthProfile && within bound ordinaryProfile && unused && !within bound bodyProfile
          some ⟨fixture, phase, identity, bodyProfile, depthProfile, ordinaryProfile, unused,
            completeFuel 128 body && completeFuel 128 depth && completeFuel 128 ordinary, failures⟩
      | _ => none

private def runFixture (index : Nat) (expression : S) : (Bool × Bool) × List CellObservation :=
  let first := InternedFreshOrdinaryConstruction.build expression [] (empty : Heap)
  let second := InternedFreshOrdinaryConstruction.build expression [] first.state
  let firstDone := match first with | .done .. => true | .pending .. => false
  let secondDone := match second with | .done .. => true | .pending .. => false
  ((firstDone, secondDone), cells index 0 first.state ++ cells index 1 second.state)

/-- All observations come from literal closed source runs and their immediate warm repeats. -/
def observations (_ : Unit) := fixtures.zipIdx.map fun (expression, index) => runFixture index expression

private def reportData (data : List ((Bool × Bool) × List CellObservation)) :=
  let all := data.flatMap Prod.snd
  let summary := (data.length,
    data.countP (fun value => value.1.1), data.countP (fun value => value.1.2),
    all.length,
    all.countP (fun cell => cell.unused),
    all.countP (fun cell => cell.unused && cell.bodyProfile != some 0 && cell.bodyProfile.isSome &&
      within 8 cell.depthProfile && within 8 cell.ordinaryProfile),
    all.countP (fun cell => !cell.failedDepths.isEmpty),
    all.countP (fun cell => cell.bodyProfile != cell.ordinaryProfile),
    all.countP (fun cell => cell.bodyProfile != cell.depthProfile),
    all.countP (fun cell => !cell.complete))
  (summary, all.filter (fun cell => !cell.failedDepths.isEmpty) |>.take 8,
    all.filter (fun cell => cell.bodyProfile != cell.ordinaryProfile) |>.take 8,
    all.filter (fun cell => cell.bodyProfile != cell.depthProfile) |>.take 8)

/-- The finite experiment report checks both probe equalities and the original implication at actual stored cells. -/
def experimentReport (_ : Unit) := reportData (observations ())

#print axioms observations
#check @observations
#print axioms experimentReport
#check @experimentReport
private def runExperiments : IO Unit := do
  let first := ((← IO.getEnv "MCFTA_CAP_FIRST").bind String.toNat?).getD 0
  let stop := ((← IO.getEnv "MCFTA_CAP_STOP").bind String.toNat?).getD fixtures.length
  let mut collected := []
  for (expression, index) in fixtures.zipIdx do
    if first ≤ index && index < stop then
      let result := runFixture index expression
      collected := result :: collected
      IO.println (reprStr (index, reportData [result]))
      (← IO.getStdout).flush
  IO.println (reprStr ("TOTAL", reportData collected.reverse))
  (← IO.getStdout).flush
#eval runExperiments
end MicroCFTA.CapWriteExperiments
