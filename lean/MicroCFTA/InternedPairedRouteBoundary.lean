import MicroCFTA.InternedOrdinaryLevelBoundary
import MicroCFTA.InternedPairedProbeReplay

/-!
# Paired absence alone does not replay an entire source route

A crossed ordinary entry can change its computed level.
A later target reads that ordinary local and does not read the fresh input.
Both target probes omit the fresh input, but their pair changes.
-/
namespace MicroCFTA.InternedPairedRouteBoundary
open InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback
open InternedBinderProtocol (Reference)
open InternedOrdinaryLevelBoundary (innerBody captures)

/-- The target reads the crossed binder's ordinary local. -/
def target : Syntax Nat Unit := .binder false (.var 1)

/-- The target's edge is removed after its children run. -/
def discarded : Syntax Nat Unit := .node [.mk 9 () [target, .empty]]

/-- The discarded suffix preserves the earlier level-changing result. -/
def crossedBody : Syntax Nat Unit := .union [innerBody, discarded]

/-- Follow the actual prefix to the target in the crossed binder's ordinary callback. -/
def targetPair (environment : List (Value Nat Unit)) (state : State Nat Unit) :
    Option (Nat × Value Nat Unit × Value Nat Unit × State Nat Unit) :=
  match callback crossedBody environment .depth state with
  | .pending .. => none
  | .done depth afterDepth =>
      let localEnvironment := .reference (.uninterned depth.depth) :: environment
      match build innerBody localEnvironment afterDepth with
      | .pending .. => none
      | .done _ beforeTarget =>
          match callback (.var 1) localEnvironment .depth beforeTarget with
          | .pending .. => none
          | .done first afterFirst =>
              match callback (.var 1) localEnvironment (.uninterned first.depth) afterFirst with
              | .pending .. => none
              | .done second afterSecond => some (depth.depth, first, second, afterSecond)

/-- Compare this exact target prefix before and after the actual ancestor reservation. -/
def observation : Option (Nat × Nat × Bool × Bool × Bool) :=
  match callback (.binder false crossedBody) captures .depth empty with
  | .pending .. => none
  | .done depth afterDepth =>
      match callback (.binder false crossedBody) captures (.uninterned depth.depth) afterDepth with
      | .pending .. => none
      | .done ordinary cut =>
          let key := muKey depth ordinary
          match cut.nodes.table key with
          | some _ => none
          | none =>
              let entry := Cache.intern cut.nodes key
              let allocated := {cut with nodes := entry.2}
              match targetPair (.reference .depth :: captures) empty,
                  targetPair (.reference (.interned entry.1.identity) :: captures) allocated with
              | some (firstLevel, firstDepth, firstOrdinary, _),
                  some (secondLevel, secondDepth, secondOrdinary, _) =>
                  some (firstLevel, secondLevel,
                    !(secondDepth.free.contains (.interned entry.1.identity)) &&
                      !(secondOrdinary.free.contains (.interned entry.1.identity)),
                    decide (firstDepth.referenceOf ≠ secondDepth.referenceOf),
                    decide (firstOrdinary.referenceOf ≠ secondOrdinary.referenceOf))
              | _, _ => none

/-- Both target probes omit the fresh ancestor name while both reference components change. -/
theorem paired_absence_does_not_replay_route : observation = some (0, 1, true, true, true) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 100000000 in cbv

/-- The observation retains the exact ordered source calls that precede both target probes. -/
theorem targetPair_prefix (environment : List (Value Nat Unit)) (state : State Nat Unit)
    (level : Nat) (first second : Value Nat Unit) (finish : State Nat Unit)
    (observed : targetPair environment state = some (level, first, second, finish)) :
    ∃ depth afterDepth previous beforeTarget afterFirst,
      callback crossedBody environment .depth state = .done depth afterDepth ∧
      depth.depth = level ∧
      build innerBody (.reference (.uninterned level) :: environment) afterDepth = .done previous beforeTarget ∧
      callback (.var 1) (.reference (.uninterned level) :: environment) .depth beforeTarget = .done first afterFirst ∧
      callback (.var 1) (.reference (.uninterned level) :: environment) (.uninterned first.depth) afterFirst = .done second finish := by
  cases depthDone : callback crossedBody environment .depth state with
  | pending key after => simp [targetPair, depthDone] at observed
  | done depth afterDepth =>
      cases previousDone : build innerBody (.reference (.uninterned depth.depth) :: environment) afterDepth with
      | pending key after => simp [targetPair, depthDone, previousDone] at observed
      | done previous beforeTarget =>
          cases firstDone : callback (.var 1) (.reference (.uninterned depth.depth) :: environment) .depth beforeTarget with
          | pending key after => simp [targetPair, depthDone, previousDone, firstDone] at observed
          | done actual afterFirst =>
              cases secondDone : callback (.var 1) (.reference (.uninterned depth.depth) :: environment) (.uninterned actual.depth) afterFirst with
              | pending key after => simp [targetPair, depthDone, previousDone, firstDone, secondDone] at observed
              | done other final =>
                  simp only [targetPair, depthDone, previousDone, firstDone, secondDone,
                    Option.some.injEq, Prod.mk.injEq] at observed
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := observed
                  exact ⟨depth, afterDepth, previous, beforeTarget, afterFirst, rfl, rfl, previousDone, firstDone, secondDone⟩

/-- The same source body occurs in the closed wrapper of the level-change fixture. -/
def expression : Syntax Nat Unit := .binder true (.binder true
  (.node [.mk 3 () [.binder false (.binder false crossedBody), .empty]]))

/-- Execute the closed wrapper from empty caches. -/
def result := build expression [] (empty : State Nat Unit)

/-- The final cache contains the changed ancestor route and both target pair records. -/
def closedObservation : Bool × Bool × Bool :=
  let state := result.state
  let changed := (List.range state.nodes.next).any fun identity =>
    match state.nodes.issued identity with
    | none => false
    | some key =>
        match state.nodeRecords key with
        | some (.mu _ (.mu _ _ actual _) (.mu _ _ previous _) _) => actual.depth == 1 && previous.depth == 0
        | _ => false
  let recorded := (state.nodeRecords (muKey (.reference (.uninterned 0) : Value Nat Unit) (.reference (.uninterned 0)))).isSome &&
    (state.nodeRecords (muKey (.reference (.uninterned 1) : Value Nat Unit) (.reference (.uninterned 1)))).isSome
  (changed, recorded, match result with | .done .empty _ => true | _ => false)

/-- Closed source execution retains the changed levels and both complete target records. -/
theorem closed_changed_pairs : closedObservation = (true, true, true) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 100000000 in cbv

/-- All references in the closed wrapper are in lexical scope. -/
theorem expression_scoped : Scoped 0 expression := by
  simp [expression, crossedBody, discarded, target, innerBody, Scoped, EdgesScoped, ManyScoped]

end MicroCFTA.InternedPairedRouteBoundary
