import MicroCFTA.SourceCurrentFilteredSourceFusion
import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
namespace MicroCFTA.BinderHistoryKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution (Environment Replacements)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def row : Syntax Nat Bool := .node [.mk 7 false [.var 0,.var 1]]
private def author : Syntax Nat Bool := .binder true row
private def source : Syntax Nat Bool := .binder false author
private def requesterBody : Syntax Nat Bool := .union [row,.empty]
private def requester : Syntax Nat Bool := .binder true requesterBody
private def outerDepth := callback author [] .depth (empty (Symbol := Nat) (Guard := Bool))
private def outerOrdinary := callback author [] (.uninterned (ordinaryLevel (val outerDepth))) outerDepth.state
private def outerEntry := (Cache.intern outerOrdinary.state.nodes (muKey (val outerDepth) (val outerOrdinary))).1
private def outerAllocated := {outerOrdinary.state with nodes :=
  (Cache.intern outerOrdinary.state.nodes (muKey (val outerDepth) (val outerOrdinary))).2}
private def outerBody := callback author [] (.interned outerEntry.identity) outerAllocated
private def outer : Publication (Symbol := Nat) (Guard := Bool) where
  smart := false
  expression := author
  environment := []
  before := empty
  afterDepth := outerDepth.state
  cut := outerOrdinary.state
  afterBody := outerBody.state
  depth := val outerDepth
  ordinary := val outerOrdinary
  body := val outerBody
  context := SourceCurrentConstrainedCapSourceHistory.empty_context
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv
private def reader := outer.after
private def firstName : Reference := .interned outer.entry.identity
private def secondName : Reference := .uninterned (ordinaryLevel outer.depth)
private def name (second : Bool) := if second then secondName else firstName
private def before (second : Bool) := if second then outer.afterDepth else outer.allocated
private theorem historical_context (second : Bool) : Context (before second) [.reference (name second)] := by
  obtain ⟨ordinaryContext,_cutContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts outer
  cases second with
  | false =>
      exact bodyContext.local firstName
        (InternedConstructionProvenance.reserve_available outer.key outer.cut
          _cutContext.base.normal.facts.coherent _cutContext.base.normal.facts.cached).2
  | true => exact ordinaryContext.local secondName
      (InternedNestedProvenance.ordinary_available outer.afterDepth (ordinaryLevel outer.depth))
private def depthCall (second : Bool) := callback row [.reference (name second)] .depth (before second)
private def ordinaryCall (second : Bool) := callback row [.reference (name second)]
  (.uninterned (ordinaryLevel (val (depthCall second)))) (depthCall second).state
private def entry (second : Bool) := (Cache.intern (ordinaryCall second).state.nodes
  (muKey (val (depthCall second)) (val (ordinaryCall second)))).1
private def allocated (second : Bool) := {(ordinaryCall second).state with nodes :=
  (Cache.intern (ordinaryCall second).state.nodes (muKey (val (depthCall second)) (val (ordinaryCall second)))).2}
private def bodyCall (second : Bool) := callback row [.reference (name second)]
  (.interned (entry second).identity) (allocated second)
private def writer (second : Bool) : Publication (Symbol := Nat) (Guard := Bool) where
  smart := true
  expression := row
  environment := [.reference (name second)]
  before := before second
  afterDepth := (depthCall second).state
  cut := (ordinaryCall second).state
  afterBody := (bodyCall second).state
  depth := val (depthCall second)
  ordinary := val (ordinaryCall second)
  body := val (bodyCall second)
  context := historical_context second
  depthDone := by cases second <;> cbv
  ordinaryDone := by cases second <;> cbv
  missing := by cases second <;> cbv
  bodyDone := by cases second <;> cbv
private def raw (second : Bool) := (writer second).candidate
private def replacement (second : Bool) : Environment Nat Bool :=
  fun current => if current = name second then some .empty else none
private def firstRun := execute (raw false) (replacement false) reader
private def middle := firstRun.state
private def secondRun := execute (raw true) (replacement true) middle
private def final := secondRun.state

private theorem actual : build source [] empty = .done outer.candidate reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source outer.candidate reader actual
private theorem raw_available (second : Bool) : Available reader (raw second) := by
  exact ready.semantic.1.normal.facts.cached.nodes (writer second).key (raw second) (by cases second <;> cbv)
private theorem name_available (second : Bool) : Available reader (.reference (name second)) := by
  cases second with
  | false =>
      apply reference_available reader firstName
      intro identity member
      have same : identity = outer.entry.identity := by
        simpa only [firstName,Value.free,List.mem_singleton,Reference.interned.injEq] using member
      subst identity
      exact ⟨outer.key,by cbv⟩
  | true => exact InternedNestedProvenance.ordinary_available reader (ordinaryLevel outer.depth)
private theorem context (second : Bool) : Context reader [.reference (name second)] :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic _
    (by intro value member; obtain rfl := List.mem_singleton.mp member; exact name_available second),ready.semantic.2⟩
private theorem replacements (second : Bool) (heap : State Nat Bool) : Replacements heap (replacement second) := by
  intro current value present
  dsimp only [replacement] at present
  split at present
  · cases present; exact empty_available heap
  · cases present
private theorem first_done : execute (raw false) (replacement false) reader = .done .empty middle := by cbv
private theorem second_done : execute (raw true) (replacement true) middle = .done .empty final := by cbv
private theorem first_keeps : Keeps reader middle := by
  obtain ⟨result,after,done,kept,_⟩ := SourceCurrentStoredReconstruction.execute
    (raw false) (replacement false) reader ready (raw_available false) (replacements false reader)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (done.symm.trans first_done)
  exact kept
private theorem second_keeps : Keeps middle final := by
  obtain ⟨result,after,done,kept,_⟩ := SourceCurrentStoredReconstruction.execute
    (raw true) (replacement true) middle first_keeps.ready
      (first_keeps.available _ (raw_available true)) (replacements true middle)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (done.symm.trans second_done)
  exact kept
private theorem raw_warm (second : Bool) : build requester [.reference (name second)] reader = .done (raw second) reader := by
  cases second <;> cbv
private theorem final_raw (second : Bool) : build requester [.reference (name second)] final = .done (raw second) final := by
  exact InternedFreshOrdinaryReplay.build_replay requester [.reference (name second)] reader final
    (raw second) reader ready.semantic.1.normal.facts.coherent.valid (raw_warm second)
      (first_keeps.trans second_keeps).growth
private theorem final_context (second : Bool) : Context final [.reference (name second)] := by
  exact SourceCurrentGeneratedHistoricalContext.replay requester [.reference (name second)] reader reader final
    (context second) (raw second) (raw_warm second) (first_keeps.trans second_keeps) |>.1
private theorem final_done (second : Bool) : execute (raw second) (replacement second) final = .done .empty final := by
  cases second <;> cbv
private def symbolic : List (Sum (Value Nat Bool) Unit) := [.inr ()]
private def names (second : Bool) : Unit → Reference := fun _ => name second
private theorem scope : Scope requester symbolic = [.inl .depth,.inr ()] := by cbv
private theorem aliases : Aliases requester symbolic (names false) (names true) := by
  intro a am b bm
  rw [scope] at am bm
  simp only [List.mem_cons,List.mem_singleton] at am bm
  rcases am with rfl | rfl <;> rcases bm with rfl | rfl <;> simp [names,name,firstName,secondName]
private theorem self_tests : ∀ label ∈ Scope requester symbolic,
    Sum.elim id (names false) label = .depth ↔ Sum.elim id (names true) label = .depth := by
  intro label member
  rw [scope] at member
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · obtain rfl := List.mem_singleton.mp member
    simp [names,name,firstName,secondName]
private theorem paired : SourceCurrentReaderReplacementSlots.Paired
    (fun a b : Value Nat Bool => (a.referenceOf == .empty) = (b.referenceOf == .empty))
    (replacement false) (replacement true)
    [.reference (name false)] [.reference (name true)] := by
  exact .cons (by simp [SourceCurrentReaderReplacementSlots.Slot,InternedStoredSubstitution.resolve,replacement]) .nil

private theorem checked_witness :
    build source [] empty = .done outer.candidate reader ∧ Ready reader ∧
    requester ≠ author ∧ firstName ≠ secondName ∧
    (∀ second : Bool,
      (writer second).expression = row ∧ (writer second).smart = true ∧
      (writer second).before = before second ∧
      build author [.reference (name second)] (before second) = .done (raw second) (writer second).after ∧
      (writer second).body.free.contains (.interned (writer second).entry.identity) = true ∧
      reader.nodeRecords (writer second).key = some (raw second) ∧
      callback requesterBody [.reference (name second)] .depth reader = .done (writer second).depth reader ∧
      callback requesterBody [.reference (name second)] (.uninterned (ordinaryLevel (writer second).depth)) reader =
        .done (writer second).ordinary reader ∧
      build requester [.reference (name second)] reader = .done (raw second) reader ∧
      Context reader [.reference (name second)] ∧ Available reader (raw second) ∧
      Replacements reader (replacement second)) ∧
    outer.body = raw false ∧ outer.ordinary = raw true ∧
    Aliases requester symbolic (names false) (names true) ∧
    (∀ label ∈ Scope requester symbolic,
      Sum.elim id (names false) label = .depth ↔ Sum.elim id (names true) label = .depth) ∧
    SourceCurrentReaderReplacementSlots.Paired
      (fun a b : Value Nat Bool => (a.referenceOf == .empty) = (b.referenceOf == .empty))
      (replacement false) (replacement true)
      [.reference (name false)] [.reference (name true)] ∧
    execute (raw false) (replacement false) reader = .done .empty middle ∧
    execute (raw true) (replacement true) middle = .done .empty final ∧
    Keeps reader middle ∧ Keeps middle final ∧ Ready final ∧
    reader.nodes.next < middle.nodes.next ∧
    (∀ second : Bool,
      Context final [.reference (name second)] ∧ Replacements final (replacement second) ∧
      Available final (raw second) ∧
      build requester [.reference (name second)] final = .done (raw second) final ∧
      run (withoutSelfReference .depth (raw second)) final = (raw second,final) ∧
      execute (raw second) (replacement second) final = .done .empty final) := by
  refine ⟨actual,ready,by decide,by decide,?_,by cbv,by cbv,aliases,self_tests,paired,
    first_done,second_done,first_keeps,second_keeps,second_keeps.ready,by cbv,?_⟩
  · intro second
    refine ⟨rfl,rfl,rfl,?_,?_,?_,?_,?_,raw_warm second,context second,raw_available second,replacements second reader⟩
    all_goals cases second <;> cbv
  · intro second
    exact ⟨final_context second,replacements second final,(first_keeps.trans second_keeps).available _ (raw_available second),
      final_raw second,rfl,final_done second⟩

theorem earlier_used_writer_changing_capture := checked_witness
end MicroCFTA.BinderHistoryKernels
