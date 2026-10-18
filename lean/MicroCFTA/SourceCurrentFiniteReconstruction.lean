import MicroCFTA.SourceCurrentReaderFiniteUnionStep
import MicroCFTA.InternedStoredShallowCompletion

/-!
# Actual finite reconstruction with one fixed observation reader

Initial ready inputs construct both raw source calls and both stored
reconstructions. The observation reader does not change during execution.
The source case is required at the actual final execution heap.
Source syntax without active binders derives this case by strict induction.
Captured values and replacements can contain arbitrary recursive values.
General active source binders still need their own induction clause.
-/
namespace MicroCFTA.SourceCurrentFiniteReconstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt)
open SourceCurrentReaderReplacementSlots (Paired)
open SourceCurrentFiniteObservationExecution (AlignedAt)
open InternedStoredShallowCompletion (BinderFree ManyBinderFree EdgesBinderFree)
open Language

private theorem many_free (expressions : List (Syntax Symbol Guard)) (free : ManyBinderFree expressions)
    (child : Syntax Symbol Guard) (member : child ∈ expressions) : BinderFree child := by
  induction expressions with
  | nil => cases member
  | cons expression rest ih =>
      simp only [ManyBinderFree] at free
      rcases List.mem_cons.mp member with rfl | later
      · exact free.1
      · exact ih free.2 later

private theorem edge_free (expressions : List (EdgeSyntax Symbol Guard)) (free : EdgesBinderFree expressions)
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (member : EdgeSyntax.mk symbol guard children ∈ expressions) : ManyBinderFree children := by
  induction expressions with
  | nil => cases member
  | cons expression rest ih =>
      cases expression with
      | mk ownSymbol ownGuard originals =>
          simp only [EdgesBinderFree] at free
          rcases List.mem_cons.mp member with same | later
          · cases same
            exact free.1
          · exact ih free.2 later

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial Ready data constructs both stored calls from actual earlier raw calls and an established source case. -/
theorem complete (expression : Syntax Symbol Guard) (depth : Nat) (view : State Symbol Guard)
    (aligned : ∀ common, AlignedAt depth view common expression)
    (leftInputs rightInputs : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (paired : Paired (RelatedAt depth view) first second leftInputs rightInputs)
    (before after later final common : State Symbol Guard)
    (firstContext : Context before leftInputs)
    (secondContext : Context later rightInputs)
    (rawFirst rawSecond : Value Symbol Guard)
    (firstRaw : build expression leftInputs before = .done rawFirst after)
    (secondRaw : build expression rightInputs later = .done rawSecond final)
    (firstGrowth : Grows after common) (secondGrowth : Grows final common)
    (ready : Ready common)
    (firstInputs : Values common leftInputs)
    (secondInputs : Values common rightInputs)
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second) :
    ∃ left middle right reader,
      execute rawFirst first common = .done left middle ∧ execute rawSecond second middle = .done right reader ∧
      execute rawFirst first reader = .done left reader ∧ execute rawSecond second reader = .done right reader ∧
      Keeps common middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ RelatedAt depth view left right := by
  have firstWarm := InternedFreshOrdinaryReplay.build_replay expression _ before common rawFirst after
    firstContext.normal.facts.coherent.valid firstRaw firstGrowth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay expression _ later common rawSecond final
    secondContext.normal.facts.coherent.valid secondRaw secondGrowth
  have firstAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ common
    ready.semantic.1.normal.facts firstInputs).result rawFirst common firstWarm
  have secondAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ common
    ready.semantic.1.normal.facts secondInputs).result rawSecond common secondWarm
  obtain ⟨left,middle,firstDone,firstKept,leftAvailable,firstHistory⟩ :=
    SourceCurrentStoredReconstruction.execute rawFirst first common ready firstAvailable firstReplacements
  obtain ⟨right,reader,secondDone,secondKept,rightAvailable,secondHistory⟩ :=
    SourceCurrentStoredReconstruction.execute rawSecond second middle firstKept.ready
      (firstKept.available rawSecond secondAvailable)
      (fun name value found => firstKept.available value (secondReplacements name value found))
  have firstReplay := InternedFreshOrdinaryReplay.build_replay (encode (leaves rawFirst) [] rawFirst)
    ((leaves rawFirst).map (input first)) common reader left middle ready.semantic.1.normal.facts.coherent.valid
    firstDone secondKept.growth
  have secondReplay := InternedFreshOrdinaryReplay.build_replay (encode (leaves rawSecond) [] rawSecond)
    ((leaves rawSecond).map (input second)) middle reader right reader firstKept.ready.semantic.1.normal.facts.coherent.valid
    secondDone (grows_refl _)
  have growth := grows_trans firstKept.growth secondKept.growth
  have firstSource := InternedFreshOrdinaryReplay.build_replay expression _ before reader rawFirst after
    firstContext.normal.facts.coherent.valid firstRaw (grows_trans firstGrowth growth)
  have secondSource := InternedFreshOrdinaryReplay.build_replay expression _ later reader rawSecond final
    secondContext.normal.facts.coherent.valid secondRaw (grows_trans secondGrowth growth)
  have compared := aligned reader leftInputs rightInputs first second paired secondKept.ready
    (fun value member => secondKept.available value (firstKept.available value (firstInputs value member)))
    (fun value member => secondKept.available value (firstKept.available value (secondInputs value member)))
    (fun name value found => secondKept.available value (firstKept.available value (firstReplacements name value found)))
    (fun name value found => secondKept.available value (firstKept.available value (secondReplacements name value found)))
    rawFirst rawSecond firstSource secondSource left right firstReplay secondReplay
  exact ⟨left,middle,right,reader,firstDone,secondDone,firstReplay,secondReplay,firstKept,secondKept,
    secondKept.available left leftAvailable,rightAvailable,firstHistory,secondHistory,compared⟩

/-- Strict source induction gives fixed-reader agreement without active source binders. -/
theorem binder_free (expression : Syntax Symbol Guard) (free : BinderFree expression)
    (depth : Nat) (view common : State Symbol Guard) : AlignedAt depth view common expression := by
  cases shape : expression with
  | empty => exact SourceCurrentFiniteObservationExecution.closed_source .empty (by cbv) depth view common
  | var index => exact SourceCurrentFiniteObservationExecution.reference depth view common index
  | binder smart body => simp only [shape,BinderFree] at free
  | node rows =>
      simp only [shape,BinderFree] at free
      intro leftInputs rightInputs first second paired ready firstInputs secondInputs firstReplacements
        secondReplacements rawFirst rawSecond firstRaw secondRaw result other firstDone secondDone
      have related := SourceCurrentFiniteObservationExecution.ordinary rows depth view common
        (fun rowIndex symbol guard children found childIndex child childFound smaller =>
          binder_free child
            (many_free children (edge_free rows free symbol guard children (List.mem_of_getElem? found))
              child (List.mem_of_getElem? childFound)) depth view common)
        leftInputs rightInputs first second paired ready firstInputs secondInputs firstReplacements secondReplacements
        rawFirst rawSecond firstRaw secondRaw result other firstDone secondDone
      exact ⟨related.1,related.2.lower⟩
  | union expressions =>
      simp only [shape,BinderFree] at free
      apply SourceCurrentReaderFiniteUnionStep.union expressions depth view
      intro index child found smaller current
      exact binder_free child (many_free expressions free child (List.mem_of_getElem? found)) depth view current
termination_by sizeOf expression
decreasing_by all_goals simpa only [shape] using smaller

private theorem source_keeps (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (before after : State Symbol Guard) (ready : Ready before) (available : Values before inputs)
    (value : Value Symbol Guard) (actual : build expression inputs before = .done value after) : Keeps before after := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic inputs available
  have checked := InternedFreshOrdinaryFacts.build_verified expression inputs before ready.semantic.1.normal.facts available
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source expression inputs before ready.semantic available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs before
      ready.semantic.1.normal.facts.coherent.valid ready.covered value after actual
  · simpa only [actual,Outcome.state] using
      (InternedOpenDepthExecution.build_depth expression inputs before context ready.semantic.2 ready.depth).heap
  · simpa only [actual,Outcome.state] using checked.growth
  · simpa only [actual,Outcome.state] using checked.history

/-- Initial paired inputs construct both raw and stored executions for an established finite source case. -/
theorem initial (expression : Syntax Symbol Guard) (depth : Nat) (view : State Symbol Guard)
    (aligned : ∀ common, AlignedAt depth view common expression)
    (leftInputs rightInputs : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (paired : Paired (RelatedAt depth view) first second leftInputs rightInputs)
    (before : State Symbol Guard) (ready : Ready before)
    (firstInputs : Values before leftInputs) (secondInputs : Values before rightInputs)
    (firstReplacements : Replacements before first) (secondReplacements : Replacements before second) :
    ∃ rawFirst after rawSecond common left middle right reader,
      build expression leftInputs before = .done rawFirst after ∧
      build expression rightInputs after = .done rawSecond common ∧
      execute rawFirst first common = .done left middle ∧ execute rawSecond second middle = .done right reader ∧
      execute rawFirst first reader = .done left reader ∧ execute rawSecond second reader = .done right reader ∧
      Keeps before after ∧ Keeps after common ∧ Keeps common middle ∧ Keeps middle reader ∧
      Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ RelatedAt depth view left right := by
  obtain ⟨rawFirst,after,firstRaw⟩ := InternedRecordDepthCompletion.source_complete expression leftInputs before
    (SourceRecursiveIntersectionSemanticHeap.context before ready.semantic leftInputs firstInputs)
    ready.semantic.2 ready.covered
  have firstKept := source_keeps expression leftInputs before after ready firstInputs rawFirst firstRaw
  have rightAvailable : Values after rightInputs := fun value member => firstKept.available value (secondInputs value member)
  obtain ⟨rawSecond,common,secondRaw⟩ := InternedRecordDepthCompletion.source_complete expression rightInputs after
    (SourceRecursiveIntersectionSemanticHeap.context after firstKept.ready.semantic rightInputs rightAvailable)
    firstKept.ready.semantic.2 firstKept.ready.covered
  have secondKept := source_keeps expression rightInputs after common firstKept.ready rightAvailable rawSecond secondRaw
  have kept := firstKept.trans secondKept
  obtain ⟨left,middle,right,reader,firstDone,secondDone,firstWarm,secondWarm,firstStored,secondStored,
    leftAvailable,rightOutput,firstHistory,secondHistory,related⟩ := complete expression depth view aligned
      leftInputs rightInputs first second paired before after after common common
      (SourceRecursiveIntersectionSemanticHeap.context before ready.semantic leftInputs firstInputs)
      (SourceRecursiveIntersectionSemanticHeap.context after firstKept.ready.semantic rightInputs rightAvailable)
      rawFirst rawSecond firstRaw secondRaw secondKept.growth (grows_refl _) secondKept.ready
      (fun value member => kept.available value (firstInputs value member))
      (fun value member => kept.available value (secondInputs value member))
      (fun name value found => kept.available value (firstReplacements name value found))
      (fun name value found => kept.available value (secondReplacements name value found))
  exact ⟨rawFirst,after,rawSecond,common,left,middle,right,reader,firstRaw,secondRaw,firstDone,secondDone,
    firstWarm,secondWarm,firstKept,secondKept,firstStored,secondStored,leftAvailable,rightOutput,
    firstHistory,secondHistory,related⟩

end MicroCFTA.SourceCurrentFiniteReconstruction
