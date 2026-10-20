import MicroCFTA.SourceCurrentNativeOriginalPublicationTrace
import MicroCFTA.SourceCurrentPublicationBodySourceRows
import MicroCFTA.SourceCurrentSourceRowTerminalSuffix
import MicroCFTA.SourceCurrentSourceCaptureOriginalSlots

/-!
# Stored row origins in one warm source build

One completed build fixes one publication path. Each stored row reaches an
actual node call, an exact original input, or a full Mu present at entry.
New binder writers decrease their index in the same path. Bounds refer to
the chosen producer's expression, not to a later requester.
-/
namespace MicroCFTA.SourceCurrentWarmBuildRowOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request finish work)
open InternedFreshOrdinaryConstruction (build buildEdges ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedBinderProtocol (NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentNativeOriginalPublicationTrace (events)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open InternedEdgeResidency (nodeEdges)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- A full row retains one indexed producer and its actual terminal receipt. -/
def RowOrigin (original : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (before : State Symbol Guard) {after : State Symbol Guard} (path : Path before after)
    (index : Nat) (outer : @Publication Symbol Guard _) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
    producerIndex ≤ index ∧ (events path)[producerIndex]? = some producer ∧
    ∃ raw rawAfter,
      build producer.expression (.reference (.interned producer.entry.identity) :: producer.environment)
        producer.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned producer.entry.identity) raw) rawAfter = (producer.body,producer.afterBody) ∧
      Context producer.allocated (.reference (.interned producer.entry.identity) :: producer.environment) ∧
      Reached original initial producer.expression
        (.reference (.interned producer.entry.identity) :: producer.environment) producer.allocated ∧
      RowAt raw row ∧
      SourceRow producer.expression (.reference (.interned producer.entry.identity) :: producer.environment)
        producer.allocated raw rawAfter row ∧
    ∃ expression inputs start value stop,
      SourceRow expression inputs start value stop row ∧
      build expression inputs start = .done value stop ∧ Context start inputs ∧
      Reached original initial expression inputs start ∧
      sizeOf expression ≤ sizeOf producer.expression ∧
      Grows stop rawAfter ∧ Extends stop.nodes.issued rawAfter.nodes.issued ∧
      Grows rawAfter producer.afterBody ∧ Extends rawAfter.nodes.issued producer.afterBody.nodes.issued ∧
      Grows stop outer.afterBody ∧ Extends stop.nodes.issued outer.afterBody.nodes.issued ∧
      ((∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
        expression = Syntax.node expressions ∧
        buildEdges expressions inputs start = .done rows middle ∧ run (makeNode rows) middle = (value,stop) ∧
        (nodeEdges value)[outputIndex]? = some row ∧
        ∃ call : RowCall expressions inputs start rows middle stop sourceIndex symbol guard children,
          call.output = row) ∨
      (∃ slot captured crossings originalSlot,
        expression = Syntax.var slot ∧ inputs[slot]? = some captured ∧ RowAt captured row ∧
        InternedFreshOrdinaryActiveOrigins.Path original initial expression inputs crossings ∧
        slot = crossings.length + originalSlot ∧ initial[originalSlot]? = some captured) ∨
      ∃ smart body depth afterDepth ordinary cut entry storedBody,
        expression = Syntax.binder smart body ∧
        callback body inputs .depth start = .done depth afterDepth ∧
        callback body inputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
        request smart depth ordinary (callback body inputs) cut = .done value stop ∧
        stop.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
        value = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
        before.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary))

private theorem source_done {expression : Syntax Symbol Guard} {inputs : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {raw : Value Symbol Guard} {row : EdgeValue Symbol Guard}
    (source : SourceRow expression inputs before raw after row) :
    build expression inputs before = .done raw after := by
  cases source with
  | capture found _ => simp only [build,found,Option.getD_some]
  | node built made _ _ _ => simp only [build,built,Outcome.bind,work,made]
  | union built made _ _ _ _ _ _ _ => simp only [build,built,Outcome.bind,work,made]
  | @binder smart expression inputs before raw after depth afterDepth ordinary cut entry body row
      depthDone ordinaryDone requested _ _ _ =>
    simp only [build]
    change ((callback expression inputs .depth before).bind fun depth afterDepth =>
      (callback expression inputs (.uninterned (ordinaryLevel depth)) afterDepth).bind
        fun ordinary cut => request smart depth ordinary (callback expression inputs) cut) = .done raw after
    simpa only [depthDone,ordinaryDone,Outcome.bind] using requested

private theorem later {original : Syntax Symbol Guard} {initial : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {path : Path before after}
    {index nextIndex : Nat} {outer next : @Publication Symbol Guard _} {row : EdgeValue Symbol Guard}
    (origin : RowOrigin original initial before path index outer row) (bound : index ≤ nextIndex)
    (growth : Grows outer.afterBody next.afterBody)
    (issued : Extends outer.afterBody.nodes.issued next.afterBody.nodes.issued) :
    RowOrigin original initial before path nextIndex next row := by
  obtain ⟨k,producer,less,selected,raw,rawAfter,built,filtered,context,reached,rawRow,source,
    expression,inputs,start,value,stop,terminal,done,terminalContext,terminalReached,small,
    suffix,suffixIssued,filterGrowth,filterIssued,tail,tailIssued,choice⟩ := origin
  exact ⟨k,producer,Nat.le_trans less bound,selected,raw,rawAfter,built,filtered,context,reached,
    rawRow,source,expression,inputs,start,value,stop,terminal,done,terminalContext,terminalReached,small,
    suffix,suffixIssued,filterGrowth,filterIssued,grows_trans tail growth,extends_trans tailIssued issued,choice⟩

/-- One actual warm build derives indexed full-row origins without internal history premises. -/
theorem build_row_origins
    (original : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before initial)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : build original initial before = .done result after) :
    ∃ path : Path before after,
      (∀ (index : Nat) event, (events path)[index]? = some event →
        Reached original initial (.binder event.smart event.expression) event.environment event.before) ∧
      (∀ key entry body depth ordinary,
        after.nodeRecords key = some (.mu entry body depth ordinary) →
        before.nodeRecords key = some (.mu entry body depth ordinary) ∨
        ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
          Reached original initial (.binder event.smart event.expression) event.environment event.before ∧
          key = event.key ∧ Value.mu entry body depth ordinary = event.candidate ∧
          event.afterBody.nodeRecords event.key = none ∧
          Nonempty (Path before event.before) ∧
          Nonempty (Path event.before event.afterDepth) ∧
          Nonempty (Path event.afterDepth event.cut) ∧
          Nonempty (Path event.allocated event.afterBody) ∧
          Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued) ∧
      (∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∀ key entry body depth ordinary,
          outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary) →
          before.nodeRecords key = some (.mu entry body depth ordinary) ∨
          ∃ earlierIndex : Nat, ∃ earlier, earlierIndex < index ∧ (events path)[earlierIndex]? = some earlier ∧
            Reached original initial (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
            key = earlier.key ∧ Value.mu entry body depth ordinary = earlier.candidate ∧
            earlier.afterBody.nodeRecords earlier.key = none ∧
            Nonempty (Path before earlier.before) ∧
            Nonempty (Path earlier.before earlier.afterDepth) ∧
            Nonempty (Path earlier.afterDepth earlier.cut) ∧
            Nonempty (Path earlier.allocated earlier.afterBody) ∧
            Grows earlier.after outer.afterBody ∧
            Extends earlier.after.nodes.issued outer.afterBody.nodes.issued) ∧
      ∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∀ row, RowAt outer.body row → RowOrigin original initial before path index outer row := by
  obtain ⟨path,sites,writers,precompletion⟩ :=
    SourceCurrentNativeOriginalPublicationTrace.build_trace_warm_writers original initial before context result after actual
  refine ⟨path,sites,writers,precompletion,?_⟩
  intro index
  induction index using Nat.strongRecOn with
  | ind index ih =>
    intro outer selectedOuter row inside
    obtain ⟨raw,rawAfter,built,filtered,rawContext,rawReached,rawRow,source⟩ :=
      SourceCurrentPublicationBodySourceRows.publication_body_origin outer original initial
        (sites index outer selectedOuter) row inside
    obtain ⟨expression,inputs,start,value,stop,terminal,nonunion,terminalContext,terminalReached,
      small,suffix,suffixIssued⟩ :=
      SourceCurrentSourceRowTerminalSuffix.terminal_source rawContext rawReached source
    have returnedContext : Context rawAfter
        (.reference (.interned outer.entry.identity) :: outer.environment) := by
      simpa only [built,Outcome.state] using rawContext.build outer.expression
    have filterGrowth := (run_correct (withoutSelfReference (.interned outer.entry.identity) raw)
      rawAfter returnedContext.base.normal.facts.coherent.valid).2
    have filterIssued := run_issued_extends (withoutSelfReference (.interned outer.entry.identity) raw)
      rawAfter returnedContext.base.normal.facts.coherent.valid
    rw [filtered] at filterGrowth filterIssued
    have toOuter := grows_trans suffix filterGrowth
    have issuedToOuter := extends_trans suffixIssued filterIssued
    have keep (choice) : RowOrigin original initial before path index outer row :=
      ⟨index,outer,Nat.le_refl _,selectedOuter,raw,rawAfter,built,filtered,rawContext,rawReached,
        rawRow,source,expression,inputs,start,value,stop,terminal,source_done terminal,terminalContext,
        terminalReached,small,suffix,suffixIssued,filterGrowth,filterIssued,toOuter,issuedToOuter,choice⟩
    cases terminal with
    | @capture inputs state captured row slot found capturedRow =>
      obtain ⟨crossings,activePath,_⟩ := terminalReached
      obtain ⟨originalSlot,offset,originalFound⟩ :=
        SourceCurrentSourceCaptureOriginalSlots.original_slot activePath slot captured found row capturedRow
      exact keep (.inr (.inl ⟨slot,captured,crossings,originalSlot,rfl,found,capturedRow,activePath,offset,originalFound⟩))
    | @node expressions inputs start value stop rows middle symbol guard children row
        sourceIndex outputIndex rowsBuilt made canonical call callSame =>
      exact keep (.inl ⟨expressions,rows,middle,sourceIndex,outputIndex,symbol,guard,children,
        rfl,rowsBuilt,made,canonical,call,callSame⟩)
    | union => exact (nonunion _ rfl).elim
    | @binder smart body inputs start value stop depth afterDepth ordinary cut entry storedBody row
        depthDone ordinaryDone requested present returned storedRow =>
      have selected := toOuter.nodeRecords (muKey depth ordinary) _ present
      rcases precompletion index outer selectedOuter _ _ _ _ _ selected with prior | earlier
      · exact keep (.inr (.inr ⟨smart,body,depth,afterDepth,ordinary,cut,entry,storedBody,
          rfl,depthDone,ordinaryDone,requested,present,returned,storedRow,prior⟩))
      · obtain ⟨earlierIndex,earlier,less,earlierSelected,_earlierReached,_keySame,valueSame,
          _missing,_prefix,_depth,_ordinary,_body,earlierGrowth,earlierIssued⟩ := earlier
        have bodySame : storedBody = earlier.body := (Value.mu.inj valueSame).2.1
        have ancestor := ih earlierIndex less earlier earlierSelected row (bodySame ▸ storedRow)
        have completionIssued : Extends earlier.afterBody.nodes.issued earlier.after.nodes.issued := extends_refl _
        exact later ancestor (Nat.le_of_lt less)
          (grows_trans (SourceCurrentNativeMuGrowthHistory.publication_growth earlier) earlierGrowth)
          (extends_trans completionIssued earlierIssued)

end MicroCFTA.SourceCurrentWarmBuildRowOrigins
