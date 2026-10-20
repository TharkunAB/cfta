import MicroCFTA.SourceCurrentNativeOriginalObservedResume

/-!
# Correlated source-union descent for original observed rows

The same source row supplies its terminal call and union-only descent.
The enclosing publication and callback stay fixed across all rows.
Each terminal retains its node call or selected binder writer.
-/
namespace MicroCFTA.SourceCurrentNativeOriginalUnionDescent
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work request finish)
open InternedFreshOrdinaryConstruction (build buildEdges ordinaryLevel)
open InternedFreshOrdinaryFacts (callback buildMany_verified)
open InternedBinderProtocol (NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentLiteralRootParts (Row)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open InternedEdgeResidency (nodeEdges)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeCapturedMuUnfoldRows (Observed)
open SourceCurrentNativeOriginalObservedResume (SyntaxBound)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceCurrentNativeCapturedMuStoredRows (Stored)

/-- A terminal follows only exact indexed members of original source unions. -/
inductive UnionDescent {Symbol Guard : Type} : Syntax Symbol Guard → Syntax Symbol Guard → Prop where
  /-- The selected terminal is the current source expression. -/
  | refl (expression : Syntax Symbol Guard) : UnionDescent expression expression
  /-- The same indexed source member retains its terminal descent. -/
  | member {members : List (Syntax Symbol Guard)} {expression terminal : Syntax Symbol Guard} {index : Nat}
      (selected : members[index]? = some expression) (nested : UnionDescent expression terminal) :
      UnionDescent (Syntax.union members) terminal

variable {Symbol Guard : Type}

private theorem terminal_suffix [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard} {initial inputs : List (Value Symbol Guard)}
    {before : State Symbol Guard} {raw : Value Symbol Guard} {after : State Symbol Guard}
    {fullRow : EdgeValue Symbol Guard}
    (context : Context before inputs)
    (reached : Reached root initial expression inputs before)
    (source : SourceRow expression inputs before raw after fullRow) :
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter fullRow ∧
      UnionDescent expression terminalExpression ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached root initial terminalExpression terminalInputs terminalBefore ∧
      sizeOf terminalExpression ≤ sizeOf expression ∧
      Grows terminalAfter after ∧ Extends terminalAfter.nodes.issued after.nodes.issued := by
  have descend {currentExpression : Syntax Symbol Guard} {currentInputs : List (Value Symbol Guard)}
      {start : State Symbol Guard} {value : Value Symbol Guard} {stop : State Symbol Guard}
      {row : EdgeValue Symbol Guard}
      (part : SourceRow currentExpression currentInputs start value stop row) :
      Context start currentInputs → Reached root initial currentExpression currentInputs start →
      ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
        SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
        UnionDescent currentExpression terminalExpression ∧
        (∀ members, terminalExpression ≠ Syntax.union members) ∧
        Context terminalBefore terminalInputs ∧
        Reached root initial terminalExpression terminalInputs terminalBefore ∧
        sizeOf terminalExpression ≤ sizeOf currentExpression ∧
        Grows terminalAfter stop ∧ Extends terminalAfter.nodes.issued stop.nodes.issued := by
    induction part with
    | @capture currentInputs state value row slot found inside =>
      intro currentContext currentReached
      refine ⟨.var slot,currentInputs,state,value,state,.capture found inside,.refl _,?_,
        currentContext,currentReached,Nat.le_refl _,grows_refl _,extends_refl _⟩
      intro members impossible
      cases impossible
    | @node expressions currentInputs start value stop rows middle symbol guard children row
        sourceIndex outputIndex built made canonical call same =>
      intro currentContext currentReached
      refine ⟨.node expressions,currentInputs,start,value,stop,.node built made canonical call same,.refl _,?_,
        currentContext,currentReached,Nat.le_refl _,grows_refl _,extends_refl _⟩
      intro members impossible
      cases impossible
    | @union expressions currentInputs start value stop values middle member memberValue current next row
        index built made syntaxSelected valueSelected earlier memberContext called suffix nested ih =>
      intro currentContext currentReached
      have earlierFacts := buildMany_verified (expressions.take index) currentInputs start
        currentContext.base.normal.facts currentContext.base.inputs
      have earlierGrowth : Grows start current := by
        simpa only [earlier,Outcome.state] using earlierFacts.growth
      have memberReached : Reached root initial member currentInputs current :=
        (currentReached.union (List.mem_of_getElem? syntaxSelected)).grows earlierGrowth
      obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
        terminalSource,terminalDescent,nonunion,terminalContext,terminalReached,terminalBound,terminalGrowth,terminalIssued⟩ :=
        ih memberContext memberReached
      have returnContext : Context next currentInputs := by
        simpa only [called,Outcome.state] using memberContext.build member
      have suffixFacts := buildMany_verified (expressions.drop (index + 1)) currentInputs next
        returnContext.base.normal.facts returnContext.base.inputs
      have suffixGrowth : Grows next middle := by
        simpa only [suffix,Outcome.state] using suffixFacts.growth
      have suffixIssued : Extends next.nodes.issued middle.nodes.issued := by
        simpa only [suffix,Outcome.state] using suffixFacts.history
      have middleValid : Valid middle := by
        simpa only [suffix,Outcome.state] using suffixFacts.facts.coherent.valid
      have unionGrowth : Grows middle stop := by
        simpa only [made] using (InternedConstructorTemplates.run_correct (makeUnion values) middle middleValid).2
      have unionIssued : Extends middle.nodes.issued stop.nodes.issued := by
        simpa only [made] using InternedProbeProvenance.run_issued_extends (makeUnion values) middle middleValid
      have memberBound : sizeOf member ≤ sizeOf (Syntax.union expressions) := by
        have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? syntaxSelected)
        simp only [Syntax.union.sizeOf_spec]
        omega
      exact ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
        terminalSource,.member syntaxSelected terminalDescent,nonunion,terminalContext,terminalReached,Nat.le_trans terminalBound memberBound,
        grows_trans terminalGrowth (grows_trans suffixGrowth unionGrowth),
        extends_trans terminalIssued (extends_trans suffixIssued unionIssued)⟩
    | @binder smart body currentInputs start value stop depth afterDepth ordinary cut entry stored row
        depthDone ordinaryDone requested present returned inside =>
      intro currentContext currentReached
      refine ⟨.binder smart body,currentInputs,start,value,stop,
        .binder depthDone ordinaryDone requested present returned inside,.refl _,?_,currentContext,currentReached,
        Nat.le_refl _,grows_refl _,extends_refl _⟩
      intro members impossible
      cases impossible
  exact descend source context reached


private theorem source_done [DecidableEq (EdgeKey Symbol Guard)]
    {expression : Syntax Symbol Guard} {inputs : List (Value Symbol Guard)}
    {before : State Symbol Guard} {raw : Value Symbol Guard} {after : State Symbol Guard}
    {row : EdgeValue Symbol Guard} (source : SourceRow expression inputs before raw after row) :
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

private theorem terminal_original [DecidableEq (EdgeKey Symbol Guard)]
    {original expression : Syntax Symbol Guard} {inputs : List (Value Symbol Guard)}
    {before : State Symbol Guard} {raw : Value Symbol Guard} {after : State Symbol Guard}
    {fullRow : EdgeValue Symbol Guard}
    (context : Context before inputs)
    (reached : Reached original [] expression inputs before)
    (source : SourceRow expression inputs before raw after fullRow) :
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter fullRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ rows, terminalExpression = Syntax.node rows) ∨
        ∃ smart body, terminalExpression = Syntax.binder smart body) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression expression ∧
      UnionDescent expression terminalExpression ∧
      Grows terminalAfter after ∧ Extends terminalAfter.nodes.issued after.nodes.issued := by
  obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,descent,nonunion,terminalContext,terminalReached,bound,growth,issued⟩ :=
    terminal_suffix context reached source
  have kind : (∃ rows, terminalExpression = Syntax.node rows) ∨
      ∃ smart body, terminalExpression = Syntax.binder smart body := by
    cases terminalSource with
    | capture found inside =>
      obtain ⟨crossings,path,_⟩ := terminalReached
      exact (SourceCurrentSourceCaptureOriginalSlots.empty_initial path _ _ found fullRow inside).elim
    | node => exact .inl ⟨_,rfl⟩
    | union => exact (nonunion _ rfl).elim
    | binder => exact .inr ⟨_,_,rfl⟩
  exact ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,source_done terminalSource,kind,nonunion,terminalContext,terminalReached,bound,descent,growth,issued⟩


local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem terminal_resume (original : Syntax Symbol Guard) (sourceRoot : Node) (sourceHeap : Heap)
    (sourceBuilt : build original [] empty = .done sourceRoot sourceHeap)
    (event : @Publication Symbol Guard _) (raw : Node) (rawAfter : Heap)
    (context : Context event.allocated (.reference (.interned event.entry.identity) :: event.environment))
    (built : build event.expression (.reference (.interned event.entry.identity) :: event.environment)
      event.allocated = .done raw rawAfter)
    (filtered : run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody))
    (growth : Grows event.after sourceHeap)
    (issued : Extends event.after.nodes.issued sourceHeap.nodes.issued)
    (callbackReached : Reached original [] event.expression
      (.reference (.interned event.entry.identity) :: event.environment) event.allocated)
    (row : EdgeValue Symbol Guard)
    (source : SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
      event.allocated raw rawAfter row) :
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      UnionDescent event.expression terminalExpression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          terminalExpression = Syntax.node expressions ∧
          buildEdges expressions terminalInputs terminalBefore = .done rows middle ∧
          run (makeNode rows) middle = (terminalRaw,terminalAfter) ∧
          (nodeEdges terminalRaw)[outputIndex]? = some row ∧
          ∃ call : RowCall expressions terminalInputs terminalBefore rows middle terminalAfter sourceIndex symbol guard children,
            call.output = row) ∨
        (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
          ∃ depth afterDepth ordinary cut entry storedBody,
            callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
            callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
            request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
            terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            sourceHeap.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
            Grows terminalAfter sourceHeap ∧ Extends terminalAfter.nodes.issued sourceHeap.nodes.issued ∧
            Written original [] empty sourceHeap (muKey depth ordinary) (.mu entry storedBody depth ordinary) ∧
            Stored original [] empty sourceHeap (muKey depth ordinary) entry storedBody depth ordinary)) := by
  obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,done,kind,nonunion,terminalContext,terminalReached,bound,descent,suffix,suffixIssued⟩ :=
    terminal_original context callbackReached source
  refine ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,done,kind,nonunion,terminalContext,terminalReached,bound,descent,suffix,suffixIssued,?_⟩
  rcases kind with ⟨expressions,rfl⟩ | ⟨smart,terminalBody,rfl⟩
  · cases terminalSource with
    | @node expressions inputs before raw after rows middle symbol guard children row sourceIndex outputIndex
        builtRows made selected call same =>
      exact .inl ⟨_,_,_,_,_,_,_,_,rfl,builtRows,made,selected,call,same⟩
  · exact .inr ⟨smart,terminalBody,rfl,
      SourceCurrentNativeOriginalBinderResume.resume original sourceRoot sourceHeap sourceBuilt
        event raw rawAfter context built filtered growth issued smart terminalBody terminalInputs
        terminalBefore terminalRaw terminalAfter row terminalSource suffix suffixIssued⟩

/-- One observed original writer retains actual node calls or selected binder writers for every source row. -/
theorem of_observed (original : Syntax Symbol Guard) (sourceRoot : Node) (sourceHeap : Heap)
    (sourceBuilt : build original [] empty = .done sourceRoot sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node) (current : Heap)
    (observed : Observed original [] empty sourceHeap key entry body depth ordinary current) :
    ∃ event : @Publication Symbol Guard _,
      Reached original [] (.binder event.smart event.expression) event.environment event.before ∧
      key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path empty event.before) ∧
      Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧
      Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after sourceHeap ∧ Extends event.after.nodes.issued sourceHeap.nodes.issued ∧
      ∃ raw rawAfter,
        build event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated = .done raw rawAfter ∧
        run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
        Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
        Reached original [] event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated ∧
        (∀ row, RowAt body row → RowAt raw row ∧
          SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated raw rawAfter row ∧
          ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      UnionDescent event.expression terminalExpression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          terminalExpression = Syntax.node expressions ∧
          buildEdges expressions terminalInputs terminalBefore = .done rows middle ∧
          run (makeNode rows) middle = (terminalRaw,terminalAfter) ∧
          (nodeEdges terminalRaw)[outputIndex]? = some row ∧
          ∃ call : RowCall expressions terminalInputs terminalBefore rows middle terminalAfter sourceIndex symbol guard children,
            call.output = row) ∨
        (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
          ∃ depth afterDepth ordinary cut entry storedBody,
            callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
            callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
            request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
            terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            sourceHeap.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
            Grows terminalAfter sourceHeap ∧ Extends terminalAfter.nodes.issued sourceHeap.nodes.issued ∧
            Written original [] empty sourceHeap (muKey depth ordinary) (.mu entry storedBody depth ordinary) ∧
            Stored original [] empty sourceHeap (muKey depth ordinary) entry storedBody depth ordinary))) ∧
        ∀ value after,
          InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) current = .done value after →
          SemanticHeap after ∧ Grows current after ∧ Extends current.nodes.issued after.nodes.issued ∧
            Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
            ∀ row, Row value row →
          ∃ originalRow, RowAt body originalRow ∧ row.entry.key.symbol = originalRow.entry.key.symbol ∧
            row.entry.key.constraint = originalRow.entry.key.constraint ∧ row.children.length = originalRow.children.length ∧
            (row = originalRow ∨ ∃ lexical current next, Calls lexical originalRow.children current row.children next) ∧
            RowAt raw originalRow ∧
            SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
              event.allocated raw rawAfter originalRow ∧
            ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter originalRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      UnionDescent event.expression terminalExpression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          terminalExpression = Syntax.node expressions ∧
          buildEdges expressions terminalInputs terminalBefore = .done rows middle ∧
          run (makeNode rows) middle = (terminalRaw,terminalAfter) ∧
          (nodeEdges terminalRaw)[outputIndex]? = some originalRow ∧
          ∃ call : RowCall expressions terminalInputs terminalBefore rows middle terminalAfter sourceIndex symbol guard children,
            call.output = originalRow) ∨
        (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
          ∃ depth afterDepth ordinary cut entry storedBody,
            callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
            callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
            request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
            terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            sourceHeap.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody originalRow ∧
            Grows terminalAfter sourceHeap ∧ Extends terminalAfter.nodes.issued sourceHeap.nodes.issued ∧
            Written original [] empty sourceHeap (muKey depth ordinary) (.mu entry storedBody depth ordinary) ∧
            Stored original [] empty sourceHeap (muKey depth ordinary) entry storedBody depth ordinary)) := by
  obtain ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    earlier,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,built,filtered,context,
    callbackReached,rows,unfolds⟩ := observed
  refine ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    earlier,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,built,filtered,context,
    callbackReached,?_,?_⟩
  · intro row inside
    obtain ⟨rawRow,source⟩ := rows row inside
    exact ⟨rawRow,source,terminal_resume original sourceRoot sourceHeap sourceBuilt
      event raw rawAfter context built filtered growth issued callbackReached row source⟩
  · intro value after actual
    obtain ⟨semanticAfter,nextGrowth,nextIssued,available,published,anchors⟩ := unfolds value after actual
    refine ⟨semanticAfter,nextGrowth,nextIssued,available,published,?_⟩
    intro row literal
    obtain ⟨originalRow,inside,symbol,guard,arity,calls,rawRow,source⟩ := anchors row literal
    exact ⟨originalRow,inside,symbol,guard,arity,calls,rawRow,source,
      terminal_resume original sourceRoot sourceHeap sourceBuilt
        event raw rawAfter context built filtered growth issued callbackReached originalRow source⟩

end MicroCFTA.SourceCurrentNativeOriginalUnionDescent
