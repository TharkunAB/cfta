import MicroCFTA.SourceCurrentStoredCallbackChildContexts
import MicroCFTA.SourceCurrentNativeBinderExecution
import MicroCFTA.SourceCurrentNativeRequestProbes
import MicroCFTA.SourceCurrentStoredMuRetainedAlignment
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Structural rows from completed source builds

Actual union calls retain their original member indices. An ordinary row
retains its source edge and ordered child build. A lexical variable retains
its exact slot. A binder retains the selected stored payload, including a
warm winner whose source can differ from the current callback. These
alternatives do not assert an original binding or a global decrease.
-/
namespace MicroCFTA.SourceCurrentBuildStructuralRowOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges ordinaryLevel)
open InternedFreshOrdinaryFacts (callback buildEdges_verified buildMany_verified)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (NodeKey Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open InternedEdgeResidency (nodeEdges)

/-- A selected row retains actual source calls or an exact capture or stored winner. -/
inductive SourceRow [DecidableEq (EdgeKey Symbol Guard)] :
    Syntax Symbol Guard → List (Value Symbol Guard) → State Symbol Guard →
      Value Symbol Guard → State Symbol Guard → EdgeValue Symbol Guard → Prop where
  /-- A lexical variable returns the value at its actual input slot. -/
  | capture {inputs state slot value row}
      (selected : inputs[slot]? = some value) (inside : RowAt value row) :
      SourceRow (.var slot) inputs state value state row
  /-- A canonical survivor retains its distinct source index and ordered row call. -/
  | node {expressions inputs before raw after rows middle sourceIndex outputIndex symbol guard children row}
      (built : buildEdges expressions inputs before = .done rows middle)
      (made : run (makeNode rows) middle = (raw,after))
      (selected : (nodeEdges raw)[outputIndex]? = some row)
      (call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children)
      (same : call.output = row) :
      SourceRow (.node expressions) inputs before raw after row
  /-- An original indexed member retains its actual prefix, call and suffix. -/
  | union {expressions inputs before raw after values middle index expression value current next row}
      (built : buildMany expressions inputs before = .done values middle)
      (made : run (makeUnion values) middle = (raw,after))
      (source : expressions[index]? = some expression)
      (selected : values[index]? = some value)
      (prefix : buildMany (expressions.take index) inputs before = .done (values.take index) current)
      (context : Context current inputs)
      (called : build expression inputs current = .done value next)
      (suffix : buildMany (expressions.drop (index + 1)) inputs next = .done (values.drop (index + 1)) middle)
      (nested : SourceRow expression inputs current value next row) :
      SourceRow (.union expressions) inputs before raw after row
  /-- A binder row belongs to the selected stored body, also after smart cleanup. -/
  | binder {smart expression inputs before raw after depth afterDepth ordinary cut entry body row}
      (depthDone : callback expression inputs .depth before = .done depth afterDepth)
      (ordinaryDone : callback expression inputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut)
      (requested : request smart depth ordinary (callback expression inputs) cut = .done raw after)
      (selected : after.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary))
      (returned : raw = finish smart (.mu entry body depth ordinary))
      (inside : RowAt body row) :
      SourceRow (.binder smart expression) inputs before raw after row

private theorem literal_row {value : Value Symbol Guard} {row : EdgeValue Symbol Guard}
    (part : Row value row) : RowAt value row := by
  induction part with
  | node member =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .node (index := index) found
  | union member _ ih =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .union (index := index) found ih

private theorem atom_row {value atom : Value Symbol Guard} {row : EdgeValue Symbol Guard}
    (part : Literal value atom) (inside : RowAt atom row) : RowAt value row := by
  induction part with
  | reference | mu => exact inside
  | union member _ ih =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .union (index := index) found (ih inside)

private theorem row_parts {value : Value Symbol Guard} {row : EdgeValue Symbol Guard}
    (part : RowAt value row) : Row value row ∨
      ∃ entry body depth ordinary, Literal value (.mu entry body depth ordinary) ∧ RowAt body row := by
  induction part with
  | node found => exact .inl (.node (List.mem_of_getElem? found))
  | union found _ ih =>
      rcases ih with literal | ⟨entry,body,depth,ordinary,atom,inside⟩
      · exact .inl (.union (List.mem_of_getElem? found) literal)
      · exact .inr ⟨entry,body,depth,ordinary,.union (List.mem_of_getElem? found) atom,inside⟩
  | mu part => exact .inr ⟨_,_,_,_,.mu _ _ _ _,part⟩

private theorem union_row [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal state) (available : Values state values)
    (row : EdgeValue Symbol Guard) (part : RowAt (run (makeUnion values) state).1 row) :
    ∃ value ∈ values, RowAt value row := by
  rcases row_parts part with literal | ⟨entry,body,depth,ordinary,atom,inside⟩
  · obtain ⟨value,member,found⟩ := (SourceCurrentLiteralUnionParts.row state normal.facts normal.live
        values available row).mp literal
    exact ⟨value,member,literal_row found⟩
  · obtain ⟨value,member,found⟩ := (SourceCurrentLiteralUnionParts.literal state normal.facts
        values available (.mu entry body depth ordinary)).mp atom
    exact ⟨value,member,atom_row found (.mu inside)⟩

private theorem finish_row (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (row : EdgeValue Symbol Guard)
    (part : RowAt (finish smart (.mu entry body depth ordinary)) row) : RowAt body row := by
  cases smart with
  | false => cases part with | mu inside => exact inside
  | true =>
      change RowAt (cleanup (.mu entry body depth ordinary)) row at part
      unfold cleanup at part
      split at part
      · exact part
      · split at part
        · cases part
        · cases part with | mu inside => exact inside

private theorem row_call [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (EdgeSyntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after reader : State Symbol Guard) (context : InternedFreshOrdinaryContext.Context before inputs)
    (outputs : List (EdgeValue Symbol Guard))
    (actual : buildEdges expressions inputs before = .done outputs after)
    (growth : Grows after reader) (index : Nat) (row : EdgeValue Symbol Guard)
    (found : outputs[index]? = some row) :
    ∃ symbol guard children,
      ∃ call : RowCall expressions inputs before outputs after reader index symbol guard children,
        call.output = row := by
  induction expressions generalizing before outputs index with
  | nil =>
      simp only [buildEdges,Outcome.done.injEq] at actual
      obtain ⟨rfl,rfl⟩ := actual
      simp only [List.getElem?_nil] at found
      cases found
  | cons expression expressions ih =>
    cases expression with
    | mk ownSymbol ownGuard ownChildren =>
      cases childDone : buildMany ownChildren inputs before with
      | pending key state => simp only [buildEdges,childDone,Outcome.bind] at actual; cases actual
      | done values middle =>
        let made := run (makeEdge ownSymbol ownGuard values) middle
        cases tail : buildEdges expressions inputs made.2 with
        | pending key state =>
            simp only [buildEdges,childDone,Outcome.bind,work] at actual
            change (buildEdges expressions inputs made.2).bind _ = _ at actual
            simp only [tail,Outcome.bind] at actual
            cases actual
        | done remaining last =>
          simp only [buildEdges,childDone,Outcome.bind,work] at actual
          change (buildEdges expressions inputs made.2).bind _ = _ at actual
          simp only [tail,Outcome.bind,Outcome.done.injEq] at actual
          obtain ⟨rfl,rfl⟩ := actual
          have childChecked := buildMany_verified ownChildren inputs before context.normal.facts context.inputs
          have middleContext : InternedFreshOrdinaryContext.Context middle inputs := by
            simpa only [childDone,Outcome.state] using context.many ownChildren
          have childrenAvailable := childChecked.result values middle childDone
          have edgeChecked := InternedNestedFacts.edge_verified ownSymbol ownGuard values middle
            middleContext.normal.facts childrenAvailable
          have nextContext : InternedFreshOrdinaryContext.Context made.2 inputs :=
            middleContext.edge ownSymbol ownGuard values childrenAvailable
          have tailChecked := buildEdges_verified expressions inputs made.2 nextContext.normal.facts nextContext.inputs
          have nextGrowth : Grows made.2 reader := grows_trans
            (by simpa only [tail,Outcome.state] using tailChecked.growth) growth
          have middleGrowth : Grows middle reader := grows_trans edgeChecked.growth nextGrowth
          cases index with
          | zero =>
            have same : made.1 = row := Option.some.inj found
            have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleContext.normal.facts
              ownSymbol ownGuard values childrenAvailable
            exact ⟨ownSymbol,ownGuard,ownChildren,
              ⟨before,middle,made.2,values,made.1,rfl,rfl,
                (by simp only [List.take_zero,buildEdges]),childDone,rfl,tail,context,
                fields.1,fields.2.1,fields.2.2,
                grows_trans (by simpa only [childDone,Outcome.state] using childChecked.growth) middleGrowth,
                middleGrowth,nextGrowth⟩,same⟩
          | succ index =>
            obtain ⟨symbol,guard,children,call,same⟩ := ih made.2 nextContext remaining tail nextGrowth index found
            refine ⟨symbol,guard,children,{call with selected := call.selected, earlier := ?_, suffix := ?_},same⟩
            · simp only [List.take_succ_cons,buildEdges,childDone,Outcome.bind,work]
              exact congrArg (fun result => result.bind (fun rows final => .done (made.1 :: rows) final)) call.earlier
            · simpa only [List.drop_succ_cons,Nat.add_assoc] using call.suffix

private theorem member_call [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after : State Symbol Guard) (context : Context before inputs)
    (values : List (Value Symbol Guard)) (actual : buildMany expressions inputs before = .done values after)
    (index : Nat) (value : Value Symbol Guard) (found : values[index]? = some value) :
    ∃ expression current next,
      expressions[index]? = some expression ∧
      buildMany (expressions.take index) inputs before = .done (values.take index) current ∧
      Context current inputs ∧ build expression inputs current = .done value next ∧
      buildMany (expressions.drop (index + 1)) inputs next = .done (values.drop (index + 1)) after := by
  induction expressions generalizing before values index with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at actual
      obtain ⟨rfl,rfl⟩ := actual
      simp only [List.getElem?_nil] at found
      cases found
  | cons expression expressions ih =>
      cases one : build expression inputs before with
      | pending key state => simp only [buildMany,one,Outcome.bind] at actual; cases actual
      | done first middle =>
        cases tail : buildMany expressions inputs middle with
        | pending key state => simp only [buildMany,one,tail,Outcome.bind] at actual; cases actual
        | done rest final =>
          simp only [buildMany,one,tail,Outcome.bind,Outcome.done.injEq] at actual
          obtain ⟨rfl,rfl⟩ := actual
          cases index with
          | zero =>
              have same : first = value := Option.some.inj found
              subst value
              exact ⟨expression,before,middle,rfl,(by simp only [List.take_zero,buildMany]),context,one,tail⟩
          | succ index =>
              have middleContext : Context middle inputs := by
                simpa only [one,Outcome.state] using context.build expression
              obtain ⟨child,current,next,source,prefix,childContext,called,suffix⟩ :=
                ih middle middleContext rest tail index found
              refine ⟨child,current,next,source,?_,childContext,called,?_⟩
              · simp only [List.take_succ_cons,buildMany,one,Outcome.bind,prefix]
              · simpa only [List.drop_succ_cons,Nat.add_assoc] using suffix

/-- Completed source execution derives every structural row alternative from actual calls. -/
theorem build_row_origin [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (raw : Value Symbol Guard) (after : State Symbol Guard)
    (context : Context before inputs) (actual : build expression inputs before = .done raw after)
    (row : EdgeValue Symbol Guard) (part : RowAt raw row) :
    SourceRow expression inputs before raw after row := by
  generalize measure : sizeOf expression = bound
  induction bound using Nat.strongRecOn generalizing expression inputs before raw after with
  | ind bound ih =>
    cases expression with
    | empty =>
        simp only [build,Outcome.done.injEq] at actual
        obtain ⟨rfl,rfl⟩ := actual
        cases part
    | var index =>
        cases found : inputs[index]? with
        | none =>
            simp only [build,found,Option.getD_none,Outcome.done.injEq] at actual
            obtain ⟨rfl,rfl⟩ := actual
            cases part
        | some captured =>
            simp only [build,found,Option.getD_some,Outcome.done.injEq] at actual
            obtain ⟨rfl,rfl⟩ := actual
            exact .capture found part
    | node expressions =>
        cases built : buildEdges expressions inputs before with
        | pending key state => simp only [build,built,Outcome.bind] at actual; cases actual
        | done rows middle =>
            have made : run (makeNode rows) middle = (raw,after) :=
              Prod.ext (Outcome.done.inj (by simpa only [build,built,Outcome.bind,work] using actual)).1
                (Outcome.done.inj (by simpa only [build,built,Outcome.bind,work] using actual)).2
            have middleContext : Context middle inputs := by
              simpa only [built,Outcome.state] using context.edges expressions
            have checked := buildEdges_verified expressions inputs before context.base.normal.facts context.base.inputs
            have resident := checked.result rows middle built
            have ordinary := SourceEqualityRequiredCache.node_ordinary rows middle middleContext.base.normal.facts resident
            rw [made] at ordinary
            have selected : ∃ outputIndex, (nodeEdges raw)[outputIndex]? = some row := by
              cases raw with
              | node entry rows level free => cases part with | node found => exact ⟨_,found⟩
              | empty => cases part
              | reference | union | mu => cases ordinary
            obtain ⟨outputIndex,selected⟩ := selected
            have physical := EqualityLeafProjectionPhysical.makeNode_edges rows middle
              middleContext.base.normal.facts.coherent middleContext.base.normal.facts.linked resident
            rw [made] at physical
            have original := List.mem_filter.mp (canonicalEdges_member _ row
              (physical ▸ List.mem_of_getElem? selected))
            obtain ⟨sourceIndex,found⟩ := List.mem_iff_getElem?.mp original.1
            have growth : Grows middle after := by
              simpa only [made] using (run_correct (makeNode rows) middle middleContext.base.normal.facts.coherent.valid).2
            obtain ⟨symbol,guard,children,call,same⟩ :=
              row_call expressions inputs before middle after context.base rows built growth sourceIndex row found
            exact .node built made selected call same
    | union expressions =>
        cases built : buildMany expressions inputs before with
        | pending key state => simp only [build,built,Outcome.bind] at actual; cases actual
        | done values middle =>
            have made : run (makeUnion values) middle = (raw,after) :=
              Prod.ext (Outcome.done.inj (by simpa only [build,built,Outcome.bind,work] using actual)).1
                (Outcome.done.inj (by simpa only [build,built,Outcome.bind,work] using actual)).2
            have middleContext : Context middle inputs := by
              simpa only [built,Outcome.state] using context.many expressions
            have checked := buildMany_verified expressions inputs before context.base.normal.facts context.base.inputs
            have available := checked.result values middle built
            have initial : RowAt (run (makeUnion values) middle).1 row := by simpa only [made] using part
            obtain ⟨value,member,inside⟩ := union_row values middle middleContext.base.normal available row initial
            obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
            obtain ⟨child,current,next,source,prefix,childContext,called,suffix⟩ :=
              member_call expressions inputs before middle context values built index value found
            have smaller : sizeOf child < bound := by
              have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? source)
              simp only [Syntax.union.sizeOf_spec] at measure
              omega
            have nested := @ih (sizeOf child) smaller child inputs current value next childContext called inside rfl
            exact .union built made source found prefix childContext called suffix nested
    | binder smart body =>
        obtain ⟨depth,afterDepth,ordinary,cut,_rawOrdinary,_rawHeap,depthDone,ordinaryDone,requested,
          _depthContext,_cutContext,afterContext,_rawDone,_filtered,_rawContext,_growth,_issued,
          depthAvailable,ordinaryAvailable⟩ :=
          SourceCurrentNativeBinderExecution.decompose smart body inputs before raw after context actual
        obtain ⟨entry,storedBody,selected,returned⟩ := SourceCurrentNativeRequestProbes.request_probes
          smart depth ordinary (callback body inputs) cut raw after requested afterContext.base.normal.facts
          depthAvailable ordinaryAvailable
        exact .binder depthDone ordinaryDone requested selected returned
          (finish_row smart entry storedBody depth ordinary row (returned ▸ part))

end MicroCFTA.SourceCurrentBuildStructuralRowOrigins
