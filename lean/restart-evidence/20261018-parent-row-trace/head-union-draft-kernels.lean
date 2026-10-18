import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceCurrentRecursiveHeadNodeRows
import MicroCFTA.SourceCurrentStoredUnionObservations
import MicroCFTA.SourceCurrentStoredCallsReplay

/-!
# Earlier node alternatives in actual union-body Head exposure

Initial ready inputs construct the Head and its ordered stored member calls.
Each selected row retains a literal member occurrence. A node member also
retains its original row index and warm ordered child calls. Other member
shapes retain their actual returned-value origin without a fusion claim.
-/
namespace MicroCFTA.SourceCurrentRecursiveHeadUnionRows
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps Ordinary)
open SourceEqualityRequiredHead (Head)
open SourceCurrentRecursiveHeadRowOrigins (selfEnvironment BodyRows)
open SourceCurrentStoredNodeExpansion (RowCalls)
open SourceCurrentStoredSubstitutionCalls (Calls)
open MergedFreshOrdinaryGraph (Origin)
open InternedBinderProtocol (NodeKey Reference)

private theorem paired_index {A B : Type} {relation : A → B → Prop}
    {originals : List A} {outputs : List B} (paired : All₂ relation originals outputs)
    (index : Nat) (output : B) (selected : outputs[index]? = some output) :
    ∃ original, originals[index]? = some original ∧ relation original output := by
  induction paired generalizing index with
  | nil => simp at selected
  | cons original rest ih =>
      cases index with
      | zero =>
          have same := Option.some.inj selected
          subst output
          exact ⟨_,rfl,original⟩
      | succ index => exact ih index (by simpa using selected)

private theorem calls_unique [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {originals values other : List (Value Symbol Guard)} {before after final : State Symbol Guard}
    (first : Calls environment originals before values after) (second : Calls environment originals before other final) :
    values = other ∧ after = final := by
  induction first generalizing other final with
  | nil => cases second; exact ⟨rfl,rfl⟩
  | cons original originals before middle after value values actual rest ih =>
      cases second with
      | cons _ _ _ next final output outputs done later =>
          obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans done)
          obtain ⟨rfl,rfl⟩ := ih later
          exact ⟨rfl,rfl⟩

private theorem closed_pairs [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    {originals outputs : List (Value Symbol Guard)}
    (paired : All₂ (fun original output => execute original environment common = .done output common) originals outputs)
    (closed : ∀ original ∈ originals, original.free = []) : outputs = originals := by
  induction paired with
  | nil => rfl
  | cons called rest ih =>
      have same := (Outcome.done.inj (called.symm.trans
        (SourceCurrentStoredUnionObservations.closed _ environment common (closed _ List.mem_cons_self)))).1
      exact congr (congrArg List.cons same) (ih (fun value member => closed value (List.mem_cons_of_mem _ member)))

/-- A literal source-node member retains its earlier rows and exact reconstructed children. -/
def MemberRows [DecidableEq (EdgeKey Symbol Guard)] (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (original : Value Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  match original with
  | .node _ originals _ _ =>
      ∃ outputs, All₂ (RowCalls environment common) originals outputs ∧
        ∃ (sourceIndex : Nat) (source : EdgeValue Symbol Guard),
          originals[sourceIndex]? = some source ∧ outputs[sourceIndex]? = some row ∧
          RowCalls environment common source row ∧ row ∈ surviving outputs
  | .empty | .reference .. | .union .. | .mu .. => True

private theorem member_rows [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard) (ready : Ready common)
    (original output : Value Symbol Guard) (available : Available common original)
    (replacements : Replacements common environment)
    (called : execute original environment common = .done output common)
    (row : EdgeValue Symbol Guard) (origin : Origin common [output] row) :
    MemberRows environment common original row := by
  cases original with
  | empty | reference | union | mu => trivial
  | node entry originals level free =>
      obtain ⟨outputs,paired,_,exposed⟩ := SourceCurrentStoredNodeExpansion.node_warm
        entry originals level free environment common ready.semantic.1.normal available replacements output called
      have survives := (exposed common row).mp origin
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp survives).1
      obtain ⟨source,sourceIndex,calls⟩ := paired_index paired index row found
      exact ⟨outputs,paired,index,source,sourceIndex,found,calls,survives⟩

/-- Every selected Head row retains its actual indexed union member and source-node expansion. -/
def Rows [DecidableEq (EdgeKey Symbol Guard)]
    (entry bodyEntry : Interned NodeKey) (originals : List (Value Symbol Guard))
    (level : Nat) (free : List Reference) (depth ordinary : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  let body : Value Symbol Guard := .union bodyEntry originals level free
  let environment := selfEnvironment entry body depth ordinary
  ∃ unfolded middle outputs memberAfter,
    execute body environment before = .done unfolded middle ∧
    Calls environment originals before outputs memberAfter ∧ Keeps before memberAfter ∧
    Grows memberAfter middle ∧ Grows middle after ∧
    All₂ (fun original output => execute original environment after = .done output after) originals outputs ∧
    (∀ (memberIndex : Nat) (original output : Value Symbol Guard),
      originals[memberIndex]? = some original → outputs[memberIndex]? = some output →
      ∀ row, Origin after [output] row → MemberRows environment after original row) ∧
    ∀ (index : Nat) (row : EdgeValue Symbol Guard), (nodeEdges result)[index]? = some row →
      ∃ (memberIndex : Nat) (original output : Value Symbol Guard),
        originals[memberIndex]? = some original ∧ outputs[memberIndex]? = some output ∧
        Origin after [output] row ∧ MemberRows environment after original row

/-- Initial closed Mu data constructs its union-body Head and earlier literal-node row calls. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (entry bodyEntry : Interned NodeKey) (originals : List (Value Symbol Guard))
    (level : Nat) (free : List Reference) (depth ordinary : Value Symbol Guard)
    (before : State Symbol Guard) (ready : Ready before)
    (available : Available before (.mu entry (.union bodyEntry originals level free) depth ordinary))
    (closed : (Value.mu entry (.union bodyEntry originals level free) depth ordinary).free = []) :
    ∃ result after, Head (.mu entry (.union bodyEntry originals level free) depth ordinary) before result after ∧
      Keeps before after ∧ Available after result ∧ result.free = [] ∧ Ordinary result ∧
      Rows entry bodyEntry originals level free depth ordinary before result after := by
  let body : Value Symbol Guard := .union bodyEntry originals level free
  let value : Value Symbol Guard := .mu entry body depth ordinary
  let environment := selfEnvironment entry body depth ordinary
  have bodyAvailable : Available before body := available.children body (by simp [children,body])
  have replacements : Replacements before environment := by
    intro name replacement found
    dsimp only [environment,selfEnvironment] at found
    split at found
    · cases found; exact available
    · cases found
  obtain ⟨result,after,head,keeps,returned,noFree,ordinaryResult,unfolded,middle,called,description,growth,_,origins⟩ :=
    SourceCurrentRecursiveHeadRowOrigins.complete value before ready available closed
  obtain ⟨chosen,final,outputs,memberAfter,done,calls,bodyKeeps,memberKeeps,_,_,memberGrowth,_⟩ :=
    SourceCurrentStoredUnionObservations.complete bodyEntry originals level free environment before ready bodyAvailable replacements
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (done.symm.trans called)
  have paired := SourceCurrentStoredCallsReplay.replay calls after ready.semantic.1.normal.facts.coherent.valid
    (grows_trans memberGrowth growth)
  have indexedOrigins : ∀ row, Origin after [chosen] row →
      ∃ (index : Nat) (original output : Value Symbol Guard),
        originals[index]? = some original ∧ outputs[index]? = some output ∧ Origin after [output] row := by
    rcases description with ⟨noFree,sameValue,sameState⟩ | ⟨opened,values,memberHeap,callsOwn,made,exactOrigins⟩
    · have fields := InternedNormalizationFree.union_free before ready.semantic.1.normal.facts.coherent
        bodyEntry originals level free bodyAvailable.resident
      have closedMembers : ∀ original ∈ originals, original.free = [] := by
        intro original member
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro name named
        have included := (childFree_member originals name).mpr ⟨original,member,named⟩
        rw [←fields,noFree] at included
        cases included
      have sameOutputs := closed_pairs environment after paired closedMembers
      intro row origin
      rw [sameValue] at origin
      obtain ⟨original,member,origin⟩ := (MergedFreshOrdinaryGraph.origin_union after bodyEntry originals level free row).mp origin
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact ⟨index,original,original,found,by rw [sameOutputs]; exact found,origin⟩
    · obtain ⟨rfl,rfl⟩ := calls_unique callsOwn calls
      exact fun row origin => (exactOrigins after row).mp origin
  have expansions : ∀ (memberIndex : Nat) (original output : Value Symbol Guard),
      originals[memberIndex]? = some original → outputs[memberIndex]? = some output →
      ∀ row, Origin after [output] row → MemberRows environment after original row := by
    intro memberIndex original output found chosenOutput row origin
    obtain ⟨source,sourceFound,warm⟩ := paired_index paired memberIndex output chosenOutput
    have same := Option.some.inj (sourceFound.symm.trans found)
    subst source
    have finalSource := keeps.available original (bodyAvailable.children original (List.mem_of_getElem? found))
    have finalReplacements : Replacements after environment :=
      fun name replacement present => keeps.available replacement (replacements name replacement present)
    exact member_rows environment after keeps.ready original output finalSource finalReplacements warm row origin
  refine ⟨result,after,head,keeps,returned,noFree,ordinaryResult,
    chosen,final,outputs,memberAfter,called,calls,memberKeeps,memberGrowth,growth,paired,expansions,?_⟩
  intro index row selected
  obtain ⟨memberIndex,original,output,found,chosenOutput,origin⟩ := indexedOrigins row (origins index row selected)
  exact ⟨memberIndex,original,output,found,chosenOutput,origin,expansions memberIndex original output found chosenOutput row origin⟩

/-- An actual union-body Head has the same original member indices and child calls. -/
theorem actual [DecidableEq (EdgeKey Symbol Guard)]
    (entry bodyEntry : Interned NodeKey) (originals : List (Value Symbol Guard))
    (level : Nat) (free : List Reference) (depth ordinary : Value Symbol Guard)
    (before : State Symbol Guard) (ready : Ready before)
    (available : Available before (.mu entry (.union bodyEntry originals level free) depth ordinary))
    (closed : (Value.mu entry (.union bodyEntry originals level free) depth ordinary).free = [])
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (head : Head (.mu entry (.union bodyEntry originals level free) depth ordinary) before result after) :
    Keeps before after ∧ Available after result ∧ result.free = [] ∧ Ordinary result ∧
      Rows entry bodyEntry originals level free depth ordinary before result after := by
  obtain ⟨chosen,final,produced,keeps,returned,noFree,ordinary,rows⟩ :=
    complete entry bodyEntry originals level free depth ordinary before ready available closed
  obtain ⟨rfl,rfl⟩ := produced.unique head
  exact ⟨keeps,returned,noFree,ordinary,rows⟩

end MicroCFTA.SourceCurrentRecursiveHeadUnionRows

set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.RecursiveHeadUnionKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceEqualityRequiredHead (Head)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentRecursiveHeadRowOrigins (selfEnvironment)
open SourceCurrentStoredNodeExpansion (RowCalls)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def plain : Guard := SourceEqualityConstraintConstructors.top
private def selected : Guard := ⟨some [[[0],[1]]],.same [0] [1]⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def nested : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf",.top) plain [],.mk ("pair",.top) plain [.var 0,.var 0]])
private def expression : Syntax Symbol Guard := .binder false (.union [
  .node [.mk ("chosen",.top) selected [.var 0,nested]],
  .binder false (.node [.mk ("inner",.top) plain [.var 0,.var 1]])])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def exposed := MergedFreshOrdinaryExposure.nodeEdges 32 root heap
private def rawRows : List (EdgeValue Symbol Guard) := match exposed with | .done rows _ => rows | _ => []
private def made := run (makeNode rawRows) exposed.state
private def source : Value Symbol Guard := match root with
  | .mu _ (.union _ members _ _) _ _ => (members[0]?).getD .empty
  | _ => .empty
private def environment : InternedStoredSubstitution.Environment Symbol Guard := match root with
  | .mu entry body depth ordinary => selfEnvironment entry body depth ordinary
  | _ => fun _ => none
private def sourceRun := InternedFreshOrdinaryStoredSubstitution.execute source environment made.2
private def sourceValue : Value Symbol Guard := match sourceRun with | .done value _ => value | _ => .empty
private def chosenRow : EdgeValue Symbol Guard := ((nodeEdges sourceValue)[0]?).getD
  (run (makeEdge ("unused",.top) plain []) empty).1

private theorem built_done : built = .done root heap := by
  obtain ⟨value,state,done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built,root,heap,done,InternedNestedConstruction.Outcome.state]
private theorem initial_ready : Ready heap := SourceEqualityRequiredCache.constructed expression root heap built_done
private theorem available : Available heap root := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem closed : root.free = [] := by cbv
private theorem read_done : exposed = .done rawRows exposed.state := by
  have tag : (match exposed with | .done .. => true | _ => false) = true := by cbv
  cases found : exposed <;> simp_all only [rawRows,MergedSourceExposure.Result.state,Bool.false_eq_true]
private theorem head : Head root heap made.1 made.2 := .read 32 rawRows exposed.state read_done rfl
private theorem paired_forward {A B : Type} {relation : A → B → Prop} {originals : List A} {outputs : List B}
    (paired : All₂ relation originals outputs) (original : A) (index : Nat) (selected : originals[index]? = some original) :
    ∃ output, outputs[index]? = some output ∧ relation original output := by
  induction paired generalizing index with
  | nil => simp at selected
  | cons first rest ih =>
    cases index with
    | zero =>
      have same := Option.some.inj selected
      subst original
      exact ⟨_,rfl,first⟩
    | succ index => exact ih index (by simpa using selected)

private theorem witness :
    built = .done root heap ∧ Head root heap made.1 made.2 ∧ Keeps heap made.2 ∧
    source.free ≠ [] ∧ (match source with | .node .. => True | _ => False) ∧
    (nodeEdges made.1)[0]? = some chosenRow ∧ chosenRow.entry.key.constraint = selected ∧
    chosenRow.children.length = 2 ∧
    SourceCurrentRecursiveHeadUnionRows.MemberRows environment made.2 source chosenRow ∧
    ∃ (entry bodyEntry : Interned InternedBinderProtocol.NodeKey) (originals : List (Value Symbol Guard))
      (level : Nat) (free : List InternedBinderProtocol.Reference) (depth ordinary : Value Symbol Guard),
      root = .mu entry (.union bodyEntry originals level free) depth ordinary ∧
      SourceCurrentRecursiveHeadUnionRows.Rows entry bodyEntry originals level free depth ordinary heap made.1 made.2 := by
  have shape : ∃ (entry bodyEntry : Interned InternedBinderProtocol.NodeKey) (originals : List (Value Symbol Guard))
      (level : Nat) (free : List InternedBinderProtocol.Reference) (depth ordinary : Value Symbol Guard),
      root = .mu entry (.union bodyEntry originals level free) depth ordinary := by
    have tag : (match root with | .mu _ (.union ..) _ _ => True | _ => False) := by cbv
    cases same : root <;> simp only [same] at tag
    all_goals try cases tag
    rename_i entry body depth ordinary
    cases bodyShape : body <;> simp only [bodyShape] at tag
    all_goals try cases tag
    exact ⟨_,_,_,_,_,_,_,rfl⟩
  obtain ⟨entry,bodyEntry,originals,level,free,depth,ordinary,shape⟩ := shape
  have known := available
  have noFree := closed
  have literal := head
  rw [shape] at known noFree literal
  obtain ⟨keeps,_,_,_,rows⟩ := SourceCurrentRecursiveHeadUnionRows.actual
    entry bodyEntry originals level free depth ordinary heap initial_ready known noFree made.1 made.2 literal
  have retained := rows
  obtain ⟨unfolded,middle,outputs,memberAfter,called,calls,memberKeeps,memberGrowth,growth,paired,expansions,origins⟩ := rows
  have sourceIndex : originals[0]? = some source := by
    have computed : (match root with | .mu _ (.union _ members _ _) _ _ => members[0]? | _ => none) = some source := by cbv
    simpa only [shape] using computed
  obtain ⟨output,outputIndex,warm⟩ := paired_forward paired source 0 sourceIndex
  have exactEnvironment : selfEnvironment entry (.union bodyEntry originals level free) depth ordinary = environment := by
    simp only [environment,shape]
  rw [exactEnvironment] at warm expansions
  have same : sourceValue = output := by simp only [sourceValue,sourceRun,warm]
  subst output
  have positive : (nodeEdges sourceValue)[0]? = some chosenRow := by cbv
  have origin : MergedFreshOrdinaryGraph.Origin made.2 [sourceValue] chosenRow :=
    ⟨sourceValue,.seed List.mem_cons_self,List.mem_of_getElem? positive⟩
  have originalRows := expansions 0 source sourceValue sourceIndex outputIndex chosenRow origin
  refine ⟨built_done,head,keeps,?_,?_,?_,?_,?_,originalRows,
    entry,bodyEntry,originals,level,free,depth,ordinary,shape,retained⟩
  · intro falseClosed
    have opened : source.free.isEmpty = false := by cbv
    rw [falseClosed] at opened
    cases opened
  · cbv
  · cbv
  · cbv
  · cbv

/-- An actual union-body Head exposes a row from its open original node alternative. -/
theorem open_node_alternative :
    built = .done root heap ∧ Head root heap made.1 made.2 ∧ Keeps heap made.2 ∧
    source.free ≠ [] ∧ (match source with | .node .. => True | _ => False) ∧
    (nodeEdges made.1)[0]? = some chosenRow ∧ chosenRow.entry.key.constraint = selected ∧
    chosenRow.children.length = 2 ∧
    SourceCurrentRecursiveHeadUnionRows.MemberRows environment made.2 source chosenRow ∧
    ∃ (entry bodyEntry : Interned InternedBinderProtocol.NodeKey) (originals : List (Value Symbol Guard))
      (level : Nat) (free : List InternedBinderProtocol.Reference) (depth ordinary : Value Symbol Guard),
      root = .mu entry (.union bodyEntry originals level free) depth ordinary ∧
      SourceCurrentRecursiveHeadUnionRows.Rows entry bodyEntry originals level free depth ordinary heap made.1 made.2 := witness

end MicroCFTA.RecursiveHeadUnionKernels
