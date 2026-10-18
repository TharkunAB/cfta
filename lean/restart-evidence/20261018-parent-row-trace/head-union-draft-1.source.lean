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
    rcases description with ⟨noFree,sameValue,sameState⟩ | ⟨opened,values,at,callsOwn,made,exactOrigins⟩
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
  refine ⟨result,after,head,keeps,returned,noFree,ordinaryResult,
    chosen,final,outputs,memberAfter,called,calls,memberKeeps,memberGrowth,growth,paired,?_⟩
  intro index row selected
  obtain ⟨memberIndex,original,output,found,chosenOutput,origin⟩ := indexedOrigins row (origins index row selected)
  obtain ⟨source,sourceFound,warm⟩ := paired_index paired memberIndex output chosenOutput
  have same := Option.some.inj (sourceFound.symm.trans found)
  subst source
  have finalSource := keeps.available original (bodyAvailable.children original (List.mem_of_getElem? found))
  have finalReplacements : Replacements after environment :=
    fun name replacement present => keeps.available replacement (replacements name replacement present)
  exact ⟨memberIndex,original,output,found,chosenOutput,origin,
    member_rows environment after keeps.ready original output finalSource finalReplacements warm row origin⟩

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
