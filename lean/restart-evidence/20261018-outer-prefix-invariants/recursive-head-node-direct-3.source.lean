import MicroCFTA.SourceCurrentRecursiveHeadRowOrigins
import MicroCFTA.SourceCurrentStoredNodeExpansion
import MicroCFTA.InternedFreshOrdinaryReplay

/-!
# Original stored-node rows in actual recursive Head exposure

Initial ready data constructs the Head and its first stored-body call.
Each selected Head row retains an original body-row index. Its ordered
child calls and full edge fields replay at the exact final Head heap.
Closed stored bodies use their literal rows. Nested Mu children are allowed.
-/
namespace MicroCFTA.SourceCurrentRecursiveHeadNodeRows
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps Ordinary)
open SourceEqualityRequiredHead (Head)
open SourceCurrentRecursiveHeadRowOrigins (selfEnvironment)
open SourceCurrentStoredNodeExpansion (RowCalls)
open InternedBinderProtocol (NodeKey Reference)

private theorem paired_indexed {A B : Type} {relation : A → B → Prop}
    {originals : List A} {outputs : List B} (paired : All₂ relation originals outputs)
    (index : Nat) (output : B) (selected : outputs[index]? = some output) :
    ∃ original, originals[index]? = some original ∧ relation original output := by
  induction paired generalizing index with
  | nil => simp at selected
  | @cons original current originals outputs first rest ih =>
    cases index with
    | zero =>
      have same : current = output := by simpa using selected
      subst output
      exact ⟨_,rfl,first⟩
    | succ index =>
      obtain ⟨original,found,related⟩ := ih index (by simpa using selected)
      exact ⟨original,found,related⟩

/-- Every selected row retains its literal stored-body occurrence and final warm child calls. -/
def Rows [DecidableEq (EdgeKey Symbol Guard)]
    (entry bodyEntry : Interned NodeKey) (originals : List (EdgeValue Symbol Guard))
    (level : Nat) (free : List Reference) (depth ordinary : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  let body : Value Symbol Guard := .node bodyEntry originals level free
  let environment := selfEnvironment entry body depth ordinary
  ∃ unfolded middle outputs,
    execute body environment before = .done unfolded middle ∧
    Grows middle after ∧ execute body environment after = .done unfolded after ∧
    All₂ (RowCalls environment after) originals outputs ∧
    ∀ (index : Nat) (row : EdgeValue Symbol Guard), (nodeEdges result)[index]? = some row →
      ∃ (sourceIndex : Nat) (original : EdgeValue Symbol Guard), originals[sourceIndex]? = some original ∧ outputs[sourceIndex]? = some row ∧
        RowCalls environment after original row ∧ row ∈ surviving outputs

/-- Initial ready closed Mu data constructs its Head and indexed literal-node body sources. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (entry bodyEntry : Interned NodeKey) (originals : List (EdgeValue Symbol Guard))
    (level : Nat) (free : List Reference) (depth ordinary : Value Symbol Guard)
    (before : State Symbol Guard) (ready : Ready before)
    (available : Available before (.mu entry (.node bodyEntry originals level free) depth ordinary))
    (closed : (Value.mu entry (.node bodyEntry originals level free) depth ordinary).free = []) :
    ∃ result after, Head (.mu entry (.node bodyEntry originals level free) depth ordinary) before result after ∧
      Keeps before after ∧ Available after result ∧ result.free = [] ∧ Ordinary result ∧
      Rows entry bodyEntry originals level free depth ordinary before result after := by
  let body : Value Symbol Guard := .node bodyEntry originals level free
  let value : Value Symbol Guard := .mu entry body depth ordinary
  let environment := selfEnvironment entry body depth ordinary
  obtain ⟨result,after,head,keeps,returned,noFree,ordinaryResult,unfolded,middle,called,description,growth,warm,origins⟩ :=
    SourceCurrentRecursiveHeadRowOrigins.complete value before ready available closed
  have actualWarm : execute body environment after = .done unfolded after :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves body) [] body)
      ((leaves body).map (input environment)) before after unfolded middle
      ready.semantic.1.normal.facts.coherent.valid called growth
  have bodyAvailable : Available after body := keeps.available body
    (available.children body (by simp [children,body]))
  have replacements : Replacements after environment := by
    intro name replacement found
    dsimp only [environment,selfEnvironment] at found
    split at found
    · cases found
      exact keeps.available value available
    · cases found
  obtain ⟨outputs,paired,plain,exposed⟩ := SourceCurrentStoredNodeExpansion.node_warm
    bodyEntry originals level free environment after keeps.ready.semantic.1.normal
    bodyAvailable replacements unfolded actualWarm
  refine ⟨result,after,head,keeps,returned,noFree,ordinaryResult,unfolded,middle,outputs,called,growth,actualWarm,paired,?_⟩
  intro index row selected
  have survives := (exposed after row).mp (origins index row selected)
  obtain ⟨sourceIndex,outputIndex⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp survives).1
  obtain ⟨original,sourceIndexFound,calls⟩ := paired_indexed paired sourceIndex row outputIndex
  exact ⟨sourceIndex,original,sourceIndexFound,outputIndex,calls,survives⟩

/-- An actual Head has the same indexed body sources as the initial ready producer. -/
theorem actual [DecidableEq (EdgeKey Symbol Guard)]
    (entry bodyEntry : Interned NodeKey) (originals : List (EdgeValue Symbol Guard))
    (level : Nat) (free : List Reference) (depth ordinary : Value Symbol Guard)
    (before : State Symbol Guard) (ready : Ready before)
    (available : Available before (.mu entry (.node bodyEntry originals level free) depth ordinary))
    (closed : (Value.mu entry (.node bodyEntry originals level free) depth ordinary).free = [])
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (head : Head (.mu entry (.node bodyEntry originals level free) depth ordinary) before result after) :
    Keeps before after ∧ Available after result ∧ result.free = [] ∧ Ordinary result ∧
      Rows entry bodyEntry originals level free depth ordinary before result after := by
  obtain ⟨chosen,final,produced,keeps,returned,noFree,plain,rows⟩ :=
    complete entry bodyEntry originals level free depth ordinary before ready available closed
  obtain ⟨rfl,rfl⟩ := produced.unique head
  exact ⟨keeps,returned,noFree,plain,rows⟩

end MicroCFTA.SourceCurrentRecursiveHeadNodeRows
