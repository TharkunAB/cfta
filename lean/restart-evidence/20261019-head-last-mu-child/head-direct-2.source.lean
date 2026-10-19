import MicroCFTA.SourceCurrentRecursiveHeadChainRows
import MicroCFTA.SourceCurrentStoredMuUnfoldChildContexts

/-!
# The last Mu call on a selected Head branch

The suffix selects union members and retains other collector effects.
It has no explicit Mu call on this branch. Other branches can allocate Mu
records during an advance. The selected stored body need not be an
original input body. This result gives no global recursion bound.
-/
namespace MicroCFTA.SourceCurrentRecursiveHeadMuChildContexts
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryStoredSubstitution (unfold)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceEqualityRequiredHead (Head)
open SourceCurrentRecursiveHeadChainRows (Chain)
open SourceCurrentLiteralRootParts (Row)
open SourceCurrentNativeMuPublication (History Written)
open SourceCurrentStoredMuUnfoldChildContexts (Child)
open InternedBinderProtocol (NodeKey)

/-- A selected branch suffix contains union choices and cache effects, but no explicit Mu call. -/
inductive Suffix : State Symbol Guard → Value Symbol Guard →
    State Symbol Guard → Value Symbol Guard → Prop where
  /-- The suffix starts at its actual ready heap. -/
  | start (ready : Ready before) : Suffix before value before value
  /-- A union step selects one literal member. -/
  | member (prior : Suffix before root current (.union entry members depth free))
      (index : Nat) (found : members[index]? = some value) : Suffix before root current value
  /-- Other collector effects retain the selected value. -/
  | advance (prior : Suffix before root current value) (keeps : Keeps current next) :
      Suffix before root next value

/-- Every suffix retains its actual cache interval. -/
theorem Suffix.keeps {before current : State Symbol Guard} {root value : Value Symbol Guard}
    (actual : Suffix before root current value) : Keeps before current := by
  induction actual with
  | start ready => exact SourceEqualityRequiredCache.pure_keeps _ ready
  | member _ _ _ ih => exact ih
  | advance _ keeps ih => exact ih.trans keeps

/-- A suffix's selected row is literal in its starting value. -/
theorem Suffix.literal {before current : State Symbol Guard} {root value : Value Symbol Guard}
    (actual : Suffix before root current value) (row : EdgeValue Symbol Guard)
    (literal : Row value row) : Row root row := by
  induction actual with
  | start => exact literal
  | member prior index found ih => exact ih (.union (List.mem_of_getElem? found) literal)
  | advance prior keeps ih => exact ih literal

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A chronological branch has no Mu call, or retains its last explicit Mu and the suffix after it. -/
theorem chain {before current : State Symbol Guard} {root value : Value Symbol Guard}
    (actual : Chain before root current value) :
    Suffix before root current value ∨
      ∃ (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
          (first second : State Symbol Guard) (returned : Value Symbol Guard),
        Chain before root first (.mu entry body depth ordinary) ∧
        unfold (.mu entry body depth ordinary) first = .done returned second ∧
        Suffix second returned current value := by
  induction actual with
  | start ready available closed => exact .inl (.start ready)
  | member prior index found ih =>
      rcases ih with suffix | ⟨entry,body,depth,ordinary,first,second,returned,earlierBranch,called,suffix⟩
      · exact .inl (.member suffix index found)
      · exact .inr ⟨entry,body,depth,ordinary,first,second,returned,earlierBranch,called,.member suffix index found⟩
  | mu prior called =>
      have current := (Chain.mu prior called).verified
      exact .inr ⟨_,_,_,_,_,_,_,prior,called,.start current.1.ready⟩
  | advance prior keeps ih =>
      rcases ih with suffix | ⟨entry,body,depth,ordinary,first,second,returned,earlierBranch,called,suffix⟩
      · exact .inl (.advance suffix keeps)
      · exact .inr ⟨entry,body,depth,ordinary,first,second,returned,earlierBranch,called,.advance suffix keeps⟩

/-- A selected Head child is literal initially or has a last stored Mu call with supported child context. -/
theorem head_child (value : Value Symbol Guard) (before : State Symbol Guard)
    (ready : Ready before) (available : Available before value) (closed : value.free = [])
    (result : Value Symbol Guard) (after : State Symbol Guard) (head : Head value before result after)
    (history : History empty after) (position : Nat) (row : EdgeValue Symbol Guard)
    (selected : (nodeEdges result)[position]? = some row)
    (index : Nat) (child : Value Symbol Guard) (childSelected : row.children[index]? = some child) :
    Row value row ∨
      ∃ (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
          (first second : State Symbol Guard) (returned : Value Symbol Guard)
          (terminal : State Symbol Guard) (terminalValue : Value Symbol Guard),
        Chain before value first (.mu entry body depth ordinary) ∧
        unfold (.mu entry body depth ordinary) first = .done returned second ∧
        Suffix second returned terminal terminalValue ∧ Keeps terminal after ∧
        Row returned row ∧ Written empty entry.key (.mu entry body depth ordinary) ∧
        Child body first second row index child := by
  obtain ⟨_,_,_,_,rows⟩ := SourceCurrentRecursiveHeadChainRows.actual
    value before ready available closed result after head
  obtain ⟨terminal,nodeEntry,originals,level,free,sourceIndex,branch,later,_warm,found,_calls⟩ :=
    rows position row selected
  have literal : Row (.node nodeEntry originals level free) row := .node (List.mem_of_getElem? found)
  rcases chain branch with suffix | ⟨entry,body,depth,ordinary,first,second,returned,earlierBranch,called,suffix⟩
  · exact .inl (suffix.literal row literal)
  · have known := earlierBranch.verified
    have literal := suffix.literal row literal
    have context := SourceCurrentStoredMuUnfoldChildContexts.unfold_child entry body depth ordinary first
      known.1.ready.semantic.1 known.2.1 returned second called after history
      (grows_trans suffix.keeps.growth later.growth) row literal index child childSelected
    exact .inr ⟨entry,body,depth,ordinary,first,second,returned,terminal,
      .node nodeEntry originals level free,earlierBranch,called,suffix,later,literal,context.1,context.2⟩

end MicroCFTA.SourceCurrentRecursiveHeadMuChildContexts
