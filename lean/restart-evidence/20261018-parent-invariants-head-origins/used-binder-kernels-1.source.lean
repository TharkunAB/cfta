import MicroCFTA.SourceCurrentUsedBinderRootAlternatives
import MicroCFTA.SourceCurrentNativeMuPublication
import MicroCFTA.SourceEqualityRequiredCache

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.UsedBinderKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentUsedBinderRootAlternatives (RootMatch AtomMatch)
open Language

private def output (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def captureSource : Syntax Nat Bool := .binder false (.node [.mk 7 false
  [.var 0,.binder false (.node [.mk 9 true [.var 0,.var 1]])]])
private def source : Syntax Nat Bool := .node [.mk 3 false [captureSource,captureSource],.mk 4 true []]
private def built := build source [] empty
private def root := output built
private def reader := built.state
private def captured := output (build captureSource [] empty)
private theorem actual : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual
private noncomputable def history : History empty reader := by
  simpa only [reader,built] using SourceCurrentNativeMuPublication.closed_history source
private theorem rootAvailable : Available reader root := (closed_verified source).result root reader actual
private theorem capturedAvailable : Available reader captured := rootAvailable.children captured (by cbv)
private def parts : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private def own : Reference := .interned (parts captured).1.identity
private def ordinary : Reference := .uninterned (ordinaryLevel (parts captured).2.2.1)
private def names (first second : Reference) : Prop :=
  (first = own ∧ second = ordinary) ∨ (first = second ∧ first ≠ own ∧ second ≠ ordinary)
private theorem ownAvailable : Available reader (.reference own) := reference_available reader own (by cbv)
private theorem ordinaryAvailable : Available reader (.reference ordinary) := InternedNestedProvenance.ordinary_available _ _
private theorem names_own : names own ordinary := Or.inl ⟨rfl,rfl⟩
private theorem compatible (first second : Reference) (matched : names first second) :
    first = own ↔ second = ordinary := by
  rcases matched with ⟨rfl,rfl⟩ | ⟨rfl,first,second⟩
  · exact Iff.rfl
  · exact iff_of_false first second

private theorem all_eq (values : List (Value Nat Bool)) : All₂ Eq values values := by
  induction values with
  | nil => exact .nil
  | cons value rest ih => exact .cons rfl ih
private theorem node_match (entry : Interned NodeKey) (rows : List (EdgeValue Nat Bool)) (depth free) :
    RootMatch names Eq (.node entry rows depth free) (.node entry rows depth free) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro atom part; cases part
  · intro atom part; cases part
  · intro row part
    cases part with
    | node member => exact ⟨row,.node member,rfl,rfl,all_eq row.children⟩
  · intro row part
    cases part with
    | node member => exact ⟨row,.node member,rfl,rfl,all_eq row.children⟩
private theorem mu_match (entry : Interned NodeKey) (body depth ordinary : Value Nat Bool) :
    RootMatch names Eq (.mu entry body depth ordinary) (.mu entry body depth ordinary) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro atom part; cases part; exact ⟨_,.mu _ _ _ _,rfl⟩
  · intro atom part; cases part; exact ⟨_,.mu _ _ _ _,rfl⟩
  · intro row part; cases part
  · intro row part; cases part
private theorem empty_match : RootMatch names Eq (.empty : Value Nat Bool) .empty := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro value part <;> cases part
private theorem reference_match : RootMatch names Eq (Value.reference own : Value Nat Bool) (.reference ordinary) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro atom part; cases part; exact ⟨_,.reference _,names_own⟩
  · intro atom part; cases part; exact ⟨_,.reference _,names_own⟩
  · intro row part; cases part
  · intro row part; cases part
private theorem root_match : RootMatch names Eq root root := by
  have shape : ∃ entry rows depth free, root = .node entry rows depth free := by
    exact ⟨_,_,_,_,by cbv⟩
  obtain ⟨entry,rows,depth,free,same⟩ := shape
  rw [same]
  exact node_match entry rows depth free
private theorem captured_match : RootMatch names Eq captured captured := by
  have shape : captured = .mu (parts captured).1 (parts captured).2.1 (parts captured).2.2.1 (parts captured).2.2.2 := by cbv
  rw [shape]
  exact mu_match _ _ _ _

private def firstMembers := [.reference own,captured,.empty,root,root]
private def secondMembers := [root,.empty,.reference ordinary,captured]
private theorem firstAvailable : Values reader firstMembers := by
  intro value member
  simp only [firstMembers,List.mem_cons,List.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact ownAvailable
  · exact capturedAvailable
  · exact empty_available _
  · exact rootAvailable
  · exact rootAvailable
private theorem secondAvailable : Values reader secondMembers := by
  intro value member
  simp only [secondMembers,List.mem_cons,List.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact rootAvailable
  · exact empty_available _
  · exact ordinaryAvailable
  · exact capturedAvailable
private theorem members :
    (∀ value ∈ firstMembers, ∃ other ∈ secondMembers, RootMatch names Eq value other) ∧
    (∀ value ∈ secondMembers, ∃ other ∈ firstMembers, RootMatch names Eq other value) := by
  constructor
  · intro value member
    simp only [firstMembers,List.mem_cons,List.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_,by simp [secondMembers],reference_match⟩
    · exact ⟨_,by simp [secondMembers],captured_match⟩
    · exact ⟨_,by simp [secondMembers],empty_match⟩
    · exact ⟨_,by simp [secondMembers],root_match⟩
    · exact ⟨_,by simp [secondMembers],root_match⟩
  · intro value member
    simp only [secondMembers,List.mem_cons,List.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨_,by simp [firstMembers],root_match⟩
    · exact ⟨_,by simp [firstMembers],empty_match⟩
    · exact ⟨_,by simp [firstMembers],reference_match⟩
    · exact ⟨_,by simp [firstMembers],captured_match⟩
private def firstCall := run (makeUnion firstMembers) reader
private def secondCall := run (makeUnion secondMembers) reader
private theorem firstNormal : InternedStoredMuOrigins.Normal firstCall.2 :=
  (SourceRecursiveIntersectionSemanticHeap.union firstMembers reader ready.semantic firstAvailable).1.normal
private theorem secondNormal : InternedStoredMuOrigins.Normal secondCall.2 :=
  (SourceRecursiveIntersectionSemanticHeap.union secondMembers reader ready.semantic secondAvailable).1.normal
private theorem firstOutput : Available firstCall.2 firstCall.1 :=
  (InternedNestedFacts.union_verified firstMembers reader ready.semantic.1.normal.facts firstAvailable).result _ _ rfl
private theorem secondOutput : Available secondCall.2 secondCall.1 :=
  (InternedNestedFacts.union_verified secondMembers reader ready.semantic.1.normal.facts secondAvailable).result _ _ rfl
private theorem union_match : RootMatch names Eq firstCall.1 secondCall.1 :=
  SourceCurrentUsedBinderRootAlternatives.union names Eq firstMembers secondMembers reader reader
    ready.semantic.1.normal ready.semantic.1.normal firstAvailable secondAvailable members

private theorem union_filter_proof :
    build source [] empty = .done root reader ∧ Ready reader ∧ Nonempty (History empty reader) ∧
    (match captured with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    RootMatch names Eq firstCall.1 secondCall.1 ∧
    RootMatch names Eq (SourceCurrentNativeCallbackErasure.eraseSelf own
      (run (withoutSelfReference own firstCall.1) firstCall.2).1)
      (SourceCurrentNativeCallbackErasure.eraseSelf ordinary
      (run (withoutSelfReference ordinary secondCall.1) secondCall.2).1) := by
  exact ⟨actual,ready,⟨history⟩,by cbv,union_match,
    SourceCurrentUsedBinderRootAlternatives.erased_filter names Eq own ordinary firstCall.1 secondCall.1
      firstCall.2 secondCall.2 firstNormal secondNormal firstOutput secondOutput union_match compatible⟩

/-- Source-built nested recursion and full guarded rows pass through reordered duplicate union operands and paired self erasure. -/
theorem union_filter :
    build source [] empty = .done root reader ∧ Ready reader ∧ Nonempty (History empty reader) ∧
    (match captured with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    RootMatch names Eq firstCall.1 secondCall.1 ∧
    RootMatch names Eq (SourceCurrentNativeCallbackErasure.eraseSelf own
      (run (withoutSelfReference own firstCall.1) firstCall.2).1)
      (SourceCurrentNativeCallbackErasure.eraseSelf ordinary
      (run (withoutSelfReference ordinary secondCall.1) secondCall.2).1) := union_filter_proof

private theorem bare_filter_proof :
    RootMatch names Eq
      (run (withoutSelfReference own (.reference own : Value Nat Bool)) reader).1
      (run (withoutSelfReference ordinary (.reference ordinary : Value Nat Bool)) reader).1 ∧
    RootMatch names Eq
      (SourceCurrentNativeCallbackErasure.eraseSelf own
        (run (withoutSelfReference own (.reference own : Value Nat Bool)) reader).1)
      (SourceCurrentNativeCallbackErasure.eraseSelf ordinary
        (run (withoutSelfReference ordinary (.reference ordinary : Value Nat Bool)) reader).1) := by
  exact ⟨SourceCurrentUsedBinderRootAlternatives.filter names Eq own ordinary _ _ reader reader
    ready.semantic.1.normal ready.semantic.1.normal ownAvailable ordinaryAvailable reference_match compatible (by simp),
    SourceCurrentUsedBinderRootAlternatives.erased_filter names Eq own ordinary _ _ reader reader
    ready.semantic.1.normal ready.semantic.1.normal ownAvailable ordinaryAvailable reference_match compatible⟩

/-- The actual bare-self filter preserves the paired references, and erasure removes both. -/
theorem bare_filter :
    RootMatch names Eq
      (run (withoutSelfReference own (.reference own : Value Nat Bool)) reader).1
      (run (withoutSelfReference ordinary (.reference ordinary : Value Nat Bool)) reader).1 ∧
    RootMatch names Eq
      (SourceCurrentNativeCallbackErasure.eraseSelf own
        (run (withoutSelfReference own (.reference own : Value Nat Bool)) reader).1)
      (SourceCurrentNativeCallbackErasure.eraseSelf ordinary
        (run (withoutSelfReference ordinary (.reference ordinary : Value Nat Bool)) reader).1) := bare_filter_proof

end MicroCFTA.UsedBinderKernels
