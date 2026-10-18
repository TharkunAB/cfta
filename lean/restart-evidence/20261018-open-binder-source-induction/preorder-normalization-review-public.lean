import MicroCFTA.SourceCurrentOpenPreorderSimulation
import MicroCFTA.SourceEqualityRequiredCache

namespace MicroCFTA.PreorderNormalizationReview
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)
open InternedBinderProtocol (Reference NodeKey)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready)
open MergedFreshOrdinaryGraph (Origin successors)
open SourceCurrentOpenObservations (Same RowMatch ReferenceOrigin)
open SourceCurrentOpenOriginSteps (Path)
open SourceCurrentOpenWeakSimulation (Forward)
open SourceCurrentOpenPreorderSimulation (Directed Mutual)
open Productivity (Reachable)

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def leaf (symbol : Nat) : Syntax Nat Bool := .node [.mk symbol false []]
private def source : Syntax Nat Bool := .binder false (.node [.mk 9 false
  [.union [.binder false (leaf 1),.binder false (leaf 2),.var 0],
   .union [.union [leaf 1,leaf 2],.var 0]]])
private def built := build source [] empty
private def root := value built
private def reader := built.state
private def body : Value Nat Bool := match root with | .mu _ body _ _ => body | _ => .empty
private def own : Reference := match root with | .mu entry .. => .interned entry.identity | _ => .depth
private def u : Value Nat Bool := (children body)[0]?.getD .empty
private def v : Value Nat Bool := (children body)[1]?.getD .empty
private def unionMembers : Value Nat Bool → List (Value Nat Bool)
  | .union _ members .. => members | _ => []
private def muA := (unionMembers u)[0]?.getD .empty
private def muB := (unionMembers u)[1]?.getD .empty
private def z : Value Nat Bool := .reference own
private def muBody : Value Nat Bool → Value Nat Bool
  | .mu _ body .. => body | _ => .empty
private def a := muBody muA
private def b := muBody muB
private def merged := (unionMembers v)[0]?.getD .empty
private def rowA : EdgeValue Nat Bool := (nodeEdges a)[0]?.getD ⟨⟨0,⟨0,[],false⟩⟩,[]⟩
private def rowB : EdgeValue Nat Bool := (nodeEdges b)[0]?.getD ⟨⟨0,⟨0,[],false⟩⟩,[]⟩

private theorem actual : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual
private theorem root_available : Available reader root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro input member; cases member)).result root reader actual
private theorem body_available : Available reader body := by
  apply root_available.children body
  exact List.mem_of_getElem? (show (children root)[0]? = some body by cbv)
private theorem u_available : Available reader u := body_available.children u
  (List.mem_of_getElem? (show (children body)[0]? = some u by cbv))
private theorem v_available : Available reader v := body_available.children v
  (List.mem_of_getElem? (show (children body)[1]? = some v by cbv))
private theorem made_u : run (makeUnion [muA,muB,z]) reader = (u,reader) := by cbv
private theorem made_merged : run (makeUnion [a,b]) reader = (merged,reader) := by cbv
private theorem made_v : run (makeUnion [merged,z]) reader = (v,reader) := by cbv
private theorem unfolded_a : unfold muA reader = .done a reader := by cbv
private theorem unfolded_b : unfold muB reader = .done b reader := by cbv
private theorem su : successors reader u = [muA,muB,z] := by cbv
private theorem sv : successors reader v = [merged,z] := by cbv
private theorem sma : successors reader muA = [a] := by cbv
private theorem smb : successors reader muB = [b] := by cbv
private theorem sa : successors reader a = [] := by cbv
private theorem sb : successors reader b = [] := by cbv
private theorem sm : successors reader merged = [] := by cbv
private theorem sz : successors reader z = [] := by rfl
private theorem na : nodeEdges a = [rowA] := by cbv
private theorem nb : nodeEdges b = [rowB] := by cbv
private theorem nm : nodeEdges merged = [rowA,rowB] := by cbv
private theorem nu : nodeEdges u = [] := by cbv
private theorem nv : nodeEdges v = [] := by cbv
private theorem nma : nodeEdges muA = [] := by cbv
private theorem nmb : nodeEdges muB = [] := by cbv
private theorem nz : nodeEdges z = [] := by rfl

private theorem u_reached (target : Value Nat Bool)
    (actual : Reachable (successors reader) [u] target) :
    target = u ∨ target = muA ∨ target = muB ∨ target = z ∨ target = a ∨ target = b := by
  induction actual with
  | seed member => exact Or.inl (List.mem_singleton.mp member)
  | step previous next ih =>
      rcases ih with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [su] at next
        rcases List.mem_cons.mp next with rfl | rest
        · exact Or.inr (Or.inl rfl)
        · rcases List.mem_cons.mp rest with rfl | rest
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_singleton.mp rest))))
      · rw [sma] at next
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_singleton.mp next)))))
      · rw [smb] at next
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.mem_singleton.mp next)))))
      · rw [sz] at next; cases next
      · rw [sa] at next; cases next
      · rw [sb] at next; cases next

private theorem v_reached (target : Value Nat Bool)
    (actual : Reachable (successors reader) [v] target) : target = v ∨ target = merged ∨ target = z := by
  induction actual with
  | seed member => exact Or.inl (List.mem_singleton.mp member)
  | step previous next ih =>
      rcases ih with rfl | rfl | rfl
      · rw [sv] at next
        rcases List.mem_cons.mp next with present | present
        · exact Or.inr (Or.inl present)
        · exact Or.inr (Or.inr (List.mem_singleton.mp present))
      · rw [sm] at next; cases next
      · rw [sz] at next; cases next

private def isRef : Value Nat Bool → Bool | .reference .. => true | _ => false
private theorem u_nonref : isRef u = false := by cbv
private theorem v_nonref : isRef v = false := by cbv
private theorem ma_nonref : isRef muA = false := by cbv
private theorem mb_nonref : isRef muB = false := by cbv
private theorem a_nonref : isRef a = false := by cbv
private theorem b_nonref : isRef b = false := by cbv
private theorem m_nonref : isRef merged = false := by cbv
private theorem not_ref (value : Value Nat Bool) (plain : isRef value = false) (name : Reference) :
    .reference name ≠ value := by
  intro same
  have impossible : true = false := (congrArg isRef same).trans plain
  cases impossible

private theorem u_reference (name : Reference) : ReferenceOrigin reader [u] name ↔ name = own := by
  constructor
  · intro actual
    rcases u_reached (.reference name) actual with same | same | same | same | same | same
    · exact False.elim (not_ref u u_nonref name same)
    · exact False.elim (not_ref muA ma_nonref name same)
    · exact False.elim (not_ref muB mb_nonref name same)
    · exact Value.reference.inj same
    · exact False.elim (not_ref a a_nonref name same)
    · exact False.elim (not_ref b b_nonref name same)
  · intro same
    subst name
    apply Reachable.step (.seed List.mem_cons_self)
    rw [su]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

private theorem v_reference (name : Reference) : ReferenceOrigin reader [v] name ↔ name = own := by
  constructor
  · intro actual
    rcases v_reached (.reference name) actual with same | same | same
    · exact False.elim (not_ref v v_nonref name same)
    · exact False.elim (not_ref merged m_nonref name same)
    · exact Value.reference.inj same
  · intro same
    subst name
    apply Reachable.step (.seed List.mem_cons_self)
    rw [sv]
    exact List.mem_cons_of_mem _ List.mem_cons_self

private theorem u_path_a : Path reader 2 u a := by
  refine ⟨muA,?_,a,?_,rfl⟩
  · rw [su]; exact List.mem_cons_self
  · rw [sma]; exact List.mem_cons_self
private theorem u_path_b : Path reader 2 u b := by
  refine ⟨muB,?_,b,?_,rfl⟩
  · rw [su]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [smb]; exact List.mem_cons_self
private theorem v_path_m : Path reader 1 v merged := by
  refine ⟨merged,?_,rfl⟩
  rw [sv]; exact List.mem_cons_self

private theorem u_rows (row : EdgeValue Nat Bool) : Origin reader [u] row ↔ row = rowA ∨ row = rowB := by
  constructor
  · rintro ⟨last,reached,member⟩
    rcases u_reached last reached with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [nu] at member; cases member
    · rw [nma] at member; cases member
    · rw [nmb] at member; cases member
    · rw [nz] at member; cases member
    · rw [na] at member; exact Or.inl (List.mem_singleton.mp member)
    · rw [nb] at member; exact Or.inr (List.mem_singleton.mp member)
  · rintro (rfl | rfl)
    · exact ⟨a,u_path_a.reachable reader,by rw [na]; exact List.mem_cons_self⟩
    · exact ⟨b,u_path_b.reachable reader,by rw [nb]; exact List.mem_cons_self⟩

private theorem v_rows (row : EdgeValue Nat Bool) : Origin reader [v] row ↔ row = rowA ∨ row = rowB := by
  constructor
  · rintro ⟨last,reached,member⟩
    rcases v_reached last reached with rfl | rfl | rfl
    · rw [nv] at member; cases member
    · rw [nm] at member
      rcases List.mem_cons.mp member with present | present
      · exact Or.inl present
      · exact Or.inr (List.mem_singleton.mp present)
    · rw [nz] at member; cases member
  · rintro (rfl | rfl)
    · exact ⟨merged,v_path_m.reachable reader,by rw [nm]; exact List.mem_cons_self⟩
    · exact ⟨merged,v_path_m.reachable reader,by rw [nm]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩

private theorem same_all (depth : Nat) : Same depth reader [u] [v] :=
  SourceCurrentOpenObservations.of_origins depth reader [u] [v]
    (fun name => (u_reference name).trans (v_reference name).symm)
    (fun row => (u_rows row).trans (v_rows row).symm)

private theorem a_no_references (name : Reference) : ¬ ReferenceOrigin reader [a] name := by
  intro actual
  have expanded := SourceCurrentOpenObservations.reference_expand reader a
    (fun name same => not_ref a a_nonref name same.symm) name
  have impossible := expanded.mp actual
  rw [sa] at impossible
  obtain ⟨_,member,_⟩ := (SourceCurrentOpenObservations.reference_seeds reader [] name).mp impossible
  cases member

private theorem terminal_reached (first : Value Nat Bool) (terminal : successors reader first = [])
    (last : Value Nat Bool) (actual : Reachable (successors reader) [first] last) : last = first := by
  induction actual with
  | seed present => exact List.mem_singleton.mp present
  | step previous next ih => rw [ih,terminal] at next; cases next

private theorem a_rows (row : EdgeValue Nat Bool) : Origin reader [a] row ↔ row = rowA := by
  constructor
  · rintro ⟨last,reached,member⟩
    rw [terminal_reached a sa last reached,na] at member
    exact List.mem_singleton.mp member
  · intro same
    subst row
    exact ⟨a,.seed List.mem_cons_self,by rw [na]; exact List.mem_cons_self⟩
private theorem symbol_a : rowA.entry.key.symbol = 1 := by cbv
private theorem symbol_b : rowB.entry.key.symbol = 2 := by cbv
private theorem merged_row_b : Origin reader [merged] rowB :=
  ⟨merged,.seed List.mem_cons_self,by rw [nm]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩

private theorem no_two_way : ¬ ∃ relation : Value Nat Bool → Value Nat Bool → Prop,
    relation u v ∧ Forward reader relation ∧ Forward reader (fun right left => relation left right) := by
  rintro ⟨relation,paired,forward,backward⟩
  obtain ⟨later,reached,matched⟩ := forward.path reader relation paired u_path_a
  have observed := SourceCurrentOpenWeakSimulation.same reader relation forward backward 1 a later matched
  rcases v_reached later reached with rfl | rfl | rfl
  · exact a_no_references own ((observed.1 own).mpr ((v_reference own).mpr rfl))
  · obtain ⟨other,present,fields⟩ := observed.2.2 rowB merged_row_b
    have same := (a_rows other).mp present
    rw [same] at fields
    have impossible := fields.1
    rw [symbol_b,symbol_a] at impossible
    omega
  · exact a_no_references own ((observed.1 own).mpr (.seed List.mem_cons_self))

private def supportRelation (left right : List (Value Symbol Guard))
    (first second : Value Symbol Guard) (a b : Value Symbol Guard) : Prop :=
  a = b ∨ (a ∈ left ∧ b = second) ∨ (a ∈ right ∧ b = first)

private theorem finite_support_directed [DecidableEq (EdgeKey Symbol Guard)]
    (reader : State Symbol Guard) (left right : List (Value Symbol Guard))
    (first second : Value Symbol Guard)
    (leftClosed : ∀ value ∈ left, ∀ next ∈ successors reader value, next ∈ left)
    (rightClosed : ∀ value ∈ right, ∀ next ∈ successors reader value, next ∈ right)
    (leftReferences : ∀ value ∈ left, ∀ name : Reference,
      value = .reference name → ReferenceOrigin reader [second] name)
    (rightReferences : ∀ value ∈ right, ∀ name : Reference,
      value = .reference name → ReferenceOrigin reader [first] name)
    (leftRows : ∀ value ∈ left, ∀ row ∈ nodeEdges value, Origin reader [second] row)
    (rightRows : ∀ value ∈ right, ∀ row ∈ nodeEdges value, Origin reader [first] row) :
    Directed reader (supportRelation left right first second) := by
  let relation := supportRelation left right first second
  have identity (row : EdgeValue Symbol Guard) : RowMatch (Mutual relation) row row := by
    refine ⟨rfl,rfl,?_⟩
    induction row.children with
    | nil => exact .nil
    | cons head tail ih => exact .cons ⟨Or.inl rfl,Or.inl rfl⟩ ih
  intro a b paired
  rcases paired with rfl | ⟨member,rfl⟩ | ⟨member,rfl⟩
  · refine ⟨?_,?_,?_⟩
    · intro name same
      cases same
      exact .seed List.mem_cons_self
    · intro row member
      exact ⟨row,⟨a,.seed List.mem_cons_self,member⟩,identity row⟩
    · intro next member
      exact ⟨next,.step (.seed List.mem_cons_self) member,Or.inl rfl⟩
  · refine ⟨leftReferences a member,?_,?_⟩
    · intro row present
      exact ⟨row,leftRows a member row present,identity row⟩
    · intro next present
      exact ⟨b,.seed List.mem_cons_self,Or.inr (Or.inl ⟨leftClosed a member next present,rfl⟩)⟩
  · refine ⟨rightReferences a member,?_,?_⟩
    · intro row present
      exact ⟨row,rightRows a member row present,identity row⟩
    · intro next present
      exact ⟨b,.seed List.mem_cons_self,Or.inr (Or.inr ⟨rightClosed a member next present,rfl⟩)⟩


private def leftSupport : List (Value Nat Bool) := [u,muA,muB,z,a,b]
private def rightSupport : List (Value Nat Bool) := [v,merged,z]

private theorem left_reached (value : Value Nat Bool) :
    value ∈ leftSupport ↔ Reachable (successors reader) [u] value := by
  constructor
  · intro member
    simp only [leftSupport,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .seed List.mem_cons_self
    · exact .step (.seed List.mem_cons_self) (by rw [su]; exact List.mem_cons_self)
    · exact .step (.seed List.mem_cons_self) (by rw [su]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    · exact .step (.seed List.mem_cons_self)
        (by rw [su]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact u_path_a.reachable reader
    · exact u_path_b.reachable reader
  · intro actual
    simpa only [leftSupport,List.mem_cons,List.not_mem_nil,or_false] using u_reached value actual

private theorem right_reached (value : Value Nat Bool) :
    value ∈ rightSupport ↔ Reachable (successors reader) [v] value := by
  constructor
  · intro member
    simp only [rightSupport,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .seed List.mem_cons_self
    · exact v_path_m.reachable reader
    · exact .step (.seed List.mem_cons_self) (by rw [sv]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  · intro actual
    simpa only [rightSupport,List.mem_cons,List.not_mem_nil,or_false] using v_reached value actual

private theorem positive : ∃ relation : Value Nat Bool → Value Nat Bool → Prop,
    Directed reader relation ∧ Mutual relation u v := by
  refine ⟨supportRelation leftSupport rightSupport u v,
    finite_support_directed reader leftSupport rightSupport u v ?_ ?_ ?_ ?_ ?_ ?_,?_⟩
  · intro value member next selected
    exact (left_reached next).mpr (.step ((left_reached value).mp member) selected)
  · intro value member next selected
    exact (right_reached next).mpr (.step ((right_reached value).mp member) selected)
  · intro value member name same
    have actual := (left_reached value).mp member
    rw [same] at actual
    exact (v_reference name).mpr ((u_reference name).mp actual)
  · intro value member name same
    have actual := (right_reached value).mp member
    rw [same] at actual
    exact (u_reference name).mpr ((v_reference name).mp actual)
  · intro value member row selected
    exact (v_rows row).mpr ((u_rows row).mp ⟨value,(left_reached value).mp member,selected⟩)
  · intro value member row selected
    exact (u_rows row).mpr ((v_rows row).mp ⟨value,(right_reached value).mp member,selected⟩)
  · exact ⟨Or.inr (Or.inl ⟨by simp only [leftSupport,List.mem_cons_self],rfl⟩),
      Or.inr (Or.inr ⟨by simp only [rightSupport,List.mem_cons_self],rfl⟩)⟩

private theorem checked :
    build source [] empty = .done root reader ∧ Ready reader ∧ Available reader u ∧ Available reader v ∧
    run (makeUnion [muA,muB,z]) reader = (u,reader) ∧
    run (makeUnion [a,b]) reader = (merged,reader) ∧
    run (makeUnion [merged,z]) reader = (v,reader) ∧
    unfold muA reader = .done a reader ∧ unfold muB reader = .done b reader ∧
    (∀ depth, Same depth reader [u] [v]) ∧
    (∃ relation : Value Nat Bool → Value Nat Bool → Prop, Directed reader relation ∧ Mutual relation u v) ∧
    ¬ ∃ relation : Value Nat Bool → Value Nat Bool → Prop,
      relation u v ∧ Forward reader relation ∧ Forward reader (fun right left => relation left right) :=
  ⟨actual,ready,u_available,v_available,made_u,made_merged,made_v,unfolded_a,unfolded_b,same_all,positive,no_two_way⟩

/-- Actual canonical grouped unions agree at every finite depth but admit no old two-way simulation. -/
theorem witness :
    build source [] empty = .done root reader ∧ Ready reader ∧ Available reader u ∧ Available reader v ∧
    run (makeUnion [muA,muB,z]) reader = (u,reader) ∧
    run (makeUnion [a,b]) reader = (merged,reader) ∧
    run (makeUnion [merged,z]) reader = (v,reader) ∧
    unfold muA reader = .done a reader ∧ unfold muB reader = .done b reader ∧
    (∀ depth, Same depth reader [u] [v]) ∧
    (∃ relation : Value Nat Bool → Value Nat Bool → Prop, Directed reader relation ∧ Mutual relation u v) ∧
    ¬ ∃ relation : Value Nat Bool → Value Nat Bool → Prop,
      relation u v ∧ Forward reader relation ∧ Forward reader (fun right left => relation left right) := checked

end MicroCFTA.PreorderNormalizationReview

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.PreorderNormalizationReview.witness
#print MicroCFTA.PreorderNormalizationReview.witness
#print axioms MicroCFTA.PreorderNormalizationReview.witness
