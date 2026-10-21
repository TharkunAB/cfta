import MicroCFTA.SourceCurrentRequiredPositivePosition
import MicroCFTA.SourceCurrentNativeMuPublication
import MicroCFTA.InternedFreshOrdinaryFirstOrderHeap
import MicroCFTA.InternedUnionFilterFusion
import MicroCFTA.InternedStoredPlanBinderDepthExact
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Positive positions in an actual binder-free publication

The three callbacks retain one source body and one capture list. The body
contains no nested binder syntax. Captured Mu values remain opaque.
-/
namespace MicroCFTA.SourceCurrentBinderFreePublicationPositions
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedNestedProvenance (Values Edges)
open InternedNestedFacts (edge_verified)
open InternedEdgeResidency (nodeEdges EdgeResident)
open InternedStoredMuOrigins (Normal)
open InternedStoredShallowCompletion (BinderFree ManyBinderFree EdgesBinderFree)
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentNativeMuPublication (Publication)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard

private def RowsPositive (rows : List Row) : List Nat → Prop
  | [] => ∃ row ∈ rows, SourceMemoGate.plain row.entry.key.constraint = false
  | index :: rest => ∃ row ∈ rows, ∃ child, row.children[index]? = some child ∧ PositiveAt child rest

private theorem node_positive {entry rows depth free path} :
    PositiveAt (.node entry rows depth free) path ↔ RowsPositive rows path := by
  constructor
  · intro positive
    cases positive with
    | root index row selected nonplain => exact ⟨row,List.mem_of_getElem? selected,nonplain⟩
    | child index childIndex row child selected chosen rest => exact ⟨row,List.mem_of_getElem? selected,child,chosen,rest⟩
  · cases path with
    | nil =>
        rintro ⟨row,member,positive⟩
        obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
        exact .root index row selected positive
    | cons index path =>
        rintro ⟨row,member,child,chosen,positive⟩
        obtain ⟨rowIndex,selected⟩ := List.mem_iff_getElem?.mp member
        exact .child rowIndex index row child selected chosen positive

private theorem union_positive {entry members depth free path} :
    PositiveAt (.union entry members depth free) path ↔ ∃ child ∈ members, PositiveAt child path := by
  constructor
  · intro positive; cases positive with
    | member index child selected rest => exact ⟨child,List.mem_of_getElem? selected,rest⟩
  · rintro ⟨child,member,positive⟩
    obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
    exact .member index child selected positive

private theorem rows_members {first second : List Row}
    (same : ∀ row, row ∈ first ↔ row ∈ second) (path) :
    RowsPositive first path ↔ RowsPositive second path := by
  cases path <;> simp only [RowsPositive, same]

private theorem rows_append (first second : List Row) (path) :
    RowsPositive (first ++ second) path ↔ RowsPositive first path ∨ RowsPositive second path := by
  cases path <;> simp only [RowsPositive,List.mem_append]
  all_goals
    constructor
    · rintro ⟨row,member,rest⟩
      exact member.elim (fun own => Or.inl ⟨row,own,rest⟩) (fun later => Or.inr ⟨row,later,rest⟩)
    · rintro (⟨row,member,rest⟩ | ⟨row,member,rest⟩)
      · exact ⟨row,Or.inl member,rest⟩
      · exact ⟨row,Or.inr member,rest⟩

section Physical

private theorem makeNode_positive [DecidableEq (EdgeKey Symbol Guard)] (rows : List Row) (state : Heap) (normal : Normal state)
    (resident : Edges state rows) (path) :
    PositiveAt (run (makeNode rows) state).1 path ↔ RowsPositive (surviving rows) path := by
  have fields := EqualityLeafProjectionPhysical.makeNode_edges rows state normal.facts.coherent normal.facts.linked resident
  have kept : ∀ row ∈ surviving rows, EdgeResident state row :=
    fun row member => resident row (List.mem_filter.mp member).1
  have exactRows : RowsPositive (canonicalEdges (surviving rows)) path ↔ RowsPositive (surviving rows) path :=
    rows_members (fun row => ⟨canonicalEdges_member _ row,
      InternedEdgeResidency.canonicalEdges_retains state normal.facts.coherent _ row kept⟩) path
  have ordinary := SourceEqualityRequiredCache.node_ordinary rows state normal.facts resident
  generalize value : (run (makeNode rows) state).1 = result at fields ordinary ⊢
  cases result with
  | empty =>
      have noRows : canonicalEdges (surviving rows) = [] := fields.symm
      rw [← exactRows,noRows]
      cases path <;> simp [RowsPositive]
      all_goals intro impossible; cases impossible
  | node entry rows depth free =>
      change rows = canonicalEdges (surviving _) at fields
      rw [node_positive,fields]; exact exactRows
  | reference | union | mu => cases ordinary

private theorem ordinary_positive (inputs : List Node) (rows : List Row)
    (actual : ordinaryEdges inputs = some rows) (path) :
    RowsPositive rows path ↔ ∃ input ∈ inputs, PositiveAt input path := by
  induction inputs generalizing rows with
  | nil => cases actual; cases path <;> simp [RowsPositive]
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at actual <;> try contradiction
      case node entry own depth free =>
        cases later : ordinaryEdges rest with
        | none => simp [later] at actual
        | some outputs =>
            have same : own ++ outputs = rows := by simpa only [later,Option.map_some,Option.some.injEq] using actual
            subst rows
            rw [rows_append,ih outputs later]
            simp only [List.mem_cons,exists_eq_or_imp,node_positive]

private theorem flattened_positive (inputs : List Node) (path) :
    (∃ input ∈ inputs.flatMap unionMembers, PositiveAt input path) ↔
      ∃ input ∈ inputs, PositiveAt input path := by
  constructor
  · rintro ⟨input,present,positive⟩
    obtain ⟨source,member,selected⟩ := List.mem_flatMap.mp present
    cases source with
    | empty => cases selected
    | union entry members depth free => exact ⟨_,member,union_positive.mpr ⟨input,selected,positive⟩⟩
    | reference | node | mu =>
        have same := List.mem_singleton.mp selected
        exact ⟨_,member,same ▸ positive⟩
  · rintro ⟨input,member,positive⟩
    cases input with
    | empty | reference | mu => cases positive
    | node entry rows depth free => exact ⟨_,List.mem_flatMap.mpr ⟨_,member,List.mem_singleton_self _⟩,positive⟩
    | union entry members depth free =>
        obtain ⟨child,selected,positive⟩ := union_positive.mp positive
        exact ⟨child,List.mem_flatMap.mpr ⟨_,member,selected⟩,positive⟩

private theorem makeUnion_positive [DecidableEq (EdgeKey Symbol Guard)] (inputs : List Node) (state : Heap) (normal : Normal state)
    (available : Values state inputs) (path) :
    PositiveAt (run (makeUnion inputs) state).1 path ↔ ∃ input ∈ inputs, PositiveAt input path := by
  have flatAvailable : Values state (inputs.flatMap unionMembers) := by
    intro value member
    obtain ⟨input,present,selected⟩ := List.mem_flatMap.mp member
    exact unionMembers_available input (available input present) value selected
  have selectedPositive :
      (∃ input ∈ distinctNodes (inputs.flatMap unionMembers), PositiveAt input path) ↔
        ∃ input ∈ inputs, PositiveAt input path := by
    rw [← flattened_positive inputs path]
    constructor
    · rintro ⟨input,member,positive⟩; exact ⟨input,distinctNodes_member _ _ member,positive⟩
    · rintro ⟨input,member,positive⟩
      exact ⟨input,InternedUnionRetention.distinctNodes_retains state normal.facts.coherent _
        (fun value member => (flatAvailable value member).resident) input member,positive⟩
  rw [← selectedPositive]
  cases selected : distinctNodes (inputs.flatMap unionMembers) with
  | nil => simp only [makeUnion,selected,run,List.not_mem_nil,false_and,exists_false]
           constructor <;> (intro impossible; cases impossible)
  | cons first rest =>
      cases rest with
      | nil => simp only [makeUnion,selected,run,List.mem_singleton,exists_eq_left]
      | cons second tail =>
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | none =>
              obtain ⟨entry,readback⟩ := InternedUnionFilterFusion.union_readback inputs first second tail state
                normal.facts available selected ordinary
              rw [readback,union_positive]
          | some rows =>
              have inputsAvailable : Values state (first :: second :: tail) := by
                simpa only [selected] using InternedUnionFilterFusion.selected_available inputs state available
              have resident := InternedEdgeResidency.ordinaryEdges_resident _ rows state normal.facts.linked
                (fun value member => (inputsAvailable value member).resident) ordinary
              have live := InternedStoredPlanBinderDepth.ordinaryEdges_surviving _ rows state normal.live inputsAvailable ordinary
              simpa only [makeUnion,selected,ordinary] using
                (makeNode_positive rows state normal resident path).trans (by rw [live]; exact ordinary_positive _ rows ordinary path)

private theorem filter_positive [DecidableEq (EdgeKey Symbol Guard)] (name : InternedBinderProtocol.Reference) (value : Node) (state : Heap)
    (normal : Normal state) (available : Available state value) (path) :
    PositiveAt (run (withoutSelfReference name value) state).1 path ↔ PositiveAt value path := by
  cases value <;> simp only [withoutSelfReference,run] <;> try exact Iff.rfl
  case union entry members depth free =>
    split
    · have inputs : Values state (members.filter (fun member => member.referenceOf != .ref name)) :=
        fun value member => available.children value (List.mem_filter.mp member).1
      rw [makeUnion_positive _ state normal inputs,union_positive]
      constructor
      · rintro ⟨child,member,positive⟩; exact ⟨child,(List.mem_filter.mp member).1,positive⟩
      · rintro ⟨child,member,positive⟩
        refine ⟨child,List.mem_filter.mpr ⟨member,?_⟩,positive⟩
        simp only [bne_iff_ne]
        intro equal
        have same := (referenceOf_self_iff name child).mp equal
        subst child
        cases positive
    · exact Iff.rfl

end Physical


private def Same (first second : Node) : Prop :=
  (first.referenceOf == .empty) = (second.referenceOf == .empty) ∧
    ∀ path, PositiveAt first path ↔ PositiveAt second path

private def RowSame (first second : Row) : Prop :=
  first.entry.key.constraint = second.entry.key.constraint ∧ All₂ Same first.children second.children

private theorem all_symm {A : Type} {R : A → A → Prop} {first second}
    (symmetric : ∀ a b, R a b → R b a) (related : All₂ R first second) : All₂ R second first := by
  induction related with
  | nil => exact .nil
  | cons head rest ih => exact .cons (symmetric _ _ head) ih

private theorem same_symm {first second} (related : Same first second) : Same second first :=
  ⟨related.1.symm,fun path => (related.2 path).symm⟩

private theorem row_symm {first second} (related : RowSame first second) : RowSame second first :=
  ⟨related.1.symm,all_symm (fun _ _ => same_symm) related.2⟩

private theorem all_lookup {A B : Type} {R : A → B → Prop} {first second}
    (related : All₂ R first second) (index : Nat) (value : A) (found : first[index]? = some value) :
    ∃ result, second[index]? = some result ∧ R value result := by
  induction related generalizing index with
  | nil => cases found
  | cons head rest ih =>
      cases index with
      | zero => cases Option.some.inj found; exact ⟨_,rfl,head⟩
      | succ index => exact ih index found

private theorem all_forall {A B : Type} {R : A → B → Prop} {first second}
    (related : All₂ R first second) (P : A → Prop) (Q : B → Prop)
    (each : ∀ a b, R a b → (P a ↔ Q b)) :
    (∀ a ∈ first, P a) ↔ ∀ b ∈ second, Q b := by
  induction related with
  | nil => simp
  | cons head rest ih => simpa only [List.mem_cons,forall_eq_or_imp] using and_congr (each _ _ head) ih

private theorem all_exists {A B : Type} {R : A → B → Prop} {first second}
    (related : All₂ R first second) (P : A → Prop) (Q : B → Prop)
    (each : ∀ a b, R a b → (P a ↔ Q b)) :
    (∃ a ∈ first, P a) ↔ ∃ b ∈ second, Q b := by
  induction related with
  | nil => simp
  | cons head rest ih => simpa only [List.mem_cons,exists_eq_or_imp] using or_congr (each _ _ head) ih

private theorem dead_same {first second} (related : All₂ Same first second) :
    first.any (fun child => child.referenceOf == .empty) = second.any (fun child => child.referenceOf == .empty) := by
  induction related with
  | nil => rfl
  | cons head rest ih => simp only [List.any_cons,head.1,ih]

private theorem singleton_positive {first second} (related : RowSame first second) (path) :
    RowsPositive [first] path ↔ RowsPositive [second] path := by
  have direction : ∀ {first second}, RowSame first second → RowsPositive [first] path → RowsPositive [second] path := by
    intro first second same positive
    cases path with
    | nil =>
        obtain ⟨row,member,positive⟩ := positive
        have equal := List.mem_singleton.mp member
        subst row
        exact ⟨second,List.mem_singleton_self _,same.1 ▸ positive⟩
    | cons index path =>
        obtain ⟨row,member,child,selected,positive⟩ := positive
        have equal := List.mem_singleton.mp member
        subst row
        obtain ⟨result,found,matched⟩ := all_lookup same.2 index child selected
        exact ⟨second,List.mem_singleton_self _,result,found,(matched.2 path).mp positive⟩
  exact ⟨direction related,direction (row_symm related)⟩

private theorem surviving_positive {first second} (related : All₂ RowSame first second) (path) :
    RowsPositive (surviving first) path ↔ RowsPositive (surviving second) path := by
  induction related with
  | nil => exact Iff.rfl
  | @cons left right lefts rights head rest ih =>
      have dead := dead_same head.2
      simp only [surviving,List.filter_cons]
      rw [dead]
      split
      · change RowsPositive ([left] ++ surviving lefts) path ↔ RowsPositive ([right] ++ surviving rights) path
        rw [rows_append,rows_append]
        exact or_congr (singleton_positive head path) ih
      · exact ih

private theorem completed_bind {A B : Type} (first : Outcome Symbol Guard A)
    (next : A → Heap → Outcome Symbol Guard B) (value : B) (after : Heap)
    (actual : first.bind next = .done value after) :
    ∃ input middle, first = .done input middle ∧ next input middle = .done value after := by
  cases first with
  | pending key state => cases actual
  | done input middle => exact ⟨input,middle,rfl,actual⟩

private theorem all_refl (values : List Node) : All₂ Same values values := by
  induction values with
  | nil => exact .nil
  | cons first rest ih => exact .cons ⟨rfl,fun _ => Iff.rfl⟩ ih

private theorem getD_same {first second} (related : All₂ Same first second) (index : Nat) :
    Same (first[index]?.getD .empty) (second[index]?.getD .empty) := by
  induction related generalizing index with
  | nil => exact ⟨rfl,fun _ => Iff.rfl⟩
  | cons head rest ih => cases index with
    | zero => exact head
    | succ index => exact ih index

section Execution
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem node_same {first second} (related : All₂ RowSame first second)
    (left right : Heap) (ln : Normal left) (rn : Normal right) (la : Edges left first) (ra : Edges right second) :
    Same (run (makeNode first) left).1 (run (makeNode second) right).1 := by
  constructor
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rw [InternedEmptyNormalization.makeNode_empty_iff first left ln.facts.coherent ln.facts.linked la,
      InternedEmptyNormalization.makeNode_empty_iff second right rn.facts.coherent rn.facts.linked ra]
    exact all_forall related _ _ (fun _ _ same => by rw [dead_same same.2])
  · intro path
    exact (makeNode_positive first left ln la path).trans
      ((surviving_positive related path).trans (makeNode_positive second right rn ra path).symm)

private theorem union_same {first second} (related : All₂ Same first second)
    (left right : Heap) (ln : Normal left) (rn : Normal right) (la : Values left first) (ra : Values right second) :
    Same (run (makeUnion first) left).1 (run (makeUnion second) right).1 := by
  constructor
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rw [InternedEmptyNormalization.makeUnion_empty_iff first left ln.facts.coherent ln.facts.linked ln.live ln.proper la,
      InternedEmptyNormalization.makeUnion_empty_iff second right rn.facts.coherent rn.facts.linked rn.live rn.proper ra]
    exact all_forall related _ _ (fun _ _ same => by simpa only [beq_iff_eq] using Bool.eq_iff_iff.mp same.1)
  · intro path
    rw [makeUnion_positive first left ln la path,makeUnion_positive second right rn ra path]
    exact all_exists related _ _ (fun _ _ same => same.2 path)

private theorem edge_guard (symbol : Symbol) (guard : Guard) (values : List Node) (state : Heap)
    (normal : Normal state) : (run (makeEdge symbol guard values) state).1.entry.key.constraint = guard := by
  let key : EdgeKey Symbol Guard := ⟨symbol,values.map Value.referenceOf,guard⟩
  have correct := edgeStep_correct key (fun entry => .mk entry values) state normal.facts.coherent.valid
  have coherent := edgeStep_coherent key (fun entry => .mk entry values) state normal.facts.coherent
    (fun _ found => ⟨rfl,found,rfl⟩)
  exact congrArg EdgeKey.constraint (coherent.edges key _ correct.2.2).2.1


mutual
private theorem build_same (expression : Syntax Symbol Guard) (free : BinderFree expression)
    (first second : List Node) (paired : All₂ Same first second) (left right : Heap)
    (ln : Normal left) (rn : Normal right) (la : Values left first) (ra : Values right second)
    (output result : Node) (after final : Heap)
    (ld : build expression first left = .done output after) (rd : build expression second right = .done result final) :
    Same output result := by
  cases expression with
  | empty => rw [build] at ld rd; cases ld; cases rd; exact ⟨rfl,fun _ => Iff.rfl⟩
  | var index =>
      simp only [build,Outcome.done.injEq] at ld rd
      rw [← ld.1,← rd.1]
      exact getD_same paired index
  | binder => simp only [BinderFree] at free
  | node edges =>
      simp only [BinderFree] at free
      rw [build] at ld rd
      obtain ⟨leftRows,middle,lrows,lmade⟩ := completed_bind _ _ _ _ ld
      obtain ⟨rightRows,current,rrows,rmade⟩ := completed_bind _ _ _ _ rd
      have related := edges_same edges free first second paired left right ln rn la ra _ _ _ _ lrows rrows
      have lv := buildEdges_verified edges first left ln.facts la
      have rv := buildEdges_verified edges second right rn.facts ra
      have mn : Normal middle := by simpa only [lrows,Outcome.state] using InternedFreshOrdinaryNormal.buildEdges_normal edges first left ln la
      have cn : Normal current := by simpa only [rrows,Outcome.state] using InternedFreshOrdinaryNormal.buildEdges_normal edges second right rn ra
      have same := node_same related middle current mn cn (lv.result _ _ lrows) (rv.result _ _ rrows)
      exact (Outcome.done.inj lmade).1 ▸ ((Outcome.done.inj rmade).1 ▸ same)
  | union members =>
      simp only [BinderFree] at free
      rw [build] at ld rd
      obtain ⟨leftValues,middle,lvalues,lmade⟩ := completed_bind _ _ _ _ ld
      obtain ⟨rightValues,current,rvalues,rmade⟩ := completed_bind _ _ _ _ rd
      have related := many_same members free first second paired left right ln rn la ra _ _ _ _ lvalues rvalues
      have lv := buildMany_verified members first left ln.facts la
      have rv := buildMany_verified members second right rn.facts ra
      have mn : Normal middle := by simpa only [lvalues,Outcome.state] using InternedFreshOrdinaryNormal.buildMany_normal members first left ln la
      have cn : Normal current := by simpa only [rvalues,Outcome.state] using InternedFreshOrdinaryNormal.buildMany_normal members second right rn ra
      have same := union_same related middle current mn cn (lv.result _ _ lvalues) (rv.result _ _ rvalues)
      exact (Outcome.done.inj lmade).1 ▸ ((Outcome.done.inj rmade).1 ▸ same)
termination_by sizeOf expression

private theorem many_same (expressions : List (Syntax Symbol Guard)) (free : ManyBinderFree expressions)
    (first second : List Node) (paired : All₂ Same first second) (left right : Heap)
    (ln : Normal left) (rn : Normal right) (la : Values left first) (ra : Values right second)
    (outputs results : List Node) (after final : Heap)
    (ld : buildMany expressions first left = .done outputs after) (rd : buildMany expressions second right = .done results final) :
    All₂ Same outputs results := by
  cases expressions with
  | nil => rw [buildMany] at ld rd; cases ld; cases rd; exact .nil
  | cons head rest =>
      simp only [ManyBinderFree] at free
      rw [buildMany] at ld rd
      obtain ⟨lv,middle,lhead,ltail⟩ := completed_bind _ _ _ _ ld
      obtain ⟨rv,current,rhead,rtail⟩ := completed_bind _ _ _ _ rd
      obtain ⟨lvs,afterTail,lrest,lreturn⟩ := completed_bind _ _ _ _ ltail
      obtain ⟨rvs,finalTail,rrest,rreturn⟩ := completed_bind _ _ _ _ rtail
      cases lreturn; cases rreturn
      have lcheck := build_verified head first left ln.facts la
      have rcheck := build_verified head second right rn.facts ra
      exact .cons (build_same head free.1 first second paired left right ln rn la ra _ _ _ _ lhead rhead)
        (many_same rest free.2 first second paired middle current
          (by simpa only [lhead,Outcome.state] using InternedFreshOrdinaryNormal.build_normal head first left ln la)
          (by simpa only [rhead,Outcome.state] using InternedFreshOrdinaryNormal.build_normal head second right rn ra)
          (fun value member => by simpa only [lhead,Outcome.state] using lcheck.available value (la value member))
          (fun value member => by simpa only [rhead,Outcome.state] using rcheck.available value (ra value member))
          _ _ _ _ lrest rrest)
termination_by sizeOf expressions

private theorem edges_same (expressions : List (EdgeSyntax Symbol Guard)) (free : EdgesBinderFree expressions)
    (first second : List Node) (paired : All₂ Same first second) (left right : Heap)
    (ln : Normal left) (rn : Normal right) (la : Values left first) (ra : Values right second)
    (outputs results : List Row) (after final : Heap)
    (ld : buildEdges expressions first left = .done outputs after) (rd : buildEdges expressions second right = .done results final) :
    All₂ RowSame outputs results := by
  cases expressions with
  | nil => rw [buildEdges] at ld rd; cases ld; cases rd; exact .nil
  | cons head rest =>
      cases head with
      | mk symbol guard children =>
          simp only [EdgesBinderFree] at free
          rw [buildEdges] at ld rd
          obtain ⟨lvs,middle,lchildren,ledge⟩ := completed_bind _ _ _ _ ld
          obtain ⟨rvs,current,rchildren,redge⟩ := completed_bind _ _ _ _ rd
          obtain ⟨le,afterEdge,lmade,ltail⟩ := completed_bind _ _ _ _ ledge
          obtain ⟨re,afterOther,rmade,rtail⟩ := completed_bind _ _ _ _ redge
          obtain ⟨les,afterTail,lrest,lreturn⟩ := completed_bind _ _ _ _ ltail
          obtain ⟨res,finalTail,rrest,rreturn⟩ := completed_bind _ _ _ _ rtail
          cases lreturn; cases rreturn
          have lcheck := buildMany_verified children first left ln.facts la
          have rcheck := buildMany_verified children second right rn.facts ra
          have mn : Normal middle := by simpa only [lchildren,Outcome.state] using InternedFreshOrdinaryNormal.buildMany_normal children first left ln la
          have cn : Normal current := by simpa only [rchildren,Outcome.state] using InternedFreshOrdinaryNormal.buildMany_normal children second right rn ra
          have lav := lcheck.result _ _ lchildren
          have rav := rcheck.result _ _ rchildren
          have leftEdge := edge_verified symbol guard lvs middle mn.facts lav
          have rightEdge := edge_verified symbol guard rvs current cn.facts rav
          have leftEqual := Outcome.done.inj lmade
          have rightEqual := Outcome.done.inj rmade
          have row : RowSame le re := by
            rw [← leftEqual.1,← rightEqual.1]
            constructor
            · exact (edge_guard symbol guard lvs middle mn).trans (edge_guard symbol guard rvs current cn).symm
            · rw [InternedShallowValues.makeEdge_children symbol guard lvs middle mn.facts.coherent mn.facts.cached lav,
                InternedShallowValues.makeEdge_children symbol guard rvs current cn.facts.coherent cn.facts.cached rav]
              exact many_same children free.1 first second paired left right ln rn la ra _ _ _ _ lchildren rchildren
          have an : Normal afterEdge := by
            rw [← leftEqual.2]
            exact InternedNestedMuOrigins.edge_normal symbol guard lvs middle mn lav
          have bn : Normal afterOther := by
            rw [← rightEqual.2]
            exact InternedNestedMuOrigins.edge_normal symbol guard rvs current cn rav
          exact .cons row (edges_same rest free.2 first second paired afterEdge afterOther an bn
            (fun value member => by
              have available : Available middle value := by simpa only [lchildren,Outcome.state] using lcheck.available value (la value member)
              simpa only [← leftEqual.2] using leftEdge.available value available)
            (fun value member => by
              have available : Available current value := by simpa only [rchildren,Outcome.state] using rcheck.available value (ra value member)
              simpa only [← rightEqual.2] using rightEdge.available value available)
            _ _ _ _ lrest rrest)
termination_by sizeOf expressions
end

private theorem callback_positions (expression : Syntax Symbol Guard) (free : BinderFree expression)
    (environment : List Node) (firstName secondName : InternedBinderProtocol.Reference)
    (left right : Heap) (ln : Normal left) (rn : Normal right)
    (la : Values left (.reference firstName :: environment)) (ra : Values right (.reference secondName :: environment))
    (output result : Node) (after final : Heap)
    (ld : callback expression environment firstName left = .done output after)
    (rd : callback expression environment secondName right = .done result final) :
    ∀ path, PositiveAt output path ↔ PositiveAt result path := by
  unfold callback at ld rd
  obtain ⟨lv,middle,lbuild,lmade⟩ := completed_bind _ _ _ _ ld
  obtain ⟨rv,current,rbuild,rmade⟩ := completed_bind _ _ _ _ rd
  have fixed := all_refl environment
  have arguments : Same (.reference firstName) (.reference secondName) := by
    refine ⟨rfl,?_⟩
    intro path
    constructor <;> (intro impossible; cases impossible)
  have related := build_same expression free _ _ (.cons arguments fixed) left right ln rn la ra _ _ _ _ lbuild rbuild
  have lcheck := build_verified expression _ left ln.facts la
  have rcheck := build_verified expression _ right rn.facts ra
  have mn : Normal middle := by simpa only [lbuild,Outcome.state] using InternedFreshOrdinaryNormal.build_normal expression _ left ln la
  have cn : Normal current := by simpa only [rbuild,Outcome.state] using InternedFreshOrdinaryNormal.build_normal expression _ right rn ra
  intro path
  rw [← (Outcome.done.inj lmade).1,← (Outcome.done.inj rmade).1]
  exact (filter_positive firstName lv middle mn (lcheck.result _ _ lbuild) path).trans
    ((related.2 path).trans (filter_positive secondName rv current cn (rcheck.result _ _ rbuild) path).symm)

/-- One actual binder-free publication retains every positive path in its ordinary probe. -/
theorem publication (event : @Publication Symbol Guard _)
    (firstOrder : BinderFree event.expression) (path : List Nat) :
    PositiveAt event.body path ↔ PositiveAt event.ordinary path := by
  have first : InternedFreshOrdinaryContext.Context event.afterDepth event.environment := by
    simpa only [event.depthDone,Outcome.state] using
      event.context.base.callback event.expression .depth (InternedNestedProvenance.depth_available event.before)
  have cut : InternedFreshOrdinaryContext.Context event.cut event.environment := by
    simpa only [event.ordinaryDone,Outcome.state] using
      first.callback event.expression (.uninterned (ordinaryLevel event.depth))
        (InternedNestedProvenance.ordinary_available event.afterDepth (ordinaryLevel event.depth))
  have allocated := cut.reserve event.key
  have own := (InternedConstructionProvenance.reserve_available event.key event.cut cut.normal.facts.coherent cut.normal.facts.cached).2
  exact callback_positions event.expression firstOrder event.environment _ _ event.allocated event.afterDepth
    allocated.normal first.normal (allocated.local _ own).inputs
    (first.local _ (InternedNestedProvenance.ordinary_available event.afterDepth (ordinaryLevel event.depth))).inputs
    event.body event.ordinary event.afterBody event.cut event.bodyDone event.ordinaryDone path

end Execution
end MicroCFTA.SourceCurrentBinderFreePublicationPositions
