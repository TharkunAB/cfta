import MicroCFTA.SourceCurrentBuildStructuralRowOrigins

/-!
# Open ordinary leaves from actual source child calls

An indexed leaf retains its canonical row, ordered child, and inner leaf
position. The same row retains its original source index and actual child
call. Source positions and canonical positions remain separate.
-/
namespace MicroCFTA.SourceCurrentOpenOrdinaryLeafSourceCalls
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open InternedStoredSubstitution (leaves manyLeaves edgeLeaves)
open InternedEdgeResidency (nodeEdges)

private theorem flat_lookup (f : α → List β) (values : List α) (index : Nat) (value : β)
    (found : (values.flatMap f)[index]? = some value) :
    ∃ outer selected inner,
      values[outer]? = some selected ∧ (f selected)[inner]? = some value ∧
      index = ((values.take outer).flatMap f).length + inner := by
  induction values generalizing index with
  | nil => simp only [List.flatMap_nil,List.getElem?_nil] at found; cases found
  | cons first rest ih =>
      simp only [List.flatMap_cons] at found
      by_cases short : index < (f first).length
      · rw [List.getElem?_append_left short] at found
        exact ⟨0,first,index,rfl,found,by simp only [List.take_zero,List.flatMap_nil,List.length_nil,Nat.zero_add]⟩
      · have long : (f first).length ≤ index := by omega
        rw [List.getElem?_append_right long] at found
        obtain ⟨outer,selected,inner,source,inside,offset⟩ := ih (index - (f first).length) found
        refine ⟨outer + 1,selected,inner,source,inside,?_⟩
        simp only [List.take_succ_cons,List.flatMap_cons,List.length_append]
        omega

private theorem many_flat (values : List (Value Symbol Guard)) :
    manyLeaves values = values.flatMap leaves := by
  induction values with
  | nil => simp only [manyLeaves,List.flatMap_nil]
  | cons first rest ih => simp only [manyLeaves,List.flatMap_cons,ih]

private theorem edges_flat (rows : List (EdgeValue Symbol Guard)) :
    edgeLeaves rows = rows.flatMap (fun row => manyLeaves row.children) := by
  induction rows with
  | nil => simp only [edgeLeaves,List.flatMap_nil]
  | cons row rest ih =>
      cases row
      simp only [edgeLeaves,EdgeValue.children,List.flatMap_cons,ih]

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
              obtain ⟨child,current,next,source,earlier,childContext,called,suffix⟩ :=
                ih middle middleContext rest tail index found
              refine ⟨child,current,next,source,?_,childContext,called,?_⟩
              · simp only [List.take_succ_cons,buildMany,one,Outcome.bind,earlier]
              · simpa only [List.drop_succ_cons,Nat.add_assoc] using suffix

/-- An indexed open-node leaf retains its canonical position and actual strict source-child call. -/
theorem node_leaf [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (EdgeSyntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (raw : Value Symbol Guard) (after : State Symbol Guard)
    (context : Context before inputs) (actual : build (.node expressions) inputs before = .done raw after)
    (opened : raw.free ≠ []) (leafIndex : Nat) (leaf : Value Symbol Guard)
    (found : (leaves raw)[leafIndex]? = some leaf) :
    ∃ outputIndex row childIndex child inner sourceIndex symbol guard children rows middle,
      ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
      ∃ childSyntax current next,
      (nodeEdges raw)[outputIndex]? = some row ∧ row.children[childIndex]? = some child ∧
      (leaves child)[inner]? = some leaf ∧
      leafIndex = (edgeLeaves ((nodeEdges raw).take outputIndex)).length +
        (manyLeaves (row.children.take childIndex)).length + inner ∧
      buildEdges expressions inputs before = .done rows middle ∧
      run (makeNode rows) middle = (raw,after) ∧ call.output = row ∧
      children[childIndex]? = some childSyntax ∧ call.values[childIndex]? = some child ∧
      buildMany (children.take childIndex) inputs call.current = .done (call.values.take childIndex) current ∧
      Context current inputs ∧ build childSyntax inputs current = .done child next ∧
      buildMany (children.drop (childIndex + 1)) inputs next = .done (call.values.drop (childIndex + 1)) call.middle ∧
      sizeOf childSyntax < sizeOf (Syntax.node expressions) := by
  have ordinary : raw = .empty ∨ ∃ entry edges depth free, raw = .node entry edges depth free := by
    cases built : buildEdges expressions inputs before with
    | pending key state => simp only [build,built,Outcome.bind] at actual; cases actual
    | done rows middle =>
      have made : run (makeNode rows) middle = (raw,after) :=
        Prod.ext (Outcome.done.inj (by simpa only [build,built,Outcome.bind,InternedNestedConstruction.work] using actual)).1
          (Outcome.done.inj (by simpa only [build,built,Outcome.bind,InternedNestedConstruction.work] using actual)).2
      have middleContext : Context middle inputs := by
        simpa only [built,Outcome.state] using context.edges expressions
      have resident := (InternedFreshOrdinaryFacts.buildEdges_verified expressions inputs before
        context.base.normal.facts context.base.inputs).result rows middle built
      have plain := SourceEqualityRequiredCache.node_ordinary rows middle middleContext.base.normal.facts resident
      rw [made] at plain
      cases raw with
      | empty => exact .inl rfl
      | node entry rows depth free => exact .inr ⟨entry,rows,depth,free,rfl⟩
      | reference | union | mu => cases plain
  have rawLeaves : leaves raw = edgeLeaves (nodeEdges raw) := by
    rcases ordinary with rfl | ⟨entry,rows,depth,free,rfl⟩
    · exact False.elim (opened rfl)
    · change free ≠ [] at opened
      rw [leaves.eq_def]
      simp only [Value.free,List.isEmpty_eq_false_iff.mpr opened,Bool.false_eq_true,↓reduceIte,nodeEdges]
  rw [rawLeaves,edges_flat] at found
  obtain ⟨outputIndex,row,rowInner,selected,inside,rowOffset⟩ :=
    flat_lookup (fun edge : EdgeValue Symbol Guard => manyLeaves edge.children) (nodeEdges raw) leafIndex leaf found
  rw [many_flat] at inside
  obtain ⟨childIndex,child,inner,childSelected,leafSelected,childOffset⟩ :=
    flat_lookup leaves row.children rowInner leaf inside
  have part : RowAt raw row := by
    cases raw with
    | node entry rows depth free => exact .node selected
    | empty | reference | union | mu => simp only [nodeEdges,List.getElem?_nil] at selected; cases selected
  have source := SourceCurrentBuildStructuralRowOrigins.build_row_origin
    (.node expressions) inputs before raw after context actual row part
  cases source with
  | @node rows middle symbol guard children sourceIndex _ built made _ call same =>
      have rowContext : Context call.current inputs := by
        have currentContext := context.edges (expressions.take sourceIndex)
        rw [call.earlier] at currentContext
        exact currentContext
      have childFound : call.values[childIndex]? = some child := by
        rw [← call.children_eq,same]
        exact childSelected
      obtain ⟨childSyntax,current,next,syntaxFound,earlier,childContext,called,suffix⟩ :=
        member_call _ inputs call.current call.middle rowContext call.values call.called childIndex child childFound
      have smaller : sizeOf childSyntax < sizeOf (Syntax.node expressions) := by
        have childSmall := List.sizeOf_lt_of_mem (List.mem_of_getElem? syntaxFound)
        have rowSmall := List.sizeOf_lt_of_mem (List.mem_of_getElem? call.source)
        simp only [Syntax.node.sizeOf_spec,EdgeSyntax.mk.sizeOf_spec] at *
        omega
      refine ⟨outputIndex,row,childIndex,child,inner,_,_,_,_,_,_,call,childSyntax,current,next,
        selected,childSelected,leafSelected,?_,built,made,same,syntaxFound,childFound,earlier,childContext,called,suffix,smaller⟩
      rw [edges_flat,many_flat]
      omega

end MicroCFTA.SourceCurrentOpenOrdinaryLeafSourceCalls
