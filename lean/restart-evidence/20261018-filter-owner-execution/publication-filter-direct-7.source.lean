import MicroCFTA.SourceCurrentNativePublicationNodeAlignment
import MicroCFTA.SourceCurrentLiteralFilterParts
import MicroCFTA.SourceCurrentNativeCallbackErasure
import MicroCFTA.InternedFilterSelfReference

/-!
# Actual source filtering along the root union spine

The source transformation removes the local variable only at the root
and through root unions. Ordinary children and captured records stay
unchanged. Exact literal atoms and rows account for union regrouping.
-/
namespace MicroCFTA.SourceCurrentPublicationFilterSource
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedStoredShallowCompletion (BinderFree ManyBinderFree)
open SourceCurrentLiteralRootParts (Literal Row SameParts)
open SourceCurrentNativeCallbackErasure (eraseSelf)
open InternedBinderProtocol (Reference)
open Language

/-- Remove the supplied local only along the root union spine. -/
def rootErase (expression : Syntax Symbol Guard) : Syntax Symbol Guard :=
  match expression with
  | .var 0 => .empty
  | .union members => .union (members.map rootErase)
  | other => other
termination_by sizeOf expression

private def RootFresh (expression : Syntax Symbol Guard) (captures : List (Value Symbol Guard))
    (own : Reference) : Prop :=
  match expression with
  | .var (index + 1) => own ∉ (captures[index]?.getD .empty).free
  | .union members => ∀ child ∈ members, RootFresh child captures own
  | _ => True
termination_by sizeOf expression

private theorem support_fresh (expression : Syntax Symbol Guard) (captures : List (Value Symbol Guard))
    (own : Reference)
    (fresh : own ∉ InternedFreeNameSemantics.evaluate (.binder true expression)
      (captures.map InternedRootProfile.profile) (captures.map Value.free)) :
    RootFresh expression captures own := by
  cases expression with
  | empty | node | binder => simp only [RootFresh]
  | var index =>
      cases index with
      | zero => simp only [RootFresh]
      | succ index =>
          rw [RootFresh]
          cases found : captures[index]? with
          | none => simp only [Option.getD_none,Value.free,List.not_mem_nil,not_false_eq_true]
          | some value =>
              simpa [InternedFreeNameSemantics.evaluate,InternedFreeNameSemantics.lower,
                List.getElem?_map,found,List.map_map,Function.comp_def] using fresh
  | union members =>
      rw [RootFresh]
      intro child member
      apply support_fresh child captures own
      intro present
      apply fresh
      rw [InternedFreeNameSemantics.evaluate, InternedFreeNameSemantics.lower_member] at present ⊢
      rw [InternedFreeNameSemantics.evaluate]
      exact (InternedFreeNameSemantics.evaluateMany_member _ _ _ _).mpr ⟨child,member,present⟩
termination_by sizeOf expression

private theorem erased_row (own : Reference) (value : Value Symbol Guard) (row : EdgeValue Symbol Guard) :
    Row (eraseSelf own value) row ↔ Row value row := by
  cases value with
  | empty | node | union | mu => rfl
  | reference other =>
      unfold eraseSelf
      split <;> constructor <;> intro impossible <;> cases impossible

private theorem erased_literal (own : Reference) (value atom : Value Symbol Guard)
    (notBare : value ≠ .reference own) : Literal (eraseSelf own value) atom ↔ Literal value atom := by
  have different : value.referenceOf ≠ .ref own := fun same => notBare ((referenceOf_self_iff own value).mp same)
  simp only [eraseSelf,different,↓reduceIte]

/-- Filtering and bare-self erasure remove exactly the selected literal atom. -/
theorem filtered_literal [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (normal : InternedStoredMuOrigins.Normal state)
    (own : Reference) (value : Value Symbol Guard) (available : Available state value)
    (atom : Value Symbol Guard) :
    Literal (eraseSelf own (run (withoutSelfReference own value) state).1) atom ↔
      Literal value atom ∧ atom ≠ .reference own := by
  by_cases bare : value = .reference own
  · subst value
    simp only [withoutSelfReference,run,eraseSelf,Value.referenceOf,↓reduceIte]
    constructor
    · intro impossible; cases impossible
    · rintro ⟨part,different⟩
      cases part
      exact False.elim (different rfl)
  · have notBare : (run (withoutSelfReference own value) state).1 ≠ .reference own :=
      fun same => bare ((InternedFilterSelfReference.filter_self_iff own value state
        normal.facts.coherent normal.flat available).mp same)
    rw [erased_literal own _ atom notBare,
      SourceCurrentLiteralFilterParts.literal state normal own value available atom]
    simp only [bare,false_or]

/-- Filtering and bare-self erasure preserve every exact ordinary row. -/
theorem filtered_row [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (normal : InternedStoredMuOrigins.Normal state)
    (own : Reference) (value : Value Symbol Guard) (available : Available state value)
    (row : EdgeValue Symbol Guard) :
    Row (eraseSelf own (run (withoutSelfReference own value) state).1) row ↔ Row value row := by
  rw [erased_row]
  exact SourceCurrentLiteralFilterParts.row state normal own value available row

private theorem many_free (expressions : List (Syntax Symbol Guard)) (free : ManyBinderFree expressions)
    (child : Syntax Symbol Guard) (member : child ∈ expressions) : BinderFree child := by
  induction expressions with
  | nil => cases member
  | cons expression rest ih =>
      simp only [ManyBinderFree] at free
      rcases List.mem_cons.mp member with rfl | later
      · exact free.1
      · exact ih free.2 later

/-- Root erasure preserves the static absence of source binders. -/
theorem rootErase_binder_free (expression : Syntax Symbol Guard) (free : BinderFree expression) :
    BinderFree (rootErase expression) := by
  cases expression with
  | empty | node => simpa only [rootErase] using free
  | var index => cases index <;> simp only [rootErase,BinderFree]
  | binder => simp only [BinderFree] at free
  | union members =>
      rw [rootErase,BinderFree]
      have every : ∀ child ∈ members, BinderFree (rootErase child) := by
        intro child member
        exact rootErase_binder_free child (many_free members (by simpa only [BinderFree] using free) child member)
      clear free
      induction members with
      | nil => simp only [List.map_nil,ManyBinderFree]
      | cons child rest ih =>
          rw [List.map_cons,ManyBinderFree]
          exact ⟨every child List.mem_cons_self,
            ih (fun item included => every item (List.mem_cons_of_mem _ included))⟩
termination_by sizeOf expression


private theorem source_children [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (common : State Symbol Guard) (valid : Valid common)
    (outputs : List (Value Symbol Guard))
    (actual : buildMany expressions inputs common = .done outputs common) :
    All₂ (fun expression output => build expression inputs common = .done output common) expressions outputs := by
  induction expressions generalizing outputs with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at actual
      obtain ⟨rfl,_⟩ := actual
      exact .nil
  | cons expression rest ih =>
      cases called : build expression inputs common with
      | pending key state => simp only [buildMany,called,Outcome.bind] at actual; cases actual
      | done output middle =>
          cases tail : buildMany rest inputs middle with
          | pending key state => simp only [buildMany,called,tail,Outcome.bind] at actual; cases actual
          | done remaining final =>
              simp only [buildMany,called,tail,Outcome.bind,Outcome.done.injEq] at actual
              obtain ⟨rfl,sameHeap⟩ := actual
              rw [sameHeap] at tail
              have middleValid : Valid middle := by
                simpa only [called,Outcome.state] using
                  (InternedFreshOrdinaryGrowth.build_correct expression inputs common valid).1
              have growth : Grows middle common := by
                simpa only [tail,Outcome.state] using
                  (InternedFreshOrdinaryGrowth.buildMany_correct rest inputs middle middleValid).2
              have head := InternedFreshOrdinaryReplay.build_replay expression inputs common common output middle valid called growth
              have rest := InternedFreshOrdinaryReplay.buildMany_replays rest inputs middle common remaining common
                middleValid tail (grows_refl _)
              exact .cons head (ih remaining rest)

private theorem raw_parts [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (common : State Symbol Guard) (context : Context common inputs) (result : Value Symbol Guard)
    (actual : build (.union expressions) inputs common = .done result common) :
    ∃ values, buildMany expressions inputs common = .done values common ∧
      Values common values ∧ run (makeUnion values) common = (result,common) := by
  cases called : buildMany expressions inputs common with
  | pending key state => simp only [build,called,Outcome.bind] at actual; cases actual
  | done values middle =>
      have made : run (makeUnion values) middle = (result,common) :=
        Prod.ext (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).1
          (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).2
      have checked := InternedFreshOrdinaryFacts.buildMany_verified expressions inputs common context.normal.facts context.inputs
      have middleFacts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
      have growth : Grows middle common := by
        simpa only [made] using (run_correct (makeUnion values) middle middleFacts.coherent.valid).2
      have repeated := InternedConstructorTemplates.replay (makeUnion values) middle common middleFacts.coherent.valid
        (by rw [made]; exact grows_refl _)
      rw [made] at repeated
      have warm := InternedFreshOrdinaryReplay.buildMany_replays expressions inputs common common values middle
        context.normal.facts.coherent.valid called growth
      have available := (InternedFreshOrdinaryFacts.buildMany_verified expressions inputs common
        context.normal.facts context.inputs).result values common warm
      exact ⟨values,by simpa only [called] using warm,available,repeated⟩


private theorem node_result [DecidableEq (EdgeKey Symbol Guard)]
    (rows : List (EdgeSyntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context before inputs) (value : Value Symbol Guard)
    (actual : build (.node rows) inputs before = .done value after) : SourceEqualityRequiredCache.Ordinary value := by
  cases called : buildEdges rows inputs before with
  | pending key current => simp only [build,called,Outcome.bind] at actual; cases actual
  | done edges middle =>
      have made : run (makeNode edges) middle = (value,after) :=
        Prod.ext (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).1
          (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).2
      have checked := InternedFreshOrdinaryFacts.buildEdges_verified rows inputs before context.normal.facts context.inputs
      have facts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
      simpa only [made] using SourceEqualityRequiredCache.node_ordinary edges middle facts (checked.result edges middle called)


private theorem literal_free (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value) (own : Reference)
    (part : Literal value (.reference own)) : own ∈ value.free := by
  cases value with
  | reference other => cases part; simp only [Value.free,List.mem_singleton]
  | empty | node | mu => cases part
  | union entry members level free =>
      obtain ⟨child,member,found⟩ := (SourceCurrentLiteralRootParts.literal_union entry members level free _).mp part
      have present := literal_free state coherent child (available.children child member) own found
      rw [Value.free,InternedNormalizationFree.union_free state coherent entry members level free available.resident]
      exact (childFree_member members own).mpr ⟨child,member,present⟩
termination_by sizeOf value


private theorem unchanged_parts (own : Reference) (value : Value Symbol Guard)
    (missing : ¬ Literal value (.reference own)) :
    (∀ atom, Literal value atom ↔ Literal value atom ∧ atom ≠ .reference own) ∧
      ∀ row, Row value row ↔ Row value row := by
  refine ⟨?_,fun _ => Iff.rfl⟩
  intro atom
  constructor
  · intro part
    exact ⟨part,fun same => missing (same ▸ part)⟩
  · exact And.left

private theorem list_parts (own : Reference) (first second : List (Value Symbol Guard))
    (paired : All₂ (fun raw erased =>
      (∀ atom, Literal erased atom ↔ Literal raw atom ∧ atom ≠ .reference own) ∧
      ∀ row, Row erased row ↔ Row raw row) first second) :
    (∀ atom, (∃ erased ∈ second, Literal erased atom) ↔
      (∃ raw ∈ first, Literal raw atom) ∧ atom ≠ .reference own) ∧
    ∀ row, (∃ erased ∈ second, Row erased row) ↔ ∃ raw ∈ first, Row raw row := by
  induction paired with
  | nil => simp only [List.not_mem_nil,exists_false,false_and,iff_self,implies_true,and_self]
  | @cons raw erased rest remaining head tail ih =>
      constructor
      · intro atom
        simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left,head.1 atom,ih.1 atom]
      · intro row
        simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left,head.2 row,ih.2 row]

private theorem stripped_source [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (free : BinderFree expression)
    (captures : List (Value Symbol Guard)) (own : Reference) (fresh : RootFresh expression captures own)
    (common : State Symbol Guard) (context : Context common (.reference own :: captures))
    (raw erased : Value Symbol Guard)
    (actual : build expression (.reference own :: captures) common = .done raw common)
    (changed : build (rootErase expression) (.reference own :: captures) common = .done erased common) :
    (∀ atom, Literal erased atom ↔ Literal raw atom ∧ atom ≠ .reference own) ∧
      ∀ row, Row erased row ↔ Row raw row := by
  cases expression with
  | empty =>
      simp only [rootErase,build,Outcome.done.injEq] at actual changed
      obtain ⟨rfl,_⟩ := actual
      obtain ⟨rfl,_⟩ := changed
      exact unchanged_parts own .empty (by intro impossible; cases impossible)
  | var index =>
      cases index with
      | zero =>
          simp only [rootErase,build,List.getElem?_cons_zero,Option.getD_some,Outcome.done.injEq] at actual changed
          obtain ⟨rfl,_⟩ := actual
          obtain ⟨rfl,_⟩ := changed
          constructor
          · intro atom
            constructor
            · intro impossible; cases impossible
            · rintro ⟨part,different⟩
              cases part
              exact False.elim (different rfl)
          · intro row
            constructor <;> intro impossible <;> cases impossible
      | succ index =>
          simp only [rootErase,build,List.getElem?_cons_succ,Outcome.done.injEq] at actual changed
          obtain ⟨rfl,_⟩ := actual
          obtain ⟨rfl,_⟩ := changed
          apply unchanged_parts own _
          intro present
          rw [RootFresh] at fresh
          apply fresh
          apply literal_free common context.normal.facts.coherent _ ?_ own present
          cases found : captures[index]? with
          | none => exact InternedProbeProvenance.empty_available common
          | some value =>
              simp only [Option.getD_some]
              exact context.inputs value (List.mem_cons_of_mem _ (List.mem_of_getElem? found))
  | node rows =>
      have ordinary := node_result rows _ common common context raw actual
      simp only [rootErase] at changed
      have same := Outcome.done.inj (actual.symm.trans changed)
      cases same.1
      apply unchanged_parts own raw
      intro impossible
      cases raw <;> try exact False.elim ordinary
      all_goals cases impossible
  | binder smart body => simp only [BinderFree] at free
  | union members =>
      simp only [rootErase] at changed
      obtain ⟨raws,rawMany,rawAvailable,rawMade⟩ := raw_parts members _ common context raw actual
      obtain ⟨eraseds,erasedMany,erasedAvailable,erasedMade⟩ := raw_parts (members.map rootErase) _ common context erased changed
      have firstCalls := source_children members _ common context.normal.facts.coherent.valid raws rawMany
      have secondCalls := source_children (members.map rootErase) _ common context.normal.facts.coherent.valid eraseds erasedMany
      have children : ∀ child ∈ members, ∀ first second,
          build child (.reference own :: captures) common = .done first common →
          build (rootErase child) (.reference own :: captures) common = .done second common →
          (∀ atom, Literal second atom ↔ Literal first atom ∧ atom ≠ .reference own) ∧
            ∀ row, Row second row ↔ Row first row := by
        intro child member first second firstDone secondDone
        exact stripped_source child (many_free members (by simpa only [BinderFree] using free) child member)
          captures own (by rw [RootFresh] at fresh; exact fresh child member)
          common context first second firstDone secondDone
      have paired : All₂ (fun first second =>
          (∀ atom, Literal second atom ↔ Literal first atom ∧ atom ≠ .reference own) ∧
            ∀ row, Row second row ↔ Row first row) raws eraseds := by
        clear rawMany erasedMany rawAvailable erasedAvailable rawMade erasedMade actual changed free fresh
        induction firstCalls generalizing eraseds with
        | nil => cases secondCalls; exact .nil
        | @cons child first rest values head tail ih =>
            rw [List.map_cons] at secondCalls
            cases secondCalls with
            | cons secondHead secondTail =>
                exact .cons (children child List.mem_cons_self _ _ head secondHead)
                  (ih _ secondTail (fun expression included => children expression (List.mem_cons_of_mem _ included)))
      obtain ⟨atoms,rows⟩ := list_parts own raws eraseds paired
      constructor
      · intro atom
        have left := SourceCurrentLiteralUnionParts.literal common context.normal.facts eraseds erasedAvailable atom
        have right := SourceCurrentLiteralUnionParts.literal common context.normal.facts raws rawAvailable atom
        rw [erasedMade] at left
        rw [rawMade] at right
        exact left.trans ((atoms atom).trans (and_congr right.symm Iff.rfl))
      · intro row
        have left := SourceCurrentLiteralUnionParts.row common context.normal.facts context.normal.live eraseds erasedAvailable row
        have right := SourceCurrentLiteralUnionParts.row common context.normal.facts context.normal.live raws rawAvailable row
        rw [erasedMade] at left
        rw [rawMade] at right
        exact left.trans ((rows row).trans right.symm)
termination_by sizeOf expression

/-- Actual source calls determine the exact parts after filtering and bare-self erasure. -/
theorem source_parts [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (free : BinderFree expression)
    (captures : List (Value Symbol Guard)) (own : Reference)
    (fresh : own ∉ InternedFreeNameSemantics.evaluate (.binder true expression)
      (captures.map InternedRootProfile.profile) (captures.map Value.free))
    (common : State Symbol Guard) (context : Context common (.reference own :: captures))
    (raw erased : Value Symbol Guard)
    (actual : build expression (.reference own :: captures) common = .done raw common)
    (changed : build (rootErase expression) (.reference own :: captures) common = .done erased common) :
    SameParts (eraseSelf own (run (withoutSelfReference own raw) common).1) erased := by
  have parts := stripped_source expression free captures own (support_fresh expression captures own fresh)
    common context raw erased actual changed
  have available := (InternedFreshOrdinaryFacts.build_verified expression _ common
    context.normal.facts context.inputs).result raw common actual
  constructor
  · intro atom
    exact (filtered_literal common context.normal own raw available atom).trans (parts.1 atom).symm
  · intro row
    exact (filtered_row common context.normal own raw available row).trans (parts.2 row).symm

end MicroCFTA.SourceCurrentPublicationFilterSource
