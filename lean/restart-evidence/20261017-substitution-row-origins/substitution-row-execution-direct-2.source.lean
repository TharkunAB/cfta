import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedStoredSubstitution
import MicroCFTA.MergedPhysicalGroupEdges
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Indexed rows in actual encoded substitution

The child trace retains literal encoded calls in their execution order.
Each rebuilt row retains its original symbol, full guard, and child arity.
Node normalization can remove or reorder rows. A normalized output row
therefore names an original occurrence without an injectivity requirement.
-/
namespace MicroCFTA.SourceCurrentSubstitutionRowExecution
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedEdgeResidency
open InternedNestedConstruction (Outcome work)
open InternedStoredSubstitution (encode encodeMany encodeEdges)
open InternedNestedProvenance (Values Edges)
open InternedNestedFacts
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference)
variable {context inputs originals outputs : List (Value Symbol Guard)} {locals : List Reference}
  {before after : State Symbol Guard}

/-- Each child occurrence retains its literal encoded build and complete intermediate heaps. -/
inductive ChildTrace [DecidableEq (EdgeKey Symbol Guard)] (context : List (Value Symbol Guard))
    (locals : List Reference) (inputs : List (Value Symbol Guard)) :
    List (Value Symbol Guard) → State Symbol Guard → List (Value Symbol Guard) → State Symbol Guard → Prop where
  /-- The empty child list has no constructor effects. -/
  | nil (state) : ChildTrace context locals inputs [] state [] state
  /-- The next original child completes before the remaining children execute. -/
  | cons (original originals before middle after output outputs)
      (called : build (encode context locals original) inputs before = .done output middle)
      (rest : ChildTrace context locals inputs originals middle outputs after) :
      ChildTrace context locals inputs (original :: originals) before (output :: outputs) after

/-- The trace retains the exact ordered child count. -/
theorem ChildTrace.length [DecidableEq (EdgeKey Symbol Guard)]
    (trace : ChildTrace context locals inputs originals before outputs after) : outputs.length = originals.length := by
  induction trace with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ ih => exact congrArg Nat.succ ih

/-- The trace reconstructs the actual full encoded child computation. -/
theorem ChildTrace.actual [DecidableEq (EdgeKey Symbol Guard)]
    (trace : ChildTrace context locals inputs originals before outputs after) :
    buildMany (encodeMany context locals originals) inputs before = .done outputs after := by
  induction trace with
  | nil => rfl
  | cons original originals before middle after output outputs called rest ih =>
      simp only [encodeMany, buildMany, called, Outcome.bind, ih]

/-- Every completed encoded child list supplies its actual ordered trace. -/
theorem ChildTrace.children [DecidableEq (EdgeKey Symbol Guard)]
    (context : List (Value Symbol Guard)) (locals : List Reference) (inputs originals : List (Value Symbol Guard))
    (before : State Symbol Guard) (outputs : List (Value Symbol Guard)) (after : State Symbol Guard)
    (actual : buildMany (encodeMany context locals originals) inputs before = .done outputs after) :
    ChildTrace context locals inputs originals before outputs after := by
  induction originals generalizing before outputs after with
  | nil =>
      simp only [encodeMany, buildMany, Outcome.done.injEq] at actual
      obtain ⟨rfl,rfl⟩ := actual
      exact .nil before
  | cons original originals ih =>
      simp only [encodeMany, buildMany] at actual
      cases first : build (encode context locals original) inputs before with
      | pending key state => simp only [first, Outcome.bind] at actual; cases actual
      | done output middle =>
          simp only [first, Outcome.bind] at actual
          cases tail : buildMany (encodeMany context locals originals) inputs middle with
          | pending key state => simp only [tail] at actual; cases actual
          | done values final =>
              simp only [tail, Outcome.done.injEq] at actual
              obtain ⟨rfl,rfl⟩ := actual
              exact .cons original originals before middle final output values first (ih middle values final tail)

/-- An indexed child retains the same original position and exact prefix and suffix calls. -/
theorem ChildTrace.indexed [DecidableEq (EdgeKey Symbol Guard)]
    (trace : ChildTrace context locals inputs originals before outputs after)
    (index : Nat) (output : Value Symbol Guard) (selected : outputs[index]? = some output) :
    ∃ original current next, originals[index]? = some original ∧
      ChildTrace context locals inputs (originals.take index) before (outputs.take index) current ∧
      build (encode context locals original) inputs current = .done output next ∧
      ChildTrace context locals inputs (originals.drop (index + 1)) next (outputs.drop (index + 1)) after := by
  induction trace generalizing index with
  | nil => simp only [List.getElem?_nil] at selected; cases selected
  | cons original originals before middle after value values called rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst output
          exact ⟨original,before,middle,rfl,.nil before,called,rest⟩
      | succ index =>
          obtain ⟨source,current,next,found,earlier,child,later⟩ :=
            ih index (by simpa only [List.getElem?_cons_succ] using selected)
          refine ⟨source,current,next,found,?_,child,?_⟩
          · simpa only [List.take_succ_cons] using
              ChildTrace.cons original _ before middle current value _ called earlier
          · simpa only [List.drop_succ_cons,Nat.add_assoc] using later

private theorem rows_split [DecidableEq (EdgeKey Symbol Guard)]
    (context : List (Value Symbol Guard)) (locals : List Reference) (inputs : List (Value Symbol Guard))
    (originals : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (outputs : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (actual : buildEdges (encodeEdges context locals originals) inputs before = .done outputs after)
    (index : Nat) (output : EdgeValue Symbol Guard) (selected : outputs[index]? = some output) :
    ∃ original current middle next values, originals[index]? = some original ∧
      buildEdges (encodeEdges context locals (originals.take index)) inputs before = .done (outputs.take index) current ∧
      ChildTrace context locals inputs original.children current values middle ∧
      run (makeEdge original.entry.key.symbol original.entry.key.constraint values) middle = (output,next) ∧
      buildEdges (encodeEdges context locals (originals.drop (index + 1))) inputs next =
        .done (outputs.drop (index + 1)) after := by
  induction originals generalizing before outputs after index with
  | nil =>
      simp only [encodeEdges,buildEdges,Outcome.done.injEq] at actual
      obtain ⟨rfl,rfl⟩ := actual
      simp only [List.getElem?_nil] at selected
      cases selected
  | cons original originals ih =>
      cases original with
      | mk entry children =>
          simp only [encodeEdges,buildEdges] at actual
          cases childrenDone : buildMany (encodeMany context locals children) inputs before with
          | pending key state => simp only [childrenDone,Outcome.bind] at actual; cases actual
          | done values middle =>
              let made := run (makeEdge entry.key.symbol entry.key.constraint values) middle
              simp only [childrenDone,Outcome.bind,work] at actual
              cases tailDone : buildEdges (encodeEdges context locals originals) inputs made.2 with
              | pending key state => simp only [tailDone,Outcome.bind] at actual; cases actual
              | done tailValues final =>
                  simp only [tailDone,Outcome.bind,Outcome.done.injEq] at actual
                  obtain ⟨rfl,rfl⟩ := actual
                  cases index with
                  | zero =>
                      simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
                      subst output
                      exact ⟨.mk entry children,before,middle,made.2,values,rfl,rfl,
                        ChildTrace.children context locals inputs children before values middle childrenDone,rfl,tailDone⟩
                  | succ index =>
                      obtain ⟨source,current,childAfter,next,results,found,earlier,trace,edgeDone,later⟩ :=
                        ih made.2 tailValues final tailDone index
                          (by simpa only [List.getElem?_cons_succ] using selected)
                      refine ⟨source,current,childAfter,next,results,found,?_,trace,edgeDone,?_⟩
                      · simp only [List.take_succ_cons,encodeEdges,buildEdges,childrenDone,Outcome.bind,work]
                        rw [earlier]
                        rfl
                      · simpa only [List.drop_succ_cons,Nat.add_assoc] using later

/-- Each literal rebuilt row retains its indexed source, exact fields, and actual ordered child calls. -/
theorem rows_indexed [DecidableEq (EdgeKey Symbol Guard)]
    (context : List (Value Symbol Guard)) (locals : List Reference) (inputs : List (Value Symbol Guard))
    (originals : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (outputs : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (facts : Facts before) (available : Values before inputs)
    (actual : buildEdges (encodeEdges context locals originals) inputs before = .done outputs after)
    (index : Nat) (output : EdgeValue Symbol Guard) (selected : outputs[index]? = some output) :
    ∃ original current middle next values, originals[index]? = some original ∧
      buildEdges (encodeEdges context locals (originals.take index)) inputs before = .done (outputs.take index) current ∧
      ChildTrace context locals inputs original.children current values middle ∧
      run (makeEdge original.entry.key.symbol original.entry.key.constraint values) middle = (output,next) ∧
      buildEdges (encodeEdges context locals (originals.drop (index + 1))) inputs next =
        .done (outputs.drop (index + 1)) after ∧
      output.entry.key.symbol = original.entry.key.symbol ∧
      output.entry.key.constraint = original.entry.key.constraint ∧ output.children = values ∧
      output.children.length = original.children.length := by
  obtain ⟨original,current,middle,next,values,found,earlier,trace,made,later⟩ :=
    rows_split context locals inputs originals before outputs after actual index output selected
  have initial := InternedFreshOrdinaryFacts.buildEdges_verified
    (encodeEdges context locals (originals.take index)) inputs before facts available
  have currentFacts : Facts current := by simpa only [earlier,Outcome.state] using initial.facts
  have currentInputs : Values current inputs := by
    intro value member
    simpa only [earlier,Outcome.state] using initial.available value (available value member)
  have childrenChecked := InternedFreshOrdinaryFacts.buildMany_verified
    (encodeMany context locals original.children) inputs current currentFacts currentInputs
  have middleFacts : Facts middle := by simpa only [trace.actual,Outcome.state] using childrenChecked.facts
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleFacts
    original.entry.key.symbol original.entry.key.constraint values
    (childrenChecked.result values middle trace.actual)
  rw [made] at fields
  exact ⟨original,current,middle,next,values,found,earlier,trace,made,later,
    fields.1,fields.2.1,fields.2.2,fields.2.2 ▸ trace.length⟩

/-- A normalized node row maps to a rebuilt occurrence and then its indexed source row. -/
theorem node_indexed [DecidableEq (EdgeKey Symbol Guard)]
    (context : List (Value Symbol Guard)) (locals : List Reference) (inputs : List (Value Symbol Guard))
    (originals : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (facts : Facts before) (available : Values before inputs)
    (actual : build (.node (encodeEdges context locals originals)) inputs before = .done result after)
    (index : Nat) (output : EdgeValue Symbol Guard) (selected : (nodeEdges result)[index]? = some output) :
    ∃ sourceIndex original rows middle current childAfter next values,
      originals[sourceIndex]? = some original ∧ rows[sourceIndex]? = some output ∧
      buildEdges (encodeEdges context locals originals) inputs before = .done rows middle ∧
      run (makeNode rows) middle = (result,after) ∧
      buildEdges (encodeEdges context locals (originals.take sourceIndex)) inputs before =
        .done (rows.take sourceIndex) current ∧
      ChildTrace context locals inputs original.children current values childAfter ∧
      run (makeEdge original.entry.key.symbol original.entry.key.constraint values) childAfter = (output,next) ∧
      buildEdges (encodeEdges context locals (originals.drop (sourceIndex + 1))) inputs next =
        .done (rows.drop (sourceIndex + 1)) middle ∧
      output.entry.key.symbol = original.entry.key.symbol ∧
      output.entry.key.constraint = original.entry.key.constraint ∧ output.children = values ∧
      output.children.length = original.children.length := by
  rw [build] at actual
  cases rowsDone : buildEdges (encodeEdges context locals originals) inputs before with
  | pending key state => simp only [rowsDone,Outcome.bind] at actual; cases actual
  | done rows middle =>
      simp only [rowsDone,Outcome.bind,work,Outcome.done.injEq] at actual
      obtain ⟨rfl,rfl⟩ := actual
      have checked := InternedFreshOrdinaryFacts.buildEdges_verified
        (encodeEdges context locals originals) inputs before facts available
      have middleFacts : Facts middle := by simpa only [rowsDone,Outcome.state] using checked.facts
      have rowResident := checked.result rows middle rowsDone
      rw [EqualityLeafProjectionPhysical.makeNode_edges rows middle middleFacts.coherent middleFacts.linked rowResident] at selected
      have member := (List.mem_filter.mp (canonicalEdges_member _ output (List.mem_of_getElem? selected))).1
      obtain ⟨sourceIndex,found⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨original,current,childAfter,next,values,originalFound,earlier,trace,made,later,symbol,guard,children,arity⟩ :=
        rows_indexed context locals inputs originals before rows middle facts available rowsDone sourceIndex output found
      exact ⟨sourceIndex,original,rows,middle,current,childAfter,next,values,originalFound,found,rfl,rfl,
        earlier,trace,made,later,symbol,guard,children,arity⟩

end MicroCFTA.SourceCurrentSubstitutionRowExecution
