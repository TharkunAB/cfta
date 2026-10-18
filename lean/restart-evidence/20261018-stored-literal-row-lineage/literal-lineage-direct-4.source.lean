import MicroCFTA.SourceCurrentStoredMuLiteralRows
import MicroCFTA.SourceCurrentStoredLiteralCalls

/-!
# Original source transitions for literal stored-substitution rows

Source descent follows original union members and original Mu bodies.
It does not descend through a generated result. Closed source values keep
their literal rows unchanged. Rebuilt ordinary rows retain actual ordered
child calls under the lexical environment at that source occurrence.
Rows supplied by external replacements have a separate origin.
-/
namespace MicroCFTA.SourceCurrentStoredLiteralRowLineage
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentStoredMuLexicalInputs (shadow)
open SourceCurrentLiteralRootParts (Row)
open SourceCurrentNativeMuPublication (History)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open InternedBinderProtocol (NodeKey Reference)

/-- An indexed original transition reached through original unions and Mu bodies. -/
inductive RowAt : Value Symbol Guard → EdgeValue Symbol Guard → Prop where
  /-- An ordinary source supplies its indexed original row. -/
  | node {entry} {rows : List (EdgeValue Symbol Guard)} {level free} {index : Nat} {row}
      (found : rows[index]? = some row) :
      RowAt (.node entry rows level free) row
  /-- An indexed original union member retains its source row occurrence. -/
  | union {entry} {members : List (Value Symbol Guard)} {level free} {index : Nat} {value row}
      (found : members[index]? = some value)
      (part : RowAt value row) : RowAt (.union entry members level free) row
  /-- The original stored body retains its source row occurrence. -/
  | mu {entry body depth ordinary row} (part : RowAt body row) : RowAt (.mu entry body depth ordinary) row

/-- An external reference reached through original unions and Mu bodies. -/
inductive ReferenceAt : Value Symbol Guard → Reference → Prop where
  /-- A source reference supplies its own name. -/
  | reference (name) : ReferenceAt (.reference name) name
  /-- An indexed original union member retains its reference occurrence. -/
  | union {entry} {members : List (Value Symbol Guard)} {level free} {index : Nat} {value name}
      (found : members[index]? = some value)
      (part : ReferenceAt value name) : ReferenceAt (.union entry members level free) name
  /-- A stored binder retains only references to other source names. -/
  | mu {entry : Interned NodeKey} {body depth ordinary name} (different : name ≠ .interned entry.identity)
      (part : ReferenceAt body name) : ReferenceAt (.mu entry body depth ordinary) name

/-- Literal rows retain a source path, lexical bindings, and actual ordinary child calls. -/
inductive Origin [DecidableEq (EdgeKey Symbol Guard)] :
    Environment Symbol Guard → Value Symbol Guard → EdgeValue Symbol Guard → Prop where
  /-- The closed shortcut returns the exact literal source row. -/
  | identity {environment} {source : Value Symbol Guard} {row} (closed : source.free = []) (part : Row source row) :
      Origin environment source row
  /-- An original ordinary row supplies its fields and ordered child execution. -/
  | node {environment entry} {rows : List (EdgeValue Symbol Guard)} {level free} {index : Nat}
      {original row : EdgeValue Symbol Guard} {before after}
      (found : rows[index]? = some original)
      (symbol : row.entry.key.symbol = original.entry.key.symbol)
      (guard : row.entry.key.constraint = original.entry.key.constraint)
      (called : Calls environment original.children before row.children after) :
      Origin environment (.node entry rows level free) row
  /-- An indexed original union member supplies the same row origin. -/
  | union {environment entry} {members : List (Value Symbol Guard)} {level free} {index : Nat} {original row}
      (found : members[index]? = some original) (part : Origin environment original row) :
      Origin environment (.union entry members level free) row
  /-- The original Mu body uses the actual current ordinary local reference. -/
  | mu {environment entry body depth ordinary} {currentDepth : Value Symbol Guard} {row}
      (part : Origin (shadow (.interned entry.identity)
        (.reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel currentDepth))) environment) body row) :
      Origin environment (.mu entry body depth ordinary) row
  /-- A source reference can supply a row from its actual replacement value. -/
  | replacement {environment name replacement row} (found : environment name = some replacement)
      (part : Row replacement row) : Origin environment (.reference name) row

private theorem literal_source (source : Value Symbol Guard) (row : EdgeValue Symbol Guard)
    (part : Row source row) : RowAt source row := by
  induction part with
  | node member =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .node (index := index) found
  | union member _ ih =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .union (index := index) found ih

/-- Every derived row has an original transition anchor or an explicit external replacement origin. -/
theorem anchor [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {source : Value Symbol Guard} {row : EdgeValue Symbol Guard} (origin : Origin environment source row) :
    (∃ original, RowAt source original ∧ row.entry.key.symbol = original.entry.key.symbol ∧
      row.entry.key.constraint = original.entry.key.constraint ∧ row.children.length = original.children.length ∧
      (row = original ∨ ∃ lexical before after, Calls lexical original.children before row.children after)) ∨
    (∃ name replacement, ReferenceAt source name ∧ environment name = some replacement ∧ Row replacement row) := by
  induction origin with
  | identity _ part => exact .inl ⟨_,literal_source _ _ part,rfl,rfl,rfl,Or.inl rfl⟩
  | node found symbol guard called => exact .inl ⟨_,.node found,symbol,guard,called.length,Or.inr ⟨_,_,_,called⟩⟩
  | union found _ ih =>
      rcases ih with ⟨original,part,symbol,guard,arity,children⟩ | ⟨name,replacement,part,mapped,literal⟩
      · exact .inl ⟨original,.union found part,symbol,guard,arity,children⟩
      · exact .inr ⟨name,replacement,.union found part,mapped,literal⟩
  | @mu environment entry body depth ordinary currentDepth row _ ih =>
      rcases ih with ⟨original,part,symbol,guard,arity,children⟩ | ⟨name,replacement,part,mapped,literal⟩
      · exact .inl ⟨original,.mu part,symbol,guard,arity,children⟩
      · by_cases same : name = .interned entry.identity
        · have equal : .reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel currentDepth)) = replacement := by
            simpa only [shadow,same,ite_true,Option.some.injEq] using mapped
          rw [← equal] at literal
          cases literal
        · have external : environment name = some replacement := by
            simpa only [shadow,same,ite_false] using mapped
          exact .inr ⟨name,replacement,.mu same part,external,literal⟩
  | replacement found part => exact .inr ⟨_,_,.reference _,found,part⟩

/-- Replacements with no selected literal row leave an original transition anchor with full fields and child calls. -/
theorem source_row [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {source : Value Symbol Guard} {row : EdgeValue Symbol Guard} (origin : Origin environment source row)
    (excluded : ∀ name replacement, environment name = some replacement → ¬ Row replacement row) :
    ∃ original, RowAt source original ∧ row.entry.key.symbol = original.entry.key.symbol ∧
      row.entry.key.constraint = original.entry.key.constraint ∧ row.children.length = original.children.length ∧
      (row = original ∨ ∃ lexical before after, Calls lexical original.children before row.children after) := by
  rcases anchor origin with original | ⟨name,replacement,_part,mapped,literal⟩
  · exact original
  · exact False.elim (excluded name replacement mapped literal)

private theorem closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (noFree : value.free = []) :
    execute value environment before = .done value before := by
  unfold execute
  have captured : leaves value = [value] := by
    rw [leaves.eq_def]
    simp only [noFree, List.isEmpty_nil, ite_true]
  rw [captured]
  have encoded : encode [value] [] value = .var 0 := by
    rw [encode.eq_def]
    simp [noFree, InternedStoredSubstitution.slot]
  rw [encoded]
  simpa only [List.map_cons, List.map_nil, InternedFreshOrdinaryConstruction.build,
      List.getElem?_cons_zero, Option.getD_some] using
    congrArg (fun result => (Outcome.done result before : Outcome Symbol Guard (Value Symbol Guard)))
      (InternedStoredSubstitutionScope.input_closed value environment noFree)

private theorem node_physical [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (originals : List (EdgeValue Symbol Guard)) (level : Nat) (free : List Reference)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before)
    (available : Available before (.node entry originals level free)) (replacements : Replacements before environment)
    (opened : free.isEmpty = false) (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute (.node entry originals level free) environment before = .done value after)
    (row : EdgeValue Symbol Guard) (part : Row value row) : ∃ index, (nodeEdges value)[index]? = some row := by
  let captures := leaves (.node entry originals level free)
  let inputs := captures.map (input environment)
  have inputAvailable := InternedStoredSubstitution.inputs_available _ environment before available replacements
  have compiled : encode captures [] (.node entry originals level free) =
      .node (InternedStoredSubstitution.encodeEdges captures [] originals) := by
    rw [encode.eq_def]
    simp only [Value.free,opened,Bool.false_eq_true,ite_false]
  change InternedFreshOrdinaryConstruction.build (encode captures [] (.node entry originals level free))
    inputs before = .done value after at actual
  rw [compiled,InternedFreshOrdinaryConstruction.build] at actual
  cases called : InternedFreshOrdinaryConstruction.buildEdges
      (InternedStoredSubstitution.encodeEdges captures [] originals) inputs before with
  | pending key stopped => simp only [called,Outcome.bind] at actual; cases actual
  | done edges middle =>
      have made : run (makeNode edges) middle = (value,after) :=
        Prod.ext (Outcome.done.inj (by simpa only [called,Outcome.bind,InternedNestedConstruction.work] using actual)).1
          (Outcome.done.inj (by simpa only [called,Outcome.bind,InternedNestedConstruction.work] using actual)).2
      have checked := InternedFreshOrdinaryFacts.buildEdges_verified
        (InternedStoredSubstitution.encodeEdges captures [] originals) inputs before semantic.1.normal.facts inputAvailable
      have facts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
      have ordinary := SourceEqualityRequiredCache.node_ordinary edges middle facts (checked.result edges middle called)
      rw [made] at ordinary
      cases value with
      | node entry rows level free =>
          cases part with
          | node member => exact List.mem_iff_getElem?.mp member
      | empty | reference | mu => cases part
      | union => cases ordinary

/-- An actual completed execution derives source-row provenance by descent on the original stored value. -/
theorem execute_row [DecidableEq (EdgeKey Symbol Guard)] (source : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before)
    (available : Available before source) (replacements : Replacements before environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute source environment before = .done value after)
    (reader : State Symbol Guard) (history : History empty reader) (growth : Grows after reader)
    (row : EdgeValue Symbol Guard) (part : Row value row) : Origin environment source row := by
  by_cases noFree : source.free = []
  · rw [closed source environment before noFree] at actual
    have same : value = source := (Outcome.done.inj actual).1.symm
    subst value
    exact .identity noFree part
  · cases source with
    | empty => exact False.elim (noFree rfl)
    | reference name =>
        have referenceCall : execute (.reference name) environment before =
            .done ((environment name).getD (.reference name)) before := by
          simp [execute,leaves,Value.free,encode,InternedStoredSubstitution.slot,
            InternedFreshOrdinaryConstruction.build,input]
        rw [referenceCall] at actual
        have same := (Outcome.done.inj actual).1
        cases mapped : environment name with
        | none => simp only [mapped,Option.getD_none] at same; rw [← same] at part; cases part
        | some replacement =>
            simp only [mapped,Option.getD_some] at same
            exact .replacement mapped (same ▸ part)
    | node entry originals level free =>
        have opened : free.isEmpty = false := by simpa only [Value.free,List.isEmpty_eq_false_iff] using noFree
        obtain ⟨index,selected⟩ := node_physical entry originals level free environment before semantic available
          replacements opened value after actual row part
        obtain ⟨sourceIndex,original,rows,middle,current,childAfter,next,found,_rebuilt,_edges,_node,
          _earlier,called,_made,_later,symbol,guard,_arity⟩ :=
          SourceCurrentStoredSubstitutionOrigins.node entry originals level free environment before semantic.1.normal
            available replacements opened value after actual index row selected
        exact .node found symbol guard called
    | union entry originals level free =>
        have opened : free.isEmpty = false := by simpa only [Value.free,List.isEmpty_eq_false_iff] using noFree
        obtain ⟨values,middle,index,original,output,current,next,_calls,_made,found,_selected,literal,
          _earlier,called,_later,currentSemantic,originalAvailable,currentReplacements,
          _nextSemantic,_outputAvailable,_nextReplacements,_earlierGrowth,_earlierIssued,_calledGrowth,_calledIssued,
          laterGrowth,_laterIssued⟩ := SourceCurrentStoredLiteralCalls.union_row entry originals level free environment
            before semantic available replacements opened value after actual row part
        exact .union found (execute_row original environment current currentSemantic originalAvailable currentReplacements
          output next called reader history (grows_trans laterGrowth growth) row literal)
    | mu entry body depth ordinary =>
        obtain ⟨currentDepth,afterDepth,raw,middle,_depthDone,bodyDone,bodySemantic,bodyAvailable,bodyReplacements,
          _rawGrowth,_rawIssued,laterGrowth,_laterIssued,literal⟩ := SourceCurrentStoredMuLiteralRows.mu entry body depth ordinary
            environment before semantic available replacements value after actual reader history growth row part
        exact .mu (execute_row body (shadow (.interned entry.identity)
          (.reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel currentDepth))) environment)
          afterDepth bodySemantic bodyAvailable bodyReplacements raw middle bodyDone
          reader history (grows_trans laterGrowth growth) row literal)
termination_by sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals first | omega | exact Nat.lt_trans (List.sizeOf_lt_of_mem (List.mem_of_getElem? found)) (by omega)

/-- Initial semantic inputs construct a successful return and source provenance for every literal output row. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (source : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before)
    (covered : Covered [] before) (available : Available before source) (replacements : Replacements before environment)
    (history : History empty before) :
    ∃ value after, execute source environment before = .done value after ∧
      SemanticHeap after ∧ Covered [] after ∧ Available after value ∧
      Nonempty (History before after) ∧ Nonempty (History empty after) ∧
      ∀ row, Row value row → Origin environment source row := by
  obtain ⟨value,after,actual,context,depthHeap,retained,output,_,_⟩ :=
    InternedFreshOrdinaryStoredSubstitution.execute_complete_decoded source environment before semantic.1
      available replacements semantic.2 covered
  have initialContext := SourceRecursiveIntersectionSemanticHeap.context before semantic
    ((leaves source).map (input environment))
    (InternedStoredSubstitution.inputs_available source environment before available replacements)
  have emitted := SourceCurrentNativeMuPublication.build_history (encode (leaves source) [] source)
    ((leaves source).map (input environment)) before ⟨initialContext,semantic.2⟩
  change Nonempty (History before (execute source environment before).state) at emitted
  rw [actual,Outcome.state] at emitted
  obtain ⟨segment⟩ := emitted
  have finalHistory := history.trans segment
  exact ⟨value,after,actual,⟨context,depthHeap⟩,retained,output,⟨segment⟩,⟨finalHistory⟩,
    fun row part => execute_row source environment before semantic available replacements value after actual
      after finalHistory (grows_refl after) row part⟩

end MicroCFTA.SourceCurrentStoredLiteralRowLineage
