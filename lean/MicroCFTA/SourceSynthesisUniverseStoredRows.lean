import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
import MicroCFTA.InternedStoredSubstitutionScope
import MicroCFTA.SourceSynthesisUniverseRowTransform
import MicroCFTA.SourceRecursiveIntersectionKernelReadback

/-!
# Actual stored reconstruction of source-ordered universe rows

Closed marker children and external recursive references are original
captured leaves. Source lexical lookup therefore rebuilds their literal
replacement inputs without cache effects. Actual source-ordered edge
replay then supplies the target rows. The final operation remains the
real makeNode work. Its result and cache hit are not assumed here.
-/
namespace MicroCFTA.SourceSynthesisUniverseStoredRows
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedProvenance (Values)
open InternedNestedConstruction (Outcome build buildMany buildEdges)
open InternedStoredSubstitution (Environment leaves manyLeaves edgeLeaves input encode encodeMany encodeEdges)
open InternedStoredClosedMuCompletion (PreparedWithoutMu)
open SourceRecursiveIntersectionControl (pair repeatedValue)

variable {Symbol Guard : Type}

private theorem leaf_eq (name : Reference) (marker child : Value Symbol Guard) (closed : marker.free = [])
    (kind : child = marker ∨ child = .reference name) : leaves child = [child] := by
  rcases kind with rfl | rfl
  · rw [leaves.eq_def]
    simp only [closed, List.isEmpty_nil, ↓reduceIte]
  · rw [leaves.eq_def]
    simp only [Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]

private theorem manyLeaves_eq (name : Reference) (marker : Value Symbol Guard) (closed : marker.free = [])
    (values : List (Value Symbol Guard)) :
    (∀ child ∈ values, child = marker ∨ child = .reference name) → manyLeaves values = values := by
  induction values with
  | nil => intro kinds; simp only [manyLeaves]
  | cons first rest ih =>
      intro kinds
      have own := leaf_eq name marker first closed (kinds first List.mem_cons_self)
      have tail := ih (fun child member => kinds child (List.mem_cons_of_mem _ member))
      simp only [manyLeaves, own, tail, List.singleton_append]

private theorem edgeLeaves_eq (name : Reference) (marker : Value Symbol Guard) (closed : marker.free = [])
    (rows : List (EdgeValue Symbol Guard)) :
    (∀ row ∈ rows, ∀ child ∈ row.children, child = marker ∨ child = .reference name) →
      edgeLeaves rows = rows.flatMap EdgeValue.children := by
  induction rows with
  | nil => intro kinds; simp only [edgeLeaves, List.flatMap_nil]
  | cons first rest ih =>
      intro kinds
      cases first with
      | mk entry children =>
          have own := manyLeaves_eq name marker closed children (kinds _ List.mem_cons_self)
          have tail := ih (fun row member => kinds row (List.mem_cons_of_mem _ member))
          simp only [edgeLeaves, List.flatMap_cons, EdgeValue.children, own, tail]

/-- An arbitrary external source reference and closed marker remain captured leaves. -/
theorem leaves_reference_eq_children (name : Reference) (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (marker : Value Symbol Guard) (closed : marker.free = [])
    (kinds : ∀ row ∈ rows, ∀ child ∈ row.children, child = marker ∨ child = .reference name) :
    leaves (.node entry rows 0 [name]) = rows.flatMap EdgeValue.children := by
  rw [leaves.eq_def]
  simp only [Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
  exact edgeLeaves_eq name marker closed rows kinds

/-- Each actual original child occurs as one captured leaf in the open body. -/
theorem leaves_eq_children (uId : Nat) (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (marker : Value Symbol Guard) (closed : marker.free = [])
    (kinds : ∀ row ∈ rows, ∀ child ∈ row.children, child = marker ∨ child = .reference (.interned uId)) :
    leaves (.node entry rows 0 [.interned uId]) = rows.flatMap EdgeValue.children :=
  leaves_reference_eq_children (.interned uId) entry rows marker closed kinds

private theorem build_leaf [DecidableEq (EdgeKey Symbol Guard)] (context : List (Value Symbol Guard))
    (environment : Environment Symbol Guard) (name : Reference) (marker child : Value Symbol Guard)
    (current : InternedConstructorTemplates.State Symbol Guard) (facts : Facts current)
    (available : Values current context) (closed : marker.free = []) (member : child ∈ context)
    (kind : child = marker ∨ child = .reference name) :
    build (encode context [] child) (context.map (input environment)) current = .done (input environment child) current := by
  rcases kind with same | same
  · subst child
    have done := InternedStoredSubstitutionScope.build_closed context [] [] marker environment current
      facts.coherent available member rfl closed
    simpa only [List.nil_append, InternedStoredSubstitutionScope.input_closed marker environment closed] using done
  · subst child
    have done := InternedStoredSubstitutionScope.build_external context [] [] name environment current
      facts.coherent available member rfl rfl
    simpa only [List.nil_append, input] using done

private theorem build_children [DecidableEq (EdgeKey Symbol Guard)] (context : List (Value Symbol Guard))
    (environment : Environment Symbol Guard) (values : List (Value Symbol Guard))
    (current : InternedConstructorTemplates.State Symbol Guard)
    (done : ∀ child ∈ values, build (encode context [] child) (context.map (input environment)) current =
      .done (input environment child) current) :
    buildMany (encodeMany context [] values) (context.map (input environment)) current =
      .done (values.map (input environment)) current := by
  induction values with
  | nil => simp only [encodeMany, buildMany, List.map_nil]
  | cons first rest ih =>
      have own := done first List.mem_cons_self
      have tail := ih (fun child member => done child (List.mem_cons_of_mem _ member))
      simp only [encodeMany, buildMany, own, Outcome.bind, tail, List.map_cons]

private theorem build_rows [DecidableEq (EdgeKey Symbol Guard)] (context : List (Value Symbol Guard))
    (environment : Environment Symbol Guard) (name : Reference) (top : Guard) (marker : Value Symbol Guard)
    (current : InternedConstructorTemplates.State Symbol Guard) (facts : Facts current)
    (available : Values current context) (closed : marker.free = [])
    (sources targets : List (EdgeValue Symbol Guard))
    (replayed : All₂ (fun source target =>
      run (makeEdge source.entry.key.symbol top (source.children.map (input environment))) current = (target, current)) sources targets) :
    (∀ source ∈ sources, source.entry.key.constraint = top) →
    (∀ source ∈ sources, ∀ child ∈ source.children, child = marker ∨ child = .reference name) →
    (∀ source ∈ sources, ∀ child ∈ source.children, child ∈ context) →
    buildEdges (encodeEdges context [] sources) (context.map (input environment)) current = .done targets current := by
  induction replayed with
  | nil => intro tops kinds members; simp only [encodeEdges, buildEdges]
  | @cons source target sources targets own rest ih =>
      intro tops kinds members
      cases source with
      | mk entry children =>
          change run (makeEdge entry.key.symbol top (children.map (input environment))) current = (target, current) at own
          have childrenDone := build_children context environment children current (fun child present =>
            build_leaf context environment name marker child current facts available closed
              (members _ List.mem_cons_self child present) (kinds _ List.mem_cons_self child present))
          have tailDone := ih
            (fun source member => tops source (List.mem_cons_of_mem _ member))
            (fun source member => kinds source (List.mem_cons_of_mem _ member))
            (fun source member => members source (List.mem_cons_of_mem _ member))
          have sourceTop : entry.key.constraint = top := tops _ List.mem_cons_self
          simp only [encodeEdges, buildEdges, childrenDone, Outcome.bind, sourceTop,
            InternedNestedConstruction.work]
          rw [own, tailDone]

/-- Arbitrary source replacement uses its actual replayed rows before the real final node constructor. -/
theorem execute_reference_eq_work [DecidableEq (EdgeKey Symbol Guard)] (top : Guard) (name : Reference) (entry : Interned NodeKey)
    (sources targets : List (EdgeValue Symbol Guard)) (marker : Value Symbol Guard)
    (environment : Environment Symbol Guard)
    (current : InternedConstructorTemplates.State Symbol Guard) (facts : Facts current)
    (available : Available current (.node entry sources 0 [name])) (closed : marker.free = [])
    (tops : ∀ source ∈ sources, source.entry.key.constraint = top)
    (kinds : ∀ source ∈ sources, ∀ child ∈ source.children, child = marker ∨ child = .reference name)
    (replayed : All₂ (fun source target =>
      run (makeEdge source.entry.key.symbol top (source.children.map (input environment))) current =
        (target, current)) sources targets) :
    InternedFreshOrdinaryStoredSubstitution.execute (.node entry sources 0 [name]) environment current =
      InternedNestedConstruction.work (makeNode targets) current := by
  let body : Value Symbol Guard := .node entry sources 0 [name]
  let context := leaves body
  have contextAvailable : Values current context := InternedStoredSubstitution.leaves_available body current available
  have members : ∀ source ∈ sources, ∀ child ∈ source.children, child ∈ context := by
    intro source present child selected
    change child ∈ leaves (.node entry sources 0 [name])
    rw [leaves_reference_eq_children name entry sources marker closed kinds]
    exact List.mem_flatMap.mpr ⟨source, present, selected⟩
  have edgesDone := build_rows context environment name top marker current facts contextAvailable closed
    sources targets replayed tops kinds members
  have prepared : PreparedWithoutMu body := by
    apply PreparedWithoutMu.node
    intro child present
    obtain ⟨source, sourceMember, childMember⟩ := List.mem_flatMap.mp present
    rcases kinds source sourceMember child childMember with same | same
    · subst child
      exact .closed marker closed
    · subst child
      exact .reference name
  change InternedFreshOrdinaryStoredSubstitution.execute body environment current =
    InternedNestedConstruction.work (makeNode targets) current
  rw [InternedFreshOrdinaryStoredSubstitution.execute_eq body environment current prepared]
  unfold InternedStoredSubstitution.execute
  change build (encode context [] (.node entry sources 0 [name]))
    (context.map (input environment)) current = InternedNestedConstruction.work (makeNode targets) current
  rw [encode.eq_def]
  simp only [Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, build, edgesDone, Outcome.bind]

/-- Actual edge replay determines stored execution up to the real final node constructor. -/
theorem execute_eq_work [DecidableEq (EdgeKey Symbol Guard)] (top : Guard) (uId : Nat) (entry : Interned NodeKey)
    (sources targets : List (EdgeValue Symbol Guard)) (marker : Value Symbol Guard)
    (current : InternedConstructorTemplates.State Symbol Guard) (facts : Facts current)
    (available : Available current (.node entry sources 0 [.interned uId])) (closed : marker.free = [])
    (tops : ∀ source ∈ sources, source.entry.key.constraint = top)
    (kinds : ∀ source ∈ sources, ∀ child ∈ source.children, child = marker ∨ child = .reference (.interned uId))
    (replayed : All₂ (fun source target =>
      run (makeEdge source.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children uId source)) current =
        (target, current)) sources targets) :
    InternedFreshOrdinaryStoredSubstitution.execute (.node entry sources 0 [.interned uId])
      (InternedStoredSubstitutionRebind.replacement (.interned uId) (repeatedValue (pair uId uId))) current =
      InternedNestedConstruction.work (makeNode targets) current :=
  execute_reference_eq_work top (.interned uId) entry sources targets marker
    (InternedStoredSubstitutionRebind.replacement (.interned uId) (repeatedValue (pair uId uId)))
    current facts available closed tops kinds replayed

private theorem runs_of_kernel [DecidableEq (EdgeKey Symbol Guard)] (top : Guard) (uId : Nat)
    (current : SourceRecursiveIntersectionKernel.Machine Symbol Guard) (sources targets : List (EdgeValue Symbol Guard))
    (replayed : All₂ (fun source target => SourceRecursiveIntersectionKernel.work
      (makeEdge source.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children uId source)) current =
        .done target current) sources targets) :
    All₂ (fun source target =>
      run (makeEdge source.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children uId source)) current.heap =
        (target, current.heap)) sources targets := by
  induction replayed with
  | nil => exact .nil
  | @cons source target sources targets own rest ih =>
      have fields := SourceRecursiveIntersectionKernel.work_done _ current target current own
      exact .cons (Prod.ext fields.1.symm (congrArg SourceRecursiveIntersectionKernel.Machine.heap fields.2).symm) ih

/-- Literal kernel edge replay supplies the same stored execution equation without a domain-cache premise. -/
theorem execute_eq_work_of_kernel [DecidableEq (EdgeKey Symbol Guard)] (top : Guard) (uId : Nat) (entry : Interned NodeKey)
    (sources targets : List (EdgeValue Symbol Guard)) (marker : Value Symbol Guard)
    (current : SourceRecursiveIntersectionKernel.Machine Symbol Guard) (facts : Facts current.heap)
    (available : Available current.heap (.node entry sources 0 [.interned uId])) (closed : marker.free = [])
    (tops : ∀ source ∈ sources, source.entry.key.constraint = top)
    (kinds : ∀ source ∈ sources, ∀ child ∈ source.children, child = marker ∨ child = .reference (.interned uId))
    (replayed : All₂ (fun source target => SourceRecursiveIntersectionKernel.work
      (makeEdge source.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children uId source)) current =
        .done target current) sources targets) :
    InternedFreshOrdinaryStoredSubstitution.execute (.node entry sources 0 [.interned uId])
      (InternedStoredSubstitutionRebind.replacement (.interned uId) (repeatedValue (pair uId uId))) current.heap =
      InternedNestedConstruction.work (makeNode targets) current.heap := by
  apply execute_eq_work top uId entry sources targets marker current.heap facts available closed tops kinds
  exact runs_of_kernel top uId current sources targets replayed

end MicroCFTA.SourceSynthesisUniverseStoredRows
