import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionProfile

namespace MicroCFTA.ProjectionProfileKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryProjectionProfile
open MergedOrdinaryHeight (height childrenHeight)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private theorem literal_read (value : Value Symbol Guard) (before : State Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node value) : Read value before (nodeEdges value) before := by
  cases domain with
  | empty => exact .done 0 rfl
  | ordinary => exact .done 0 rfl

private theorem literal_reads (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values) :
    ReadAll values before (values.flatMap nodeEdges) before := by
  induction values with
  | nil => exact .nil
  | cons value rest ih =>
      cases domain with
      | cons first later => exact .cons (literal_read value before first) (ih later)

/-- Root forest union constructs its own literal rows and constructor return before applying the profile. -/
theorem constructed_root_union {rows arity : Nat} (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values) (profile : ChildrenShape rows arity values)
    (count bound : Nat) (lengthBound : values.length ≤ count) (heightBound : childrenHeight values ≤ bound) :
    let built := run (makeNode (values.flatMap nodeEdges)) before
    ∃ _actual : Forest [] values before built.1 built.2,
      NodeShape (forestRows rows count 0) arity built.1 ∧ height built.1 ≤ bound := by
  dsimp only
  have actual : Forest [] values before (run (makeNode (values.flatMap nodeEdges)) before).1
      (run (makeNode (values.flatMap nodeEdges)) before).2 :=
    .root (.node (literal_reads values before (ChildrenShape.domain values profile)) rfl)
  exact ⟨actual, forest actual semantic available profile count bound lengthBound heightBound⟩

/-- A literal first-child projection derives its selected read, union, result profile, and height. -/
theorem constructed_first_child {rows arity : Nat} (node : Interned NodeKey)
    (entry : Interned (EdgeKey Symbol Guard)) (child : Value Symbol Guard) (more : List (Value Symbol Guard))
    (depth : Nat) (free : List Reference) (before : State Symbol Guard)
    (semantic : SemanticReady before)
    (available : Available before (.node node [.mk entry (child :: more)] depth free))
    (profile : NodeShape rows arity (.node node [.mk entry (child :: more)] depth free)) :
    let built := run (makeNode ([child].flatMap nodeEdges)) before
    ∃ _actual : Project [0] (.node node [.mk entry (child :: more)] depth free) before built.1 built.2,
      NodeShape (projectRows rows 1) arity built.1 ∧ height built.1 ≤ height (.node node [.mk entry (child :: more)] depth free) := by
  dsimp only
  have childShape : NodeShape rows arity child := profile.2.1.2.1
  have selected : select (.mk entry (child :: more) : EdgeValue Symbol Guard).children 0 = some child := by
    simp [select, EdgeValue.children]
  have visited : ProjectRows [] 0 [.mk entry (child :: more)] before [child] before := .selected selected .root .nil
  have combined : Union [child] before (run (makeNode ([child].flatMap nodeEdges)) before).1
      (run (makeNode ([child].flatMap nodeEdges)) before).2 :=
    .node (literal_reads [child] before (.cons (NodeShape.domain child childShape) .nil)) rfl
  have actual := Project.ordinary (entry := node) (depth := depth) (free := free) visited combined
  exact ⟨actual, project actual semantic available profile⟩

/-- A negative forest position returns before any source row or semantic premise is required. -/
theorem negative_position (values : List (Value Symbol Guard)) (before : State Symbol Guard) (suffix : List Int)
    (rows arity count depth bound : Nat) :
    Forest ((-1) :: suffix) values before .empty before ∧
      NodeShape (forestRows rows count depth) arity (.empty : Value Symbol Guard) ∧ height (.empty : Value Symbol Guard) ≤ bound := by
  exact ⟨.missing (by simp [select]), True.intro, Nat.zero_le _⟩

/-- The first actual returned profile and physical receipt supply the second generated projection. -/
theorem serial_generated_projection {rows arity : Nat} {firstPath secondPath : List Int}
    {input middle result : Value Symbol Guard} {before current after : State Symbol Guard}
    (first : Project firstPath input before middle current) (second : Project secondPath middle current result after)
    (semantic : SemanticReady before) (available : Available before input) (profile : NodeShape rows arity input) :
    NodeShape (projectRows (projectRows rows firstPath.length) secondPath.length) arity result ∧
      height result ≤ height input ∧ Available after result ∧ SemanticReady after := by
  have firstShape := project first semantic available profile
  have firstPhysical := SourceCurrentAllocatedFiniteOrdinaryProjection.project first semantic available (NodeShape.domain input profile)
  have secondShape := project second firstPhysical.2.1 firstPhysical.2.2.1 firstShape.1
  have secondPhysical := SourceCurrentAllocatedFiniteOrdinaryProjection.project second firstPhysical.2.1 firstPhysical.2.2.1
    (NodeShape.domain middle firstShape.1)
  exact ⟨secondShape.1, Nat.le_trans secondShape.2 firstShape.2, secondPhysical.2.2.1, secondPhysical.2.1⟩

#print axioms constructed_root_union
#check @constructed_root_union
#print axioms constructed_first_child
#check @constructed_first_child
#print axioms negative_position
#check @negative_position
#print axioms serial_generated_projection
#check @serial_generated_projection
end MicroCFTA.ProjectionProfileKernels
