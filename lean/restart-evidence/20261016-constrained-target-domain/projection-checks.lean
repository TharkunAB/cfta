import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.read_domain
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.read_domain
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.readAll_domain
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.readAll_domain
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.union_domain
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.union_domain
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.project
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.project
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.rows
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.rows
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.forest
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection.forest

namespace FiniteOrdinaryProjectionChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open InternedNestedProvenance (Values)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- A literal ordinary read preserves every original row and the complete input heap. -/
theorem ordinary_read (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (state : State Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Rows edges) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Rows edges ∧
      ∃ _trace : Read (.node entry edges depth free) state edges state, state = state := by
  have trace : Read (.node entry edges depth free) state edges state := .done 0 rfl
  have checked := SourceCurrentAllocatedFiniteOrdinaryProjection.read_domain trace (.ordinary domain)
  exact ⟨checked.1, trace, checked.2⟩

/-- A negative forest index takes the missing branch and returns Empty at the exact input heap. -/
theorem negative_forest (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (semantic : SemanticReady state) (available : Values state values)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values) :
    SourceEqualityRequiredCache.Keeps state state ∧ SemanticReady state ∧ Available state (.empty : Value Symbol Guard) ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node (.empty : Value Symbol Guard) := by
  apply SourceCurrentAllocatedFiniteOrdinaryProjection.forest
    (Forest.missing (path := []) (index := -1) (by simp [select])) semantic available domain

omit [DecidableEq (EdgeKey Symbol Guard)] in
/-- A root union reads the full nonempty equality-class row before actual node reconstruction. -/
theorem full_guard_root {Formula : Type} [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
    (symbol : Symbol) (guard : SourceGuards.Guard Formula)
    (state : State Symbol (SourceSymbolicIndex.Constraint Formula))
    (semantic : SemanticReady state)
    (available : Available state (.node ⟨1, .node [0]⟩
      [.mk ⟨0, ⟨symbol, [.empty, .empty], ⟨some [[[0], [1]]], guard⟩⟩⟩ [.empty, .empty]] 0 [])) :
    let edge : EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula) :=
      .mk ⟨0, ⟨symbol, [.empty, .empty], ⟨some [[[0], [1]]], guard⟩⟩⟩ [.empty, .empty]
    let built := run (makeNode [edge]) state
    SourceEqualityRequiredCache.Keeps state built.2 ∧ SemanticReady built.2 ∧ Available built.2 built.1 ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node built.1 := by
  let edge : EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula) :=
    .mk ⟨0, ⟨symbol, [.empty, .empty], ⟨some [[[0], [1]]], guard⟩⟩⟩ [.empty, .empty]
  have first : Read (.node ⟨1, .node [0]⟩ [edge] 0 []) state [edge] state := .done 0 rfl
  have read : ReadAll [.node ⟨1, .node [0]⟩ [edge] 0 []] state [edge] state := by
    simpa only [List.append_nil] using ReadAll.cons first (ReadAll.nil (state := state))
  exact SourceCurrentAllocatedFiniteOrdinaryProjection.forest (Forest.root (.node read rfl)) semantic
    (by intro value member; cases List.mem_singleton.mp member; exact available)
    (.cons (.ordinary (.cons (.cons .empty (.cons .empty .nil)) .nil)) .nil)

/-- A second actual forest projection uses only the first projection's derived returned invariants. -/
theorem serial {firstPath secondPath : List Int} {values : List (Value Symbol Guard)}
    {result output : Value Symbol Guard} {before middle after : State Symbol Guard}
    (first : Forest firstPath values before result middle)
    (second : Forest secondPath [result] middle output after)
    (semantic : SemanticReady before) (available : Values before values)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values) :
    SourceEqualityRequiredCache.Keeps before after ∧ SemanticReady after ∧ Available after output ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node output := by
  have reached := SourceCurrentAllocatedFiniteOrdinaryProjection.forest first semantic available domain
  have final := SourceCurrentAllocatedFiniteOrdinaryProjection.forest second reached.2.1
    (by intro value member; cases List.mem_singleton.mp member; exact reached.2.2.1)
    (.cons reached.2.2.2 .nil)
  exact ⟨reached.1.trans final.1, final.2⟩

end FiniteOrdinaryProjectionChecks

#print axioms FiniteOrdinaryProjectionChecks.ordinary_read
#check @FiniteOrdinaryProjectionChecks.ordinary_read
#print axioms FiniteOrdinaryProjectionChecks.negative_forest
#check @FiniteOrdinaryProjectionChecks.negative_forest
#print axioms FiniteOrdinaryProjectionChecks.full_guard_root
#check @FiniteOrdinaryProjectionChecks.full_guard_root
#print axioms FiniteOrdinaryProjectionChecks.serial
#check @FiniteOrdinaryProjectionChecks.serial
