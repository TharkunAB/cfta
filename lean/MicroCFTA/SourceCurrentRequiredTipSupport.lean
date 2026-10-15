import MicroCFTA.SourceCurrentRequiredSupport
import MicroCFTA.SourceCurrentSecondaryEndpointClosed
import MicroCFTA.SourceEqualitySelectedRequired

/-!
# Required-tip certificates including terminal endpoints

Worker completion needs no certificate for an empty local requirement.
Retaining endpoint closedness needs that certificate as well. These
domains keep every maximal original tip, including its empty suffix.
Actual ordinary and recursive heads transfer them to exact row children.
Reconstructed worker outputs still require a separate preservation proof.
-/
namespace MicroCFTA.SourceCurrentRequiredTipSupport
open InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open InternedNestedProvenance (Values)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentRequiredSupport (Tip)
open SourceCurrentSecondaryProjectionSupport (Support)
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready

/-- Each maximal local tip retains its certificate, including an empty terminal suffix. -/
def NodeTips [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (needed : Needed) (value : Value Symbol Guard) : Prop :=
  ∀ path, Tip needed path → Support unconstrained anchor path value

/-- Every present selected original child retains all its stored maximal tips. -/
def ForestTips [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (needed : Needed) (values : List (Value Symbol Guard)) : Prop :=
  match needed with
  | .node entries => ∀ index child, SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some child →
      ∀ value, values[index]? = some value → NodeTips unconstrained anchor child value

variable {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
  {needed : Needed} {value : Value Symbol Guard} {values : List (Value Symbol Guard)}

/-- Retaining terminal tips implies the existing worker input domain. -/
theorem node_support [DecidableEq (EdgeKey Symbol Guard)]
    (tips : NodeTips unconstrained anchor needed value) :
    SourceCurrentRequiredSupport.NodeSupport unconstrained anchor needed value :=
  fun path tip _ => tips path tip

/-- The strengthened original forest domain supplies the existing completion and language domain. -/
theorem forest_support [DecidableEq (EdgeKey Symbol Guard)]
    (tips : ForestTips unconstrained anchor needed values) :
    SourceCurrentRequiredSupport.ForestSupport unconstrained anchor needed values := by
  cases needed with
  | node entries => exact fun index child found value selected => node_support (tips index child found value selected)

/-- An empty local requirement retains actual original endpoint closedness. -/
theorem empty_closed [DecidableEq (EdgeKey Symbol Guard)]
    (ready : GateReady anchor) (tips : NodeTips unconstrained anchor (.node []) value) : value.free = [] :=
  SourceCurrentSecondaryEndpointClosed.support_closed unconstrained anchor ready value (tips [] .leaf)

/-- Effect-free original path certificates derive the complete compiled forest tip domain. -/
theorem of_paths [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (paths : Class) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (available : Values state values)
    (traces : ∀ path ∈ paths, SourceCurrentSecondaryTrace.PathTrace unconstrained values path state false state) :
    ForestTips unconstrained state (build (paths.map (List.map Int.ofNat))) values := by
  cases compiled : build (paths.map (List.map Int.ofNat)) with
  | node entries =>
      intro index child found value selected path tip
      have whole : Tip (build (paths.map (List.map Int.ofNat))) (index :: path) := by
        rw [compiled]
        exact .child found tip
      obtain ⟨original, member, same⟩ := List.mem_map.mp (whole.build_member (by simp))
      have equal : original = index :: path := by
        simpa [List.map_map, Function.comp_def] using congrArg (List.map Int.toNat) same
      subst original
      cases traces (index :: path) member with
      | child childTrace =>
          exact Or.inr ⟨available value (List.mem_of_getElem? selected),
            SourceCurrentSecondaryReplay.false_selected childTrace selected⟩

/-- Actual false primary execution retains terminal certificates at its exact returned heap. -/
theorem primary_domain [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {paths : Class} {values : List (Value Symbol Guard)} {before final : State Symbol Guard}
    (trace : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before false final)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Values before values) :
    SemanticReady final ∧ GateReady final ∧ Keeps before final ∧ Values final values ∧
      ForestTips unconstrained final (build (paths.map (List.map Int.ofNat))) values := by
  have anchored := SourceCurrentSecondaryProjectionAnchor.class_anchor unconstrained
    (SourceCurrentPrimaryProjectionSupport.class_false trace) semantic
    (SourceEqualityExposureCosts.gate_ready semantic costs) available
  exact ⟨anchored.1, anchored.2.1, anchored.2.2.1, anchored.2.2.2.1,
    of_paths unconstrained paths values final anchored.2.2.2.1 anchored.2.2.2.2.2⟩

/-- Selected primary certificates retain all tips of the canonical original path union at one heap. -/
theorem selected_domain [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {selected : Constraints} {state : State Symbol Guard}
    (semantic : SemanticReady state) (available : Values state values)
    (primary : ∀ paths ∈ selected,
      EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths state false state) :
    ForestTips unconstrained state (build (SourceEqualitySelectedRequired.paths selected)) values := by
  apply of_paths unconstrained (canonicalClass selected.flatten) values state available
  intro path member
  obtain ⟨paths, included, present⟩ := List.mem_flatten.mp ((mem_canonicalClass _ _).mp member)
  exact SourceCurrentSecondaryReplay.false_class_paths unconstrained values paths state state
    (SourceCurrentPrimaryProjectionSupport.class_false (primary paths included)) semantic available
    state (grows_refl state) path present

/-- Actual ordinary rows retain terminal as well as nonterminal selected child certificates. -/
theorem ordinary_rows [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller : State Symbol Guard}
    {needed : Needed} {entry : Cache.Interned InternedBinderProtocol.NodeKey}
    {edges : List (EdgeValue Symbol Guard)} {depth : Nat} {free : List InternedBinderProtocol.Reference}
    (tips : NodeTips unconstrained anchor needed (.node entry edges depth free))
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady caller)
    (available : Available caller (.node entry edges depth free)) :
    ∀ edge ∈ edges, ForestTips unconstrained anchor needed edge.children := by
  cases needed with
  | node entries =>
      intro edge member index child found value selected path tip
      exact SourceCurrentSecondaryProjectionSupport.ordinary_selected_support
        (tips (index :: path) (.child found tip)) anchorSemantic semantic available edge member value selected

/-- Actual recursive heads retain terminal and nonterminal certificates on their exposed row children. -/
theorem head_rows [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller after : State Symbol Guard}
    {needed : Needed} {original exposed : Value Symbol Guard}
    (tips : NodeTips unconstrained anchor needed original)
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady caller)
    (available : Available caller original) (growth : Grows anchor caller)
    (actual : SourceEqualityRequiredHead.Head original caller exposed after) :
    ∀ edge ∈ InternedEdgeResidency.nodeEdges exposed,
      ForestTips unconstrained anchor needed edge.children := by
  cases needed with
  | node entries =>
      intro edge member index child found value selected path tip
      rcases tips (index :: path) (.child found tip) with closed | ⟨resident, trace⟩
      · have checked := actual.verified semantic.ready available closed
        cases exposed with
        | empty | reference | union | mu => simp [InternedEdgeResidency.nodeEdges] at member
        | node entry edges depth free =>
            exact Or.inl (MergedColdReaderClosed.node_children_closed after
              checked.1.ready.semantic.1.normal.facts entry edges depth free checked.2.1 checked.2.2.1
              edge member value (List.mem_of_getElem? selected))
      · exact SourceCurrentSecondaryProjectionSupport.head_selected_support trace anchorSemantic resident
          semantic available growth actual edge member value selected

end MicroCFTA.SourceCurrentRequiredTipSupport
