import MicroCFTA.SourceCurrentPrimaryProjectionSupport
import MicroCFTA.SourceEqualityRequiredAPI

/-!
# Path-local support for the actual required-path trie

Only maximal stored paths supply gate certificates. A prefix can end at an
open ordinary node. Empty child requirements do not inspect their value.
Actual head exposure transfers each longer certificate to the exact child
positions in the exposed rows. Unselected siblings can remain open.

This module does not assert support for a new reconstructed open record at
the old anchor. It supplies the original-input domains for the next worker
induction.
-/
namespace MicroCFTA.SourceCurrentRequiredSupport
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityRequiredHead
open SourceCurrentSecondaryProjectionSupport (Support)
open InternedGuardedLanguage (meaning)

/-- A maximal stored path follows actual signed lookups and ends at an empty child map. -/
inductive Tip : Needed → EqualityNormalize.Path → Prop where
  | leaf : Tip (.node []) []
  | child (found : SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some needed)
      (rest : Tip needed path) : Tip (.node entries) (index :: path)

/-- Every maximal path is demanded by the actual source trie. -/
theorem Tip.demanded {needed : Needed} {path : EqualityNormalize.Path} (tip : Tip needed path) :
    demands needed (path.map Int.ofNat) = true := by
  induction tip with
  | leaf => rfl
  | child found rest ih => simp only [List.map_cons, demands, found, ih]

/-- A maximal stored path has no demanded strict extension. -/
theorem Tip.extension {needed : Needed} {path : EqualityNormalize.Path} (tip : Tip needed path)
    (suffix : List Int) (required : demands needed (path.map Int.ofNat ++ suffix) = true) : suffix = [] := by
  induction tip with
  | leaf =>
      cases suffix with
      | nil => rfl
      | cons => simp [demands, SourceEqualityNeededMap.lookup] at required
  | child found rest ih =>
      exact ih (by simpa only [List.map_cons, List.cons_append, demands, found] using required)

/-- A nonempty maximal compiled path is one of the exact original source paths. -/
theorem Tip.build_member {paths : List (List Int)} {path : EqualityNormalize.Path}
    (tip : Tip (build paths) path) (nonroot : path ≠ []) : path.map Int.ofNat ∈ paths := by
  rcases (demands_build paths _).mp tip.demanded with root | ⟨original, member, initial⟩
  · exact False.elim (nonroot (List.map_eq_nil_iff.mp root))
  · obtain ⟨suffix, same⟩ := initial
    have demanded : demands (build paths) original = true :=
      (demands_build paths original).mpr (Or.inr ⟨original, member, ⟨[], by simp⟩⟩)
    have emptySuffix := tip.extension suffix (by simpa only [same] using demanded)
    rw [emptySuffix, List.append_nil] at same
    simpa only [← same] using member

/-- Every finite normalized trie has a maximal natural path. -/
theorem tip_exists (needed : Needed) (valid : SourceEqualityNeeded.Valid needed)
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative needed) : ∃ path, Tip needed path := by
  cases shape : needed with
  | node entries =>
      cases entries with
      | nil => exact ⟨[], .leaf⟩
      | cons first rest =>
          obtain ⟨index, child⟩ := first
          have member : (index, child) ∈ (index, child) :: rest := List.mem_cons_self
          have checked : SourceEqualityNeededMap.Ascending ((index, child) :: rest) ∧
              ∀ key next, (key, next) ∈ (index, child) :: rest → SourceEqualityNeeded.Valid next := by
            simpa only [shape, SourceEqualityNeeded.Valid] using valid
          have positive := (show ∀ key next, (key, next) ∈ (index, child) :: rest →
              0 ≤ key ∧ SourceEqualityNeededNonnegative.Nonnegative next from
            by simpa only [shape, SourceEqualityNeededNonnegative.Nonnegative] using nonnegative) index child member
          obtain ⟨path, tip⟩ := tip_exists child (checked.2 index child member) positive.2
          have natural : Int.ofNat index.toNat = index := Int.toNat_of_nonneg positive.1
          exact ⟨index.toNat :: path, .child (by rw [natural]; exact
            SourceEqualityNeededMap.lookup_of_mem index _ child checked.1 member) tip⟩
termination_by sizeOf needed
decreasing_by
  rw [shape]
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- A node needs certificates only for the nonempty maximal paths that its worker visits. -/
def NodeSupport [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (needed : Needed) (value : Value Symbol Guard) : Prop :=
  ∀ path, Tip needed path → path ≠ [] → Support unconstrained anchor path value

/-- Each present selected original child has its own stored requirement's local domain. -/
def ForestSupport [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (needed : Needed) (values : List (Value Symbol Guard)) : Prop :=
  match needed with
  | .node entries => ∀ index child, SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some child →
      ∀ value, values[index]? = some value → NodeSupport unconstrained anchor child value

/-- Actual row children retain their exact original positions and stored child requirements. -/
def RowsSupport [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (needed : Needed) (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ edges, ForestSupport unconstrained anchor needed edge.children

/-- Empty requirements need no certificate, including at unresolved references. -/
theorem empty_support [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (value : Value Symbol Guard) :
    NodeSupport unconstrained anchor (.node []) value := by
  intro path tip nonroot
  cases tip with
  | leaf => exact False.elim (nonroot rfl)
  | child found => simp [SourceEqualityNeededMap.lookup] at found

/-- Primary false class execution derives the compiled forest domain at its actual final heap. -/
theorem primary_domain [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained reaches : Value Symbol Guard → Bool}
    {paths : EqualityNormalize.Class} {values : List (Value Symbol Guard)} {before final : State Symbol Guard}
    (trace : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before false final)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Values before values) :
    SemanticReady final ∧ InternedFreshOrdinaryMemoGateTrace.Ready final ∧ Keeps before final ∧
      Values final values ∧
      ForestSupport unconstrained final (build (paths.map (List.map Int.ofNat))) values := by
  have anchored := SourceCurrentSecondaryProjectionAnchor.class_anchor unconstrained
    (SourceCurrentPrimaryProjectionSupport.class_false trace) semantic
    (SourceEqualityExposureCosts.gate_ready semantic costs) available
  refine ⟨anchored.1, anchored.2.1, anchored.2.2.1, anchored.2.2.2.1, ?_⟩
  cases compiled : build (paths.map (List.map Int.ofNat)) with
  | node entries =>
      intro index child found value selected path tip nonroot
      have whole : Tip (build (paths.map (List.map Int.ofNat))) (index :: path) := by
        rw [compiled]
        exact .child found tip
      have member := whole.build_member (by simp)
      obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
      have originalEqual : original = index :: path := by
        simpa [List.map_map, Function.comp_def] using congrArg (List.map Int.toNat) same
      subst original
      have pathTrace := anchored.2.2.2.2.2 (index :: path) originalMember
      cases pathTrace with
      | child childTrace =>
          exact Or.inr ⟨anchored.2.2.2.1 value (List.mem_of_getElem? selected),
            SourceCurrentSecondaryReplay.false_selected childTrace selected⟩

/-- Ordinary input rows transfer their full-path certificates to the selected child requirements. -/
theorem ordinary_rows [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller : State Symbol Guard}
    {needed : Needed} {entry : Interned InternedBinderProtocol.NodeKey}
    {edges : List (EdgeValue Symbol Guard)} {depth : Nat} {free : List InternedBinderProtocol.Reference}
    (support : NodeSupport unconstrained anchor needed (.node entry edges depth free))
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady caller)
    (available : Available caller (.node entry edges depth free)) :
    RowsSupport unconstrained anchor needed edges := by
  cases needed with
  | node entries =>
      intro edge member index child found value selected path tip nonroot
      exact SourceCurrentSecondaryProjectionSupport.ordinary_selected_support
        (support (index :: path) (.child found tip) (by simp))
        anchorSemantic semantic available edge member value selected

private theorem head_child [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller after : State Symbol Guard}
    {index : Nat} {path : EqualityNormalize.Path} {original exposed : Value Symbol Guard}
    (support : Support unconstrained anchor (index :: path) original)
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady caller)
    (available : Available caller original) (growth : Grows anchor caller)
    (actual : Head original caller exposed after) :
    ∀ edge ∈ InternedEdgeResidency.nodeEdges exposed, ∀ child,
      edge.children[index]? = some child → Support unconstrained anchor path child := by
  rcases support with closed | ⟨resident, trace⟩
  · have checked := actual.verified semantic.ready available closed
    cases exposed with
    | empty | reference | union | mu => simp [InternedEdgeResidency.nodeEdges]
    | node entry edges depth free =>
        intro edge member child selected
        exact Or.inl (MergedColdReaderClosed.node_children_closed after checked.1.ready.semantic.1.normal.facts
          entry edges depth free checked.2.1 checked.2.2.1 edge member child (List.mem_of_getElem? selected))
  · exact SourceCurrentSecondaryProjectionSupport.head_selected_support trace anchorSemantic resident
      semantic available growth actual

/-- Actual recursive head exposure derives every stored child domain without whole-value closedness. -/
theorem head_rows [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller after : State Symbol Guard}
    {needed : Needed} {original exposed : Value Symbol Guard}
    (support : NodeSupport unconstrained anchor needed original)
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady caller)
    (available : Available caller original) (growth : Grows anchor caller)
    (actual : Head original caller exposed after) :
    RowsSupport unconstrained anchor needed (InternedEdgeResidency.nodeEdges exposed) := by
  cases needed with
  | node entries =>
      intro edge member index child found value selected path tip nonroot
      exact head_child (support (index :: path) (.child found tip) (by simp))
        anchorSemantic semantic available growth actual edge member value selected

/-- Nonempty normalized requirements derive finite actual head exposure and exact open language. -/
theorem head_complete [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor caller : State Symbol Guard}
    {entries : List (Int × Needed)} {original : Value Symbol Guard}
    (support : NodeSupport unconstrained anchor (.node entries) original) (nonempty : entries ≠ [])
    (valid : SourceEqualityNeeded.Valid (.node entries))
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative (.node entries))
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady caller)
    (available : Available caller original) (growth : Grows anchor caller) :
    ∃ exposed after, Head original caller exposed after ∧ Keeps caller after ∧ SemanticReady after ∧
      Available after exposed ∧ Ordinary exposed ∧
      RowsSupport unconstrained anchor (.node entries) (InternedEdgeResidency.nodeEdges exposed) ∧
      ∀ holds ambient term, meaning holds ambient exposed term ↔ meaning holds ambient original term := by
  obtain ⟨path, tip⟩ := tip_exists (.node entries) valid nonnegative
  have nonroot : path ≠ [] := by
    intro same
    subst path
    cases tip
    exact nonempty rfl
  have certificate := support path tip nonroot
  have warm := SourceCurrentSecondaryProjectionSupport.support_warm_head certificate anchorSemantic caller growth
  obtain ⟨fuel, edges, middle, read, kept, middleSemantic, resident⟩ :=
    SourceSecondaryGateHead.warm_nodeEdges_complete warm semantic available
  have built := SourceEqualityOpenOrdinaryHead.node edges middle middleSemantic resident
  have actual : Head original caller (run (makeNode edges) middle).1 (run (makeNode edges) middle).2 :=
    .read fuel edges middle read rfl
  refine ⟨_, _, actual, kept.trans built.1, built.2.1, built.2.2.1, built.2.2.2,
    head_rows support anchorSemantic semantic available growth actual, ?_⟩
  intro holds ambient term
  rcases certificate with closed | ⟨resident, trace⟩
  · exact SourceEqualityRequiredHeadLanguage.head_exact actual semantic available closed holds ambient term
  · exact SourceCurrentSecondaryProjectionLanguage.head_exact trace anchorSemantic resident
      semantic available growth actual holds ambient term

end MicroCFTA.SourceCurrentRequiredSupport
