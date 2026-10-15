import MicroCFTA.SourceCurrentClassEditDomains
import MicroCFTA.SourceEqualityEditMeaning
import MicroCFTA.SourceEqualityRequiredHeadLanguage
import MicroCFTA.SourceEqualityEditAPI

/-!
# Independent language of actual class edits with open siblings

Original class paths provide the captured projection domains. The actual
shared leaf derives its target meaning from the stored construction receipt.
Ordinary traversal permits open unselected children. Recursive prefixes use
closedness derived from their retained full edit-path certificates.
-/
namespace MicroCFTA.SourceCurrentClassEditLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityProjectionPathDomain
open SourceCurrentEditDomains SourceCurrentClassEditDomains
open SourceEqualityEdits SourceEqualitySharedEditGraph SourceEqualityEditMeaning
open SourceEqualitySharedEditEffects SourceEqualitySharedTargetState
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)

/-- Child-list edits inspect only selected children and ignore a root callback. -/
def ListSafe (edits : Edits Action) (values : List (Value Symbol Guard)) : Prop :=
  match edits with
  | .editAt _ => True
  | .editBelow entries => ChildrenSafe entries 0 values

/-- A concrete shared native leaf narrows its input language in the captured path domains. -/
theorem leaf_narrows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {input result : Value Symbol Guard} {before after : SharedState width Symbol Guard}
    (actual : SourceEqualitySharedTargetLeaf.Leaf emptyGuard conjoin clear top record originals path input before result after)
    (ready : Ready emptyGuard conjoin clear top record originals base before) (known : Values base originals)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) originals) (member : path ∈ record.paths)
    (available : Available before.native.machine.heap input) (closed : input.free = [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∀ term, meaning holds ambient result term → meaning holds ambient input term := by
  cases actual with
  | apply forced step =>
      have first := forced.path_effects ready known domains member
      have checked := step.verified first.1.native first.2.2.1 (first.2.1.available input available) first.2.2.2.1 closed holds conjoined
      exact fun term accepted => ((checked.2.2.2.2 ambient term).mp accepted).1

/-- A concrete shared native leaf retains an accepted subterm of its captured satisfied class. -/
theorem leaf_keeps_term [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {input result : Value Symbol Guard} {before after : SharedState width Symbol Guard}
    (actual : SourceEqualitySharedTargetLeaf.Leaf emptyGuard conjoin clear top record originals path input before result after)
    (ready : Ready emptyGuard conjoin clear top record originals base before) (known : Values base originals)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) originals) (member : path ∈ record.paths)
    (available : Available before.native.machine.heap input) (closed : input.free = [])
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) originals terms)
    (satisfied : EqualityNormalize.ClassSat (.node symbol terms) record.paths)
    (selected : (Term.node symbol terms).atPath path = some part) (inputAccepted : meaning holds ambient input part) :
    meaning holds ambient result part := by
  cases actual with
  | apply forced step =>
      have first := forced.path_effects ready known domains member
      have targetAccepted := (first.1.receipts path _ first.2.2.2.2.1).included_path coherent active domains
        holds ambient clearTrue topTrue conjoined symbol terms part accepted satisfied selected
      have checked := step.verified first.1.native first.2.2.1 (first.2.1.available input available) first.2.2.2.1 closed holds conjoined
      exact (checked.2.2.2.2 ambient part).mpr ⟨inputAccepted, targetAccepted⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
variable (known : Values base originals)
variable (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)
variable (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
variable (root : Term Symbol)
variable (rootSymbol : Symbol) (rootTerms : List (Term Symbol))
local notation "condition" => fun path part => root.atPath path = some part

private def NodeBounds (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before : SharedState width Symbol Guard) (result : Value Symbol Guard) : Prop :=
  SourceEqualityEdits.Valid edits → Populated edits → HasLeaf edits → Allowed record edits → Ready emptyGuard conjoin clear top record originals base before →
    Available before.native.machine.heap value → Safe edits value → ∀ term,
      (meaning holds ambient result term → meaning holds ambient value term) ∧
      (All₂ (meaning holds ambient) originals rootTerms → EqualityNormalize.ClassSat root record.paths →
        Matches condition edits term → meaning holds ambient value term → meaning holds ambient result term)

private def ChildrenBounds (entries : List (Int × Edits EqualityNormalize.Path)) (index : Nat) (values : List (Value Symbol Guard))
    (before : SharedState width Symbol Guard) (results : List (Value Symbol Guard)) : Prop :=
  SourceEqualityEdits.Valid (.editBelow entries) → Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Values before.native.machine.heap values → ChildrenSafe entries index values → ∀ terms,
      (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      (All₂ (meaning holds ambient) originals rootTerms → EqualityNormalize.ClassSat root record.paths →
        Forest condition entries index terms → All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms)

private def RowsBounds (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before : SharedState width Symbol Guard) (results : List (EdgeValue Symbol Guard)) : Prop :=
  SourceEqualityEdits.Valid (.editBelow entries) → Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Edges before.native.machine.heap edges → RowsSafe entries edges → ∀ term,
      ((∃ edge ∈ results, EdgeMeaning (meaning holds ambient) holds edge term) → ∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term) ∧
      (All₂ (meaning holds ambient) originals rootTerms → EqualityNormalize.ClassSat root record.paths →
        Matches condition (.editBelow entries) term → (∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term) →
        ∃ edge ∈ results, EdgeMeaning (meaning holds ambient) holds edge term)

local notation "NodeLaw" => NodeBounds (width := width) emptyGuard conjoin clear top record originals base holds ambient root rootTerms
local notation "ChildrenLaw" => ChildrenBounds (width := width) emptyGuard conjoin clear top record originals base holds ambient root rootTerms
local notation "RowsLaw" => RowsBounds (width := width) emptyGuard conjoin clear top record originals base holds ambient root rootTerms

variable (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
variable (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
variable (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
variable (rootSame : root = .node rootSymbol rootTerms)

include known domains coherent active clearTrue topTrue conjoined rootSymbol rootTerms rootSame

private theorem bounds :
    (∀ edits (value : Value Symbol Guard) before result after,
      EditNode emptyGuard conjoin clear top record originals edits value before result after → NodeLaw edits value before result) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after,
      EditChildren emptyGuard conjoin clear top record originals entries index values before results after → ChildrenLaw entries index values before results) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      EditRows emptyGuard conjoin clear top record originals entries edges before results after → RowsLaw entries edges before results) := by
  have leafCase : ∀ {path value before result after},
      SourceEqualitySharedTargetLeaf.Leaf emptyGuard conjoin clear top record originals path value before result after → NodeLaw (.editAt path) value before result := by
    intro path value before result after trace _ _ _ allowed ready available safe term
    have closed : value.free = [] := by simpa only [NodeClosed] using safe [] path (by simp [SourceEqualityEditLeafPaths.leaves])
    have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
    refine ⟨leaf_narrows trace ready known domains member available closed holds ambient conjoined term, ?_⟩
    intro accepted satisfied matched original
    exact leaf_keeps_term trace ready known domains member available closed coherent active holds ambient clearTrue topTrue conjoined
      rootSymbol rootTerms term accepted (by simpa only [rootSame] using satisfied) (by simpa only [Matches, rootSame] using matched) original
  have emptyCase : ∀ {entries : List (Int × Edits EqualityNormalize.Path)} {state},
      NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state .empty := by
    intro entries state _ _ _ _ _ _ _ term
    exact ⟨id, fun _ _ _ accepted => accepted⟩
  have ordinaryCase : ∀ {entries edges before rebuilt middle result heap entry depth free},
      EditRows emptyGuard conjoin clear top record originals entries edges before rebuilt middle → run (makeNode rebuilt) middle.native.machine.heap = (result, heap) →
      RowsLaw entries edges before rebuilt → NodeLaw (.editBelow entries) (.node entry edges depth free) before result := by
    intro entries edges before rebuilt middle result heap entry depth free trace rebuiltEq rowsIH valid populated _ allowed ready available safe term
    have facts := ready.native.semantic.ready.semantic.1.normal.facts
    have resident : Edges before.native.machine.heap edges := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
    have rowsSafe := ordinary_rows safe
    have checked := SourceCurrentClassEditDomains.rows_domains emptyGuard conjoin clear top record originals base known domains trace populated allowed ready resident rowsSafe
    have actual := MergedColdInterpretation.makeNode_exact middle.native.machine.heap checked.1.native.semantic.ready.semantic.1.normal.facts
      (meaning holds ambient) rebuilt checked.2.2.1 holds (InternedGuardedLanguage.laws holds ambient) term
    have readback : meaning holds ambient result term ↔ ∃ edge ∈ rebuilt, EdgeMeaning (meaning holds ambient) holds edge term := by simpa only [rebuiltEq] using actual
    have rows := rowsIH valid populated allowed ready resident rowsSafe term
    rw [readback, (InternedGuardedLanguage.laws holds ambient).node entry edges depth free term]
    exact rows
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
      EditNode emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) result after →
      NodeLaw (.editBelow entries) exposed (advanceHeap before heap) result → NodeLaw (.editBelow entries) original before result := by
    intro entries original before exposed heap result after recursive trace _ ih valid populated nonempty allowed ready available safe term
    have closed := recursive_closed recursive nonempty safe
    have nextSemantic := SourceEqualityRequiredSemanticCache.head trace ready.native.semantic available closed
    have checked := trace.verified ready.native.semantic.ready available closed
    have body := ih valid populated nonempty allowed (ready.heap heap checked.1 nextSemantic) checked.2.1
      (closed_safe _ exposed heap nextSemantic checked.2.1 checked.2.2.1) term
    rw [← SourceEqualityRequiredHeadLanguage.head_exact trace ready.native.semantic available closed holds ambient term]
    exact body
  have nilChildren : ∀ {entries index state}, ChildrenLaw entries index ([] : List (Value Symbol Guard)) state [] := by
    intro entries index state _ _ _ _ _ _ terms
    exact ⟨id, fun _ _ _ accepted => accepted⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      EditChildren emptyGuard conjoin clear top record originals entries (index + 1) values before results after → ChildrenLaw entries (index + 1) values before results →
      ChildrenLaw entries index (value :: values) before (value :: results) := by
    intro entries values before results after value index absent _ restIH valid populated allowed ready available safe terms
    have tail := restIH valid populated allowed ready (fun child member => available child (List.mem_cons_of_mem _ member))
      (children_tail safe)
    cases terms with
    | nil =>
        constructor
        · intro impossible; cases impossible
        · intro _ _ _ impossible; cases impossible
    | cons term terms =>
        constructor
        · intro run
          cases run with
          | cons first rest => exact .cons first ((tail terms).1 rest)
        · intro accepted satisfied matched run
          cases run with
          | cons first rest => exact .cons first ((tail terms).2 accepted satisfied matched.2 rest)
  have selectedCase : ∀ {entries edits value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits →
      EditNode emptyGuard conjoin clear top record originals edits value before result middle → EditChildren emptyGuard conjoin clear top record originals entries (index + 1) values middle results after →
      NodeLaw edits value before result → ChildrenLaw entries (index + 1) values middle results → ChildrenLaw entries index (value :: values) before (result :: results) := by
    intro entries edits value before result middle values results after index found first _ firstIH restIH valid populated allowed ready available safe terms
    have member := SourceEqualityNeededMap.lookup_mem _ entries edits found
    have childValid : SourceEqualityEdits.Valid edits := by rw [SourceEqualityEdits.Valid] at valid; exact valid.2 _ _ member
    have childAllowed : Allowed record edits := by rw [Allowed, All] at allowed; exact allowed _ _ member
    have firstAvailable := available value List.mem_cons_self
    have childPopulated := (show ∀ key child, (key, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ member
    have firstSafe := safe 0 _ (by simpa using found) value rfl
    have checked := SourceCurrentClassEditDomains.node_domains emptyGuard conjoin clear top record originals base known domains first
      childPopulated.1 childPopulated.2 childAllowed ready firstAvailable firstSafe
    have tail := restIH valid populated allowed checked.1
      (fun child member => checked.2.1.available child (available child (List.mem_cons_of_mem _ member)))
      (children_tail safe)
    have head := firstIH childValid childPopulated.1 childPopulated.2 childAllowed ready firstAvailable firstSafe
    cases terms with
    | nil =>
        constructor
        · intro impossible; cases impossible
        · intro _ _ _ impossible; cases impossible
    | cons term terms =>
        constructor
        · intro run
          cases run with
          | cons initial rest => exact .cons ((head term).1 initial) ((tail terms).1 rest)
        · intro accepted satisfied matched run
          cases run with
          | cons initial rest => exact .cons ((head term).2 accepted satisfied (matched.1 edits found) initial) ((tail terms).2 accepted satisfied matched.2 rest)
  have nilRows : ∀ {entries state}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) state [] := by
    intro entries state _ _ _ _ _ _ term
    exact ⟨id, fun _ _ _ accepted => accepted⟩
  have consCase : ∀ {entries before values middle result heap edges results after edge},
      EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap) →
      EditRows emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after → ChildrenLaw entries 0 edge.children before values →
      RowsLaw entries edges (advanceHeap middle heap) results → RowsLaw entries (edge :: edges) before (result :: results) := by
    intro entries before values middle result heap edges results after edge childTrace rebuilt _ childIH restIH valid populated allowed ready resident safe term
    have facts := ready.native.semantic.ready.semantic.1.normal.facts
    have available : Values before.native.machine.heap edge.children := facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    have checked := SourceCurrentClassEditDomains.children_domains emptyGuard conjoin clear top record originals base known domains childTrace populated allowed ready available (safe edge List.mem_cons_self)
    have edgeSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap checked.1.native.semantic checked.2.2.1
    have edgeChecked := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap checked.1.native.semantic.ready checked.2.2.1
    have heapSemantic : SemanticReady heap := by simpa only [rebuilt] using edgeSemantic
    have edgeKeeps : Keeps middle.native.machine.heap heap := by simpa only [rebuilt] using edgeChecked.1
    have firstKeeps := checked.2.1.trans edgeKeeps
    have tail := restIH valid populated allowed (checked.1.heap heap edgeKeeps heapSemantic)
      (fun original member => InternedEdgeResidency.edge_grows before.native.machine.heap heap firstKeeps.growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) term
    have child := childIH valid populated allowed ready available (safe edge List.mem_cons_self)
    have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.native.machine.heap checked.1.native.semantic.ready.semantic.1.normal.facts
      edge.entry.key.symbol edge.entry.key.constraint values checked.2.2.1
    have actualFields : result.entry.key.symbol = edge.entry.key.symbol ∧ result.entry.key.constraint = edge.entry.key.constraint ∧ result.children = values := by simpa only [rebuilt] using fields
    have ordered := (show SourceEqualityNeededMap.Ascending entries ∧ _ from (by simpa only [SourceEqualityEdits.Valid] using valid)).1
    have head : (EdgeMeaning (meaning holds ambient) holds result term → EdgeMeaning (meaning holds ambient) holds edge term) ∧
        (All₂ (meaning holds ambient) originals rootTerms → EqualityNormalize.ClassSat root record.paths → Matches condition (.editBelow entries) term → EdgeMeaning (meaning holds ambient) holds edge term → EdgeMeaning (meaning holds ambient) holds result term) := by
      unfold EdgeMeaning
      rw [actualFields.1, actualFields.2.1, actualFields.2.2]
      constructor
      · rintro ⟨terms, shape, runs, guard⟩
        exact ⟨terms, shape, (child terms).1 runs, guard⟩
      · rintro accepted satisfied matched ⟨terms, shape, runs, guard⟩
        have required := (forest_zero condition entries ordered edge.entry.key.symbol terms).mpr (by simpa only [shape] using matched)
        exact ⟨terms, shape, (child terms).2 accepted satisfied required runs, guard⟩
    constructor
    · rintro ⟨output, member, run⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨edge, List.mem_cons_self, head.1 run⟩
      · obtain ⟨original, member, run⟩ := tail.1 ⟨output, member, run⟩
        exact ⟨original, List.mem_cons_of_mem _ member, run⟩
    · rintro accepted satisfied matched ⟨original, member, run⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨result, List.mem_cons_self, head.2 accepted satisfied matched run⟩
      · obtain ⟨output, member, run⟩ := tail.2 accepted satisfied matched ⟨original, member, run⟩
        exact ⟨output, List.mem_cons_of_mem _ member, run⟩
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before result after trace
    exact EditNode.rec (motive_1 := fun edits value before result _ _ => NodeLaw edits value before result)
      (motive_2 := fun entries index values before results _ _ => ChildrenLaw entries index values before results)
      (motive_3 := fun entries edges before results _ _ => RowsLaw entries edges before results)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace
  · intro entries index values before results after trace
    exact EditChildren.rec (motive_1 := fun edits value before result _ _ => NodeLaw edits value before result)
      (motive_2 := fun entries index values before results _ _ => ChildrenLaw entries index values before results)
      (motive_3 := fun entries edges before results _ _ => RowsLaw entries edges before results)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace
  · intro entries edges before results after trace
    exact EditRows.rec (motive_1 := fun edits value before result _ _ => NodeLaw edits value before result)
      (motive_2 := fun entries index values before results _ _ => ChildrenLaw entries index values before results)
      (motive_3 := fun entries edges before results _ _ => RowsLaw entries edges before results)
      leafCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase (fun {_ _} => nilRows) consCase trace

/-- Node traversal derives language inclusion and retention under original path readback. -/
theorem node {edits value before result after} (trace : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after) :
    NodeLaw edits value before result :=
  (bounds emptyGuard conjoin clear top record originals base known domains holds ambient root rootSymbol rootTerms coherent active clearTrue topTrue conjoined rootSame).1 _ _ _ _ _ trace

/-- Child traversal derives ordered forest inclusion and retention under original path readback. -/
theorem children {entries index values before results after}
    (trace : EditChildren (width := width) emptyGuard conjoin clear top record originals entries index values before results after) : ChildrenLaw entries index values before results :=
  (bounds emptyGuard conjoin clear top record originals base known domains holds ambient root rootSymbol rootTerms coherent active clearTrue topTrue conjoined rootSame).2.1 _ _ _ _ _ _ trace

/-- Row traversal derives inclusion and conditional retention for accepted terms. -/
theorem rows {entries edges before results after}
    (trace : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after) : RowsLaw entries edges before results :=
  (bounds emptyGuard conjoin clear top record originals base known domains holds ambient root rootSymbol rootTerms coherent active clearTrue topTrue conjoined rootSame).2.2 _ _ _ _ _ trace

/-- Source child-list edits retain ordered language bounds and ignore root callbacks. -/
theorem list {edits values before results after}
    (trace : EditList (width := width) emptyGuard conjoin clear top record originals edits values before results after)
    (valid : SourceEqualityEdits.Valid edits) (populated : Populated edits) (allowed : Allowed record edits) (ready : Ready emptyGuard conjoin clear top record originals base before)
    (available : Values before.native.machine.heap values)
    (safe : ListSafe edits values) :
    ∀ terms, (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      (All₂ (meaning holds ambient) originals rootTerms → EqualityNormalize.ClassSat root record.paths →
        SourceEqualityEditAPI.ListCondition condition edits terms → All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  cases trace with
  | leaf => exact fun _ => ⟨id, fun _ _ _ accepted => accepted⟩
  | children trace =>
      exact children emptyGuard conjoin clear top record originals base known domains holds ambient root rootSymbol rootTerms
        coherent active clearTrue topTrue conjoined rootSame trace valid populated allowed ready available safe

end MicroCFTA.SourceCurrentClassEditLanguage

namespace MicroCFTA.SourceCurrentClassEditLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualitySharedTargetState
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualitySharedEditGraph SourceEqualitySharedEditEffects
open SourceEqualityProjectionPathDomain SourceCurrentEditDomains
open InternedGuardedLanguage (meaning)

/-- A concrete source class narrows its forest and retains every accepted class-satisfying term with open siblings. -/
theorem class_language [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (actual : SourceEqualityClassFoldGraph.Class emptyGuard conjoin clear top record values before results after)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (symbol : Symbol) (terms : List (Term Symbol)) :
    (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      (EqualityNormalize.ClassSat (.node symbol terms) record.paths →
        All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms) := by
  have supported := SourceEqualityClassEdits.coherent_supported record coherent
  have disjoint := SourceEqualityClassEdits.edits_disjoint record.paths supported id
  have matched : SourceEqualityEditAPI.ListCondition (fun path part => (Term.node symbol terms).atPath path = some part)
      (build (SourceEqualityClassEdits.edits record.paths id)) terms := by
    apply (SourceEqualityEditCompiledPaths.list_condition_exact _ _ disjoint
      (SourceEqualityClassEdits.edits_nonroot record.paths (SourceEqualityClassEdits.supported_nonroot record.paths supported active) id)
      symbol terms).mpr
    exact (SourceEqualityClassEdits.conditions_exact _ record.paths id (.node symbol terms)).mpr (fun _ _ _ selected => selected)
  have safe : ListSafe (build (SourceEqualityClassEdits.edits record.paths id)) values := by
    cases compiled : build (SourceEqualityClassEdits.edits record.paths id) with
    | editAt target => trivial
    | editBelow entries =>
        intro query child found value selected path action retained
        have member : (Int.ofNat query :: path, action) ∈ leaves (build (SourceEqualityClassEdits.edits record.paths id)) := by
          rw [compiled]
          exact below_member _ _ _ (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) _ _ retained
        obtain ⟨original, included, same⟩ := List.mem_map.mp ((SourceEqualityEditCompiledPaths.build_leaves _ disjoint).mem_iff.mp member)
        have domain := domains original included
        have same := congrArg Prod.fst same
        dsimp at same
        rw [same] at domain
        apply domain value
        change SourceEqualityProjectionGraph.select values (Int.ofNat query) = some value
        rw [select_natural]
        exact selected
  cases actual with
  | edit actual =>
      have initialReady := initial_ready emptyGuard conjoin clear top record values before.machine.heap before ready (pure_keeps _ ready.semantic.ready)
      have bounds := list emptyGuard conjoin clear top record values before.machine.heap available domains holds ambient
        (.node symbol terms) symbol terms coherent active clearTrue topTrue conjoined rfl actual
        (build_valid _) (build_populated _) (SourceEqualitySharedClassEdits.compiled_allowed record)
        initialReady available safe terms
      exact ⟨bounds.1, fun satisfied accepted => bounds.2 accepted satisfied matched accepted⟩

end MicroCFTA.SourceCurrentClassEditLanguage
