import MicroCFTA.SourceCurrentAllocatedSharedEditEffects
import MicroCFTA.SourceEqualityEditMeaning
import MicroCFTA.SourceEqualityRequiredHeadLanguage
import MicroCFTA.SourceEqualityEditAPI

/-!
# Independent language of checked simultaneous edits

Actual read receipts supply each reached checked leaf result. Ordinary
traversal retains open unselected children. Recursive prefixes use closedness
from the original edit-path domain. No callback language law is supplied.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedEditLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityProjectionPathDomain SourceCurrentEditDomains
open SourceEqualityEdits SourceEqualityEditMeaning SourceEqualitySharedEditEffects
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "MemoValid" => EndpointMemoGateTrace.Valid

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (base : Heap) (record : SourceEqualityClassOrder.Record)
variable (originals : List (Value Symbol Guard))
variable (ambient : InternedGuardedLanguage.Env Symbol)
variable (rootSymbol : Symbol) (rootTerms : List (Term Symbol))
local notation "holds" => SourceEqualityPCSGuard.holds formulas solver
local notation "root" => Term.node rootSymbol rootTerms
local notation "condition" => fun path part => Term.atPath (Term.node rootSymbol rootTerms) path = some part

private def NodeBounds (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before : SharedState width) (result : Value Symbol Guard) (memos : Memos) : Prop :=
  SourceEqualityEdits.Valid edits → Populated edits → HasLeaf edits → Allowed record edits →
    ∀ inventory, Ready formulas solver inventory record originals base before →
      Available before.checked.native.machine.heap value → Safe edits value →
      MemoValid before.checked.native.machine.heap memos → ∀ term,
        (meaning holds ambient result term → meaning holds ambient value term) ∧
        (All₂ (meaning holds ambient) originals rootTerms → EqualityNormalize.ClassSat root record.paths →
          Matches condition edits term → meaning holds ambient value term → meaning holds ambient result term)

private def ChildrenBounds (entries : List (Int × Edits EqualityNormalize.Path)) (index : Nat)
    (values : List (Value Symbol Guard)) (before : SharedState width)
    (results : List (Value Symbol Guard)) (memos : Memos) : Prop :=
  SourceEqualityEdits.Valid (.editBelow entries) → Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    ∀ inventory, Ready formulas solver inventory record originals base before →
      Values before.checked.native.machine.heap values → ChildrenSafe entries index values →
      MemoValid before.checked.native.machine.heap memos → ∀ terms,
        (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
        (All₂ (meaning holds ambient) originals rootTerms → EqualityNormalize.ClassSat root record.paths →
          Forest condition entries index terms → All₂ (meaning holds ambient) values terms → All₂ (meaning holds ambient) results terms)

private def RowsBounds (entries : List (Int × Edits EqualityNormalize.Path))
    (edges : List (EdgeValue Symbol Guard)) (before : SharedState width)
    (results : List (EdgeValue Symbol Guard)) (memos : Memos) : Prop :=
  SourceEqualityEdits.Valid (.editBelow entries) → Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    ∀ inventory, Ready formulas solver inventory record originals base before →
      Edges before.checked.native.machine.heap edges → RowsSafe entries edges →
      MemoValid before.checked.native.machine.heap memos → ∀ term,
        ((∃ edge ∈ results, EdgeMeaning (meaning holds ambient) holds edge term) →
          ∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term) ∧
        (All₂ (meaning holds ambient) originals rootTerms → EqualityNormalize.ClassSat root record.paths →
          Matches condition (.editBelow entries) term →
          (∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term) →
          ∃ edge ∈ results, EdgeMeaning (meaning holds ambient) holds edge term)

local notation "NodeLaw" => NodeBounds (width := width) formulas solver base
local notation "ChildrenLaw" => ChildrenBounds (width := width) formulas solver base
local notation "RowsLaw" => RowsBounds (width := width) formulas solver base

private theorem bounds :
    (∀ {record originals edits value before result after} {actual : EditNode record originals edits value before result after} {memos final},
      NodeReads formulas solver base actual memos final → NodeLaw record originals ambient rootSymbol rootTerms edits value before result memos) ∧
    (∀ {record originals entries index values before results after} {actual : EditChildren record originals entries index values before results after} {memos final},
      ChildrenReads formulas solver base actual memos final → ChildrenLaw record originals ambient rootSymbol rootTerms entries index values before results memos) ∧
    (∀ {record originals entries edges before results after} {actual : EditRows record originals entries edges before results after} {memos final},
      RowsReads formulas solver base actual memos final → RowsLaw record originals ambient rootSymbol rootTerms entries edges before results memos) := by
  have leafCase : ∀ {next record originals path value before result after memos saved}
      (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals base path
        value before result after memos saved), NodeLaw record originals ambient rootSymbol rootTerms (.editAt path) value before result memos := by
    intro next record originals path value before result after memos saved receipt _ _ _ _ _ _ _ _ _ term
    refine ⟨receipt.narrows ambient term, ?_⟩
    intro accepted satisfied matched original
    exact receipt.preserves ambient rootSymbol rootTerms term accepted satisfied (by simpa only [Matches] using matched) original
  have emptyCase : ∀ {record originals entries state memos},
      NodeLaw record originals ambient rootSymbol rootTerms (.editBelow entries) (.empty : Value Symbol Guard) state .empty memos := by
    intro record originals entries state memos _ _ _ _ _ _ _ _ _ term
    exact ⟨id, fun _ _ _ accepted => accepted⟩
  have ordinaryCase : ∀ {record originals memos saved entries edges before rebuilt middle value heap entry depth free}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)},
      RowsReads formulas solver base actual memos saved → RowsLaw record originals ambient rootSymbol rootTerms entries edges before rebuilt memos →
      NodeLaw record originals ambient rootSymbol rootTerms (.editBelow entries) (.node entry edges depth free) before value memos := by
    intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built read ih
      valid populated _ allowed inventory ready available safe memoValid term
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident : Edges before.checked.native.machine.heap edges := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
    have rowsSafe := ordinary_rows safe
    obtain ⟨next, checked⟩ := rows_effects read populated allowed ready resident rowsSafe memoValid
    have actual := MergedColdInterpretation.makeNode_exact middle.checked.native.machine.heap
      checked.ready.checked.semantic.ready.semantic.1.normal.facts
      (meaning holds ambient) rebuilt checked.available holds (InternedGuardedLanguage.laws holds ambient) term
    have readback : meaning holds ambient value term ↔ ∃ edge ∈ rebuilt, EdgeMeaning (meaning holds ambient) holds edge term := by
      simpa only [built] using actual
    rw [readback, (InternedGuardedLanguage.laws holds ambient).node entry edges depth free term]
    exact ih valid populated allowed inventory ready resident rowsSafe memoValid term
  have recursiveCase : ∀ {record originals memos middle saved entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after},
      SourceCurrentRequiredQueryMemos.HeadReads head memos middle →
      SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap heap memos middle →
      NodeReads formulas solver base body middle saved →
      NodeLaw record originals ambient rootSymbol rootTerms (.editBelow entries) exposed (advanceHeap before heap) value middle →
      NodeLaw record originals ambient rootSymbol rootTerms (.editBelow entries) original before value memos := by
    intro record originals memos middle saved entries original before exposed heap value after recursive head body _ headGlobal _ ih
      valid populated nonempty allowed inventory ready available safe memoValid term
    have closed := recursive_closed recursive nonempty safe
    have first := head_physical ready head available
    have checked := head.verified ready.checked.semantic.ready available closed
    have body := ih valid populated nonempty allowed inventory first.1 first.2.2
      (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1)
      headGlobal.valid term
    rw [← SourceEqualityRequiredHeadLanguage.head_exact head ready.checked.semantic available closed holds ambient term]
    exact body
  have nilChildren : ∀ {record originals entries index state memos},
      ChildrenLaw record originals ambient rootSymbol rootTerms entries index ([] : List (Value Symbol Guard)) state [] memos := by
    intro record originals entries index state memos _ _ _ _ _ _ _ _ terms
    exact ⟨id, fun _ _ _ accepted => accepted⟩
  have unselectedCase : ∀ {record originals memos saved entries values before results after value} {index : Nat}
      {absent : SourceEqualityNeededMap.lookup (index : Int) entries = none}
      {rest : EditChildren record originals entries (index + 1) values before results after},
      ChildrenReads formulas solver base rest memos saved → ChildrenLaw record originals ambient rootSymbol rootTerms entries (index + 1) values before results memos →
      ChildrenLaw record originals ambient rootSymbol rootTerms entries index (value :: values) before (value :: results) memos := by
    intro record originals memos saved entries values before results after value index absent rest _ ih
      valid populated allowed inventory ready available safe memoValid terms
    have tail := ih valid populated allowed inventory ready
      (fun child member => available child (List.mem_cons_of_mem _ member)) (children_tail safe) memoValid
    cases terms with
    | nil =>
        constructor
        · intro impossible; cases impossible
        · intro _ _ _ impossible; cases impossible
    | cons term terms =>
        constructor
        · intro accepted
          cases accepted with
          | cons first rest => exact .cons first ((tail terms).1 rest)
        · intro accepted satisfied matched run
          cases run with
          | cons first rest => exact .cons first ((tail terms).2 accepted satisfied matched.2 rest)
  have selectedCase : ∀ {record originals memos current saved entries edits value before result middle values results after} {index : Nat}
      {found : SourceEqualityNeededMap.lookup (index : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (index + 1) values middle results after},
      NodeReads formulas solver base first memos current → ChildrenReads formulas solver base rest current saved →
      NodeLaw record originals ambient rootSymbol rootTerms edits value before result memos → ChildrenLaw record originals ambient rootSymbol rootTerms entries (index + 1) values middle results current →
      ChildrenLaw record originals ambient rootSymbol rootTerms entries index (value :: values) before (result :: results) memos := by
    intro record originals memos current saved entries edits value before result middle values results after index found first rest firstRead _ firstIH restIH
      valid populated allowed inventory ready available safe memoValid terms
    have member := SourceEqualityNeededMap.lookup_mem _ entries edits found
    have childValid : SourceEqualityEdits.Valid edits := by rw [SourceEqualityEdits.Valid] at valid; exact valid.2 _ _ member
    have childAllowed : Allowed record edits := by rw [Allowed, All] at allowed; exact allowed _ _ member
    have firstAvailable := available value List.mem_cons_self
    have childPopulated := (show ∀ key child, (key, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ member
    have firstSafe := safe 0 _ (by simpa using found) value rfl
    obtain ⟨next, checked⟩ := node_effects firstRead childPopulated.1 childPopulated.2 childAllowed ready firstAvailable firstSafe memoValid
    have tail := restIH valid populated allowed next checked.ready
      (fun child member => checked.effects.keeps.available child (available child (List.mem_cons_of_mem _ member)))
      (children_tail safe) checked.globals.valid
    have head := firstIH childValid childPopulated.1 childPopulated.2 childAllowed inventory ready firstAvailable firstSafe memoValid
    cases terms with
    | nil =>
        constructor
        · intro impossible; cases impossible
        · intro _ _ _ impossible; cases impossible
    | cons term terms =>
        constructor
        · intro accepted
          cases accepted with
          | cons first rest => exact .cons ((head term).1 first) ((tail terms).1 rest)
        · intro accepted satisfied matched run
          cases run with
          | cons first rest =>
              exact .cons ((head term).2 accepted satisfied (matched.1 edits found) first)
                ((tail terms).2 accepted satisfied matched.2 rest)
  have nilRows : ∀ {record originals entries state memos}, RowsLaw record originals ambient rootSymbol rootTerms entries ([] : List (EdgeValue Symbol Guard)) state [] memos := by
    intro record originals entries state memos _ _ _ _ _ _ _ _ term
    exact ⟨id, fun _ _ _ accepted => accepted⟩
  have consCase : ∀ {record originals memos current saved entries before values middle result heap edges results after edge}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after},
      ChildrenReads formulas solver base children memos current → RowsReads formulas solver base rest current saved →
      ChildrenLaw record originals ambient rootSymbol rootTerms entries 0 edge.children before values memos → RowsLaw record originals ambient rootSymbol rootTerms entries edges (advanceHeap middle heap) results current →
      RowsLaw record originals ambient rootSymbol rootTerms entries (edge :: edges) before (result :: results) memos := by
    intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest firstRead _ childIH restIH
      valid populated allowed inventory ready resident safe memoValid term
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have available : Values before.checked.native.machine.heap edge.children := facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
    obtain ⟨next, checked⟩ := children_effects firstRead populated allowed ready available (safe edge List.mem_cons_self) memoValid
    have field := (SourceEqualityAnnotationHeap.edge _ _ ready.checked.good.fields facts edge (resident edge List.mem_cons_self)).1
    have currentField := field.grows checked.effects.grows
    have physical := edge_physical checked.ready edge.entry.key.symbol edge.entry.key.constraint values currentField checked.available
    have edgeReady : Ready formulas solver next record originals base (advanceHeap middle heap) := by simpa only [rebuilt] using physical.1
    have edgeEffects : SourceCurrentConjunctionRowsAllocation.Effects
        (SourceCurrentAllocatedNativeEffects.physical middle.checked)
        (SourceCurrentAllocatedNativeEffects.physical (advanceHeap middle heap).checked) := by simpa only [rebuilt] using physical.2.1
    have firstKeeps := checked.effects.keeps.trans edgeEffects.keeps
    have tail := restIH valid populated allowed next edgeReady
      (fun original member => InternedEdgeResidency.edge_grows _ _ firstKeeps.growth original
        (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member))
      (SourceQueryUnfoldMemo.valid_grows _ _ checked.ready.checked.semantic edgeEffects.keeps _ checked.globals.valid) term
    have child := childIH valid populated allowed inventory ready available (safe edge List.mem_cons_self) memoValid
    have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.checked.native.machine.heap
      checked.ready.checked.semantic.ready.semantic.1.normal.facts edge.entry.key.symbol edge.entry.key.constraint values checked.available
    have actualFields : result.entry.key.symbol = edge.entry.key.symbol ∧ result.entry.key.constraint = edge.entry.key.constraint ∧ result.children = values := by
      simpa only [rebuilt] using fields
    have ordered := (show SourceEqualityNeededMap.Ascending entries ∧ _ from (by simpa only [SourceEqualityEdits.Valid] using valid)).1
    have head : (EdgeMeaning (meaning holds ambient) holds result term → EdgeMeaning (meaning holds ambient) holds edge term) ∧
        (All₂ (meaning holds ambient) originals rootTerms → EqualityNormalize.ClassSat root record.paths →
          Matches condition (.editBelow entries) term → EdgeMeaning (meaning holds ambient) holds edge term → EdgeMeaning (meaning holds ambient) holds result term) := by
      unfold EdgeMeaning
      rw [actualFields.1, actualFields.2.1, actualFields.2.2]
      constructor
      · rintro ⟨terms, shape, runs, guard⟩
        exact ⟨terms, shape, (child terms).1 runs, guard⟩
      · rintro accepted satisfied matched ⟨terms, shape, runs, guard⟩
        have required := (forest_zero condition entries ordered edge.entry.key.symbol terms).mpr (by simpa only [shape] using matched)
        exact ⟨terms, shape, (child terms).2 accepted satisfied required runs, guard⟩
    constructor
    · rintro ⟨output, member, accepted⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨edge, List.mem_cons_self, head.1 accepted⟩
      · obtain ⟨original, member, accepted⟩ := tail.1 ⟨output, member, accepted⟩
        exact ⟨original, List.mem_cons_of_mem _ member, accepted⟩
    · rintro accepted satisfied matched ⟨original, member, present⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨result, List.mem_cons_self, head.2 accepted satisfied matched present⟩
      · obtain ⟨output, member, present⟩ := tail.2 accepted satisfied matched ⟨original, member, present⟩
        exact ⟨output, List.mem_cons_of_mem _ member, present⟩
  refine ⟨?_, ?_, ?_⟩
  · intro record originals edits value before result after actual memos final read
    exact NodeReads.rec (motive_1 := fun {record originals edits value before result after} _ memos _ _ => NodeLaw record originals ambient rootSymbol rootTerms edits value before result memos)
      (motive_2 := fun {record originals entries index values before results after} _ memos _ _ => ChildrenLaw record originals ambient rootSymbol rootTerms entries index values before results memos)
      (motive_3 := fun {record originals entries edges before results after} _ memos _ _ => RowsLaw record originals ambient rootSymbol rootTerms entries edges before results memos)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase read
  · intro record originals entries index values before results after actual memos final read
    exact ChildrenReads.rec (motive_1 := fun {record originals edits value before result after} _ memos _ _ => NodeLaw record originals ambient rootSymbol rootTerms edits value before result memos)
      (motive_2 := fun {record originals entries index values before results after} _ memos _ _ => ChildrenLaw record originals ambient rootSymbol rootTerms entries index values before results memos)
      (motive_3 := fun {record originals entries edges before results after} _ memos _ _ => RowsLaw record originals ambient rootSymbol rootTerms entries edges before results memos)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase read
  · intro record originals entries edges before results after actual memos final read
    exact RowsReads.rec (motive_1 := fun {record originals edits value before result after} _ memos _ _ => NodeLaw record originals ambient rootSymbol rootTerms edits value before result memos)
      (motive_2 := fun {record originals entries index values before results after} _ memos _ _ => ChildrenLaw record originals ambient rootSymbol rootTerms entries index values before results memos)
      (motive_3 := fun {record originals entries edges before results after} _ memos _ _ => RowsLaw record originals ambient rootSymbol rootTerms entries edges before results memos)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase read

/-- Actual node reads derive narrowing and conditional retention. -/
theorem node {edits value before result after} {actual : EditNode record originals edits value before result after} {memos final}
    (read : NodeReads formulas solver base actual memos final) : NodeLaw record originals ambient rootSymbol rootTerms edits value before result memos :=
  (bounds formulas solver base ambient rootSymbol rootTerms).1 read

/-- Actual child reads retain ordered forest language bounds. -/
theorem children {entries index values before results after}
    {actual : EditChildren record originals entries index values before results after} {memos final}
    (read : ChildrenReads formulas solver base actual memos final) : ChildrenLaw record originals ambient rootSymbol rootTerms entries index values before results memos :=
  (bounds formulas solver base ambient rootSymbol rootTerms).2.1 read

/-- Actual row reads derive inclusion and retention for accepted terms. -/
theorem rows {entries edges before results after}
    {actual : EditRows record originals entries edges before results after} {memos final}
    (read : RowsReads formulas solver base actual memos final) : RowsLaw record originals ambient rootSymbol rootTerms entries edges before results memos :=
  (bounds formulas solver base ambient rootSymbol rootTerms).2.2 read

/-- List edits retain their ordered forest and original class-satisfying terms. -/
theorem list {edits values before results after} {actual : EditList (width := width) record originals edits values before results after} {memos final}
    (read : ListReads formulas solver base actual memos final)
    (valid : SourceEqualityEdits.Valid edits) (populated : Populated edits) (allowed : Allowed record edits)
    {inventory : Inventory} (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ListSafe edits values)
    (memoValid : MemoValid before.checked.native.machine.heap memos) :
    ∀ terms, (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      (All₂ (meaning holds ambient) originals rootTerms → EqualityNormalize.ClassSat root record.paths →
        SourceEqualityEditAPI.ListCondition condition edits terms → All₂ (meaning holds ambient) values terms →
        All₂ (meaning holds ambient) results terms) := by
  cases read with
  | leaf => exact fun _ => ⟨id, fun _ _ _ accepted => accepted⟩
  | children read =>
      exact children formulas solver base record originals ambient rootSymbol rootTerms read
        valid populated allowed inventory ready available safe memoValid

end MicroCFTA.SourceCurrentAllocatedSharedEditLanguage
