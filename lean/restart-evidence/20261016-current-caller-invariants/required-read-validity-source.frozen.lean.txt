import MicroCFTA.SourceCurrentAllocatedReadDeterminism

/-!
# Validity of supplied required-path global reads

Each proof follows its supplied head, node, child, and row receipt.
Only a fixed-budget head exposure uses read uniqueness. Constructor
suffixes retain those same tables through their actual heap growth.
-/
namespace MicroCFTA.SourceCurrentAllocatedRequiredReadValidity
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityRequiredHead (Head)
open SourceCurrentRequiredQueryMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The supplied head exposure determines its own coherent tables through the actual constructor. -/
theorem head {value result : Value Symbol Guard} {before after : State Symbol Guard}
    {trace : Head value before result after} {memos final : Memos} (reads : HeadReads trace memos final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases reads with
  | @read fuel value result before middle after edges exposed rebuilt memos final calls =>
      have checked := SourceCurrentAllocatedReadDeterminism.exposure calls semantic costs available valid
      have actual := SourceEqualityExposureCosts.nodeEdges_verified fuel value before semantic costs available
      have middleSemantic : SemanticReady middle := by
        simpa only [exposed, MergedSourceExposure.Result.state] using actual.semantic
      have middleValid : Valid middle final := by
        simpa only [exposed, MergedSourceExposure.Result.state] using checked.1
      have constructor := SourceEqualityOpenOrdinaryHead.node edges middle middleSemantic (actual.rows _ _ exposed)
      have retained := SourceQueryUnfoldMemo.valid_grows middle _ middleSemantic constructor.1 final middleValid
      exact ⟨by simpa only [rebuilt] using retained, checked.2⟩

-- The motives keep each supplied trace's literal initial and final table indices.
local macro "reads_induction" recursor:ident reads:ident semantic:ident costs:ident available:ident valid:ident : tactic => `(tactic|
  (revert $semantic $costs $available $valid
   apply $recursor
     (motive_1 := fun {_needed value before _result after} _ memos final _ =>
       SemanticReady before → CostHeap before → Available before value → Valid before memos →
         Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query)
     (motive_2 := fun {_entries _index values before _results after} _ memos final _ =>
       SemanticReady before → CostHeap before → Values before values → Valid before memos →
         Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query)
     (motive_3 := fun {_entries edges before _results after} _ memos final _ =>
       SemanticReady before → CostHeap before → Edges before edges → Valid before memos →
         Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query)
     (t := $reads)
   · intro value before memos _ _ _ initialValid
     exact ⟨initialValid, extends_refl _, rfl⟩
   · intro before entries nonempty memos _ _ _ initialValid
     exact ⟨initialValid, extends_refl _, rfl⟩
   · intro entry depth free entries edges before rebuilt middle rowsTrace memos final nonempty result after built calls ih initialSemantic initialCosts inputAvailable initialValid
     have resident := InternedEdgeResidency.resident_edges before initialSemantic.ready.semantic.1.normal.facts.linked _ inputAvailable.resident
     have checked := ih initialSemantic initialCosts resident initialValid
     have effects := SourceCurrentRequiredHeapEffects.rows (fun _ => True) rowsTrace initialSemantic initialCosts
       (by intro _ _ _; trivial) resident
     have constructor := SourceEqualityOpenOrdinaryHead.node rebuilt middle effects.2.1 effects.2.2.2.2
     have retained := SourceQueryUnfoldMemo.valid_grows middle _ effects.2.1 constructor.1 final checked.1
     exact ⟨by simpa only [built] using retained, checked.2⟩
   · intro original before exposed middle headTrace memos middleMemo entries result after bodyTrace final nonempty recursive headCalls bodyCalls ih initialSemantic initialCosts inputAvailable initialValid
     have first := head headCalls initialSemantic initialCosts inputAvailable initialValid
     have effects := SourceCurrentRequiredHeapEffects.head (fun _ => True) headTrace initialSemantic initialCosts
       (by intro _ _ _; trivial) inputAvailable
     have rest := ih effects.2.1 effects.2.2.1 effects.2.2.2.2 first.1
     exact ⟨rest.1, extends_trans first.2.1 rest.2.1, rest.2.2.trans first.2.2⟩
   · intro entries index before memos _ _ _ initialValid
     exact ⟨initialValid, extends_refl _, rfl⟩
   · intro entries index values results before after value absent restTrace memos final calls ih initialSemantic initialCosts inputAvailable initialValid
     exact ih initialSemantic initialCosts (fun child member => inputAvailable child (List.mem_cons_of_mem _ member)) initialValid
   · intro entries index needed values results value result before middle after found firstTrace restTrace memos middleMemo final firstCalls restCalls firstIH restIH initialSemantic initialCosts inputAvailable initialValid
     have valueAvailable := inputAvailable value List.mem_cons_self
     have first := firstIH initialSemantic initialCosts valueAvailable initialValid
     have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) firstTrace initialSemantic initialCosts
       (by intro _ _ _; trivial) valueAvailable
     have rest := restIH effects.2.1 effects.2.2.1
       (fun child member => effects.1.available child (inputAvailable child (List.mem_cons_of_mem _ member))) first.1
     exact ⟨rest.1, extends_trans first.2.1 rest.2.1, rest.2.2.trans first.2.2⟩
   · intro entries before memos _ _ _ initialValid
     exact ⟨initialValid, extends_refl _, rfl⟩
   · intro entries edges before results after restTrace memos final edge rejected calls ih initialSemantic initialCosts resident initialValid
     exact ih initialSemantic initialCosts (fun original member => resident original (List.mem_cons_of_mem _ member)) initialValid
   · intro entries edge before values middle childTrace memos middleMemo edges afterEdge results after restTrace final fits result rebuilt childCalls restCalls childIH restIH initialSemantic initialCosts resident initialValid
     have inputAvailable : Values before edge.children := initialSemantic.ready.semantic.1.normal.facts.cached.edges
       edge.entry.key edge (resident edge List.mem_cons_self)
     have first := childIH initialSemantic initialCosts inputAvailable initialValid
     have effects := SourceCurrentRequiredHeapEffects.children (fun _ => True) childTrace initialSemantic initialCosts
       (by intro _ _ _; trivial) inputAvailable
     have constructor := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle
       effects.2.1.ready effects.2.2.2.2
     have kept : Keeps middle afterEdge := by simpa only [rebuilt] using constructor.1
     have afterSemantic : SemanticReady afterEdge := by
       simpa only [rebuilt] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol
         edge.entry.key.constraint values middle effects.2.1 effects.2.2.2.2
     have afterCosts : CostHeap afterEdge := by
       have same : CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 := effects.2.2.1
       simpa only [rebuilt] using same
     have middleValid := SourceQueryUnfoldMemo.valid_grows middle afterEdge effects.2.1 kept middleMemo first.1
     have rest := restIH afterSemantic afterCosts
       (fun original member => InternedEdgeResidency.edge_grows before afterEdge (effects.1.trans kept).growth original
         (resident original (List.mem_cons_of_mem _ member))) middleValid
     exact ⟨rest.1, extends_trans first.2.1 rest.2.1, rest.2.2.trans first.2.2⟩))

/-- Supplied node reads retain their own final validity and literal memo indices. -/
theorem node {needed : SourceEqualityNeeded.Needed} {value result : Value Symbol Guard}
    {before after : State Symbol Guard} {trace : RequireNode needed value before result after} {memos final : Memos}
    (reads : NodeReads trace memos final) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  reads_induction NodeReads.rec reads semantic costs available valid

/-- Supplied child reads thread their exact returned tables through selected original positions. -/
theorem children {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {trace : RequireChildren entries index values before results after} {memos final : Memos}
    (reads : ChildrenReads trace memos final) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  reads_induction ChildrenReads.rec reads semantic costs available valid

/-- Supplied row reads retain validity through actual children, constructors, and remaining rows. -/
theorem rows {entries : List (Int × SourceEqualityNeeded.Needed)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} {trace : RequireRows entries edges before results after} {memos final : Memos}
    (reads : RowsReads trace memos final) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Edges before edges) (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  reads_induction RowsReads.rec reads semantic costs available valid

/-- A supplied requireAll receipt derives coherence of its actual final global tables. -/
theorem required {paths : List (List Int)} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {memos final : Memos}
    (reads : RequireAllReads paths values results before after memos final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [RequireAllReads, compiled] at reads
      obtain ⟨trace, actual⟩ := reads
      exact children actual semantic costs available valid

/-- The literal requireAll spelling exposes the same supplied-read endpoint. -/
theorem requireAll {paths : List (List Int)} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {memos final : Memos}
    (reads : RequireAllReads paths values results before after memos final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query :=
  required reads semantic costs available valid

end MicroCFTA.SourceCurrentAllocatedRequiredReadValidity
