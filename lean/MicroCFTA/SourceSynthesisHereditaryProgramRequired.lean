import MicroCFTA.SourceSynthesisHereditaryProgramFields
import MicroCFTA.SourceCurrentHereditaryProgramRequired

/-!
# Recursive Program fields through annotation-only Required work

Only child zero can change. The actual child graph retains every later
child literally. Full source row certificates therefore retain their
recursive Program children. Actual edge and node construction retain those
certificates through cache hits and row normalization.

The input is empty or ordinary. The proof permits no union or Mu escape
at a Program position. Successful execution and genuine initial physical
facts remain premises. These laws do not prove completion, failed-prefix
safety, all reached classifications, or a global execution bound.
-/
namespace MicroCFTA.SourceSynthesisHereditaryProgramRequired
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityNeeded (Needed)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentHereditaryProgramRequired (FirstField AnnotationOnly)
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol : Type}

private theorem replace_head {values results : List (Value Symbol Guard)}
    {head : Value Symbol Guard} {tail : List (Value Symbol Guard)}
    (shape : values = head :: tail) (count : results.length = values.length)
    (tails : results.tail = values.tail) : ∃ first, results = first :: tail := by
  cases results with
  | nil =>
      rw [shape] at count
      simp only [List.length_nil, List.length_cons] at count
      omega
  | cons first remaining =>
      have same : remaining = tail := by simpa only [shape, List.tail_cons] using tails
      exact ⟨first, congrArg (List.cons first) same⟩

private theorem edge_replaced (valid : Guard → Prop) (literal : String → Symbol)
    {source result : EdgeValue Symbol Guard} (fields : EdgeFields valid literal source)
    (symbol : result.entry.key.symbol = source.entry.key.symbol)
    (guard : result.entry.key.constraint = source.entry.key.constraint)
    (count : result.children.length = source.children.length)
    (typed : FirstField valid result.children) (tails : result.children.tail = source.children.tail) :
    EdgeFields valid literal result := by
  cases fields with
  | annotated source annotation own shape original =>
      obtain ⟨first, children⟩ := replace_head shape count tails
      exact .annotated result first (guard.trans own) children (typed first (by rw [children]; rfl))
  | application source types marker function argument own constraint shape typesTyped markerTyped functionFields argumentFields =>
      obtain ⟨first, children⟩ := replace_head shape count tails
      exact .application result first marker function argument (symbol.trans own) (guard.trans constraint) children
        (typed first (by rw [children]; rfl)) markerTyped functionFields argumentFields
  | filter source goal candidates own constraint shape goalTyped candidateFields =>
      obtain ⟨first, children⟩ := replace_head shape count tails
      exact .filter result first candidates (symbol.trans own) (guard.trans constraint) children
        (typed first (by rw [children]; rfl)) candidateFields

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem edge_rebuilt (valid : Guard → Prop) (literal : String → Symbol) (source : EdgeValue Symbol Guard)
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : EdgeValue Symbol Guard}
    (actual : run (makeEdge source.entry.key.symbol source.entry.key.constraint values) before = (result, after))
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (stored : MuStored valid before) (fields : EdgeFields valid literal source)
    (typed : FirstField valid values) (tails : values.tail = source.children.tail)
    (count : values.length = source.children.length) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧
      MuStored valid after ∧ EdgeFields valid literal result := by
  have checked := SourceEqualityRequiredCache.edge source.entry.key.symbol source.entry.key.constraint values
    before semantic.ready available
  have ready := SourceEqualityRequiredSemanticCache.edge source.entry.key.symbol source.entry.key.constraint values
    before semantic available
  have finalCosts : CostHeap (run (makeEdge source.entry.key.symbol source.entry.key.constraint values) before).2 := costs
  have returned := MergedPhysicalGroupEdges.makeEdge_fields before semantic.ready.semantic.1.normal.facts
    source.entry.key.symbol source.entry.key.constraint values available
  have readback : result.entry.key.symbol = source.entry.key.symbol ∧
      result.entry.key.constraint = source.entry.key.constraint ∧ result.children = values := by
    simpa only [actual] using returned
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [actual] using checked.1
  · simpa only [actual] using ready
  · simpa only [actual] using finalCosts
  · simpa only [actual] using stored.makeEdge source.entry.key.symbol source.entry.key.constraint values
  · exact edge_replaced valid literal fields readback.1 readback.2.1
      (by rw [readback.2.2]; exact count) (by rw [readback.2.2]; exact typed)
      (by rw [readback.2.2]; exact tails)

private theorem rows (valid : Guard → Prop) (literal : String → Symbol)
    {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (stored : MuStored valid before)
    (fields : ∀ edge ∈ edges, EdgeFields valid literal edge) (only : AnnotationOnly entries) :
    MuStored valid after ∧ ∀ edge ∈ results, EdgeFields valid literal edge := by
  cases edges with
  | nil =>
      cases actual
      exact ⟨stored, by intro edge member; cases member⟩
  | cons edge edges =>
      cases actual with
      | rejected doesNotFit rest =>
          exact rows valid literal rest semantic costs
            (fun edge member => resident edge (List.mem_cons_of_mem _ member))
            (fun edge member => closed edge (List.mem_cons_of_mem _ member)) stored
            (fun edge member => fields edge (List.mem_cons_of_mem _ member)) only
      | kept doesFit adjusted made rest =>
          have facts := semantic.ready.semantic.1.normal.facts
          have available : Values before edge.children := facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
          have own := SourceCurrentHereditaryProgramRequired.children valid adjusted semantic costs available
            (closed edge List.mem_cons_self) stored (fields edge List.mem_cons_self).first only
          have physical := SourceCurrentRequiredHeapEffects.children (fun _ => True) adjusted semantic costs
            (by intro _ _ _; trivial) available
          have rebuilt := edge_rebuilt valid literal edge made physical.2.1 physical.2.2.1 physical.2.2.2.2 own.1
            (fields edge List.mem_cons_self) own.2.1 own.2.2 adjusted.length
          have growth := physical.1.trans rebuilt.1
          have later := rows valid literal rest rebuilt.2.1 rebuilt.2.2.1
            (fun edge member => InternedEdgeResidency.edge_grows _ _ growth.growth edge
              (resident edge (List.mem_cons_of_mem _ member)))
            (fun edge member => closed edge (List.mem_cons_of_mem _ member)) rebuilt.2.2.2.1
            (fun edge member => fields edge (List.mem_cons_of_mem _ member)) only
          refine ⟨later.1, ?_⟩
          intro result member
          rcases List.mem_cons.mp member with rfl | tail
          · exact rebuilt.2.2.2.2
          · exact later.2 result tail
termination_by edges.length

private theorem node_rebuilt (valid : Guard → Prop) (literal : String → Symbol)
    {edges : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (actual : run (makeNode edges) before = (result, after)) (facts : InternedNestedFacts.Facts before)
    (resident : Edges before edges) (stored : MuStored valid before)
    (fields : ∀ edge ∈ edges, EdgeFields valid literal edge) :
    MuStored valid after ∧ ValueFields valid literal result := by
  constructor
  · simpa only [actual] using stored.makeNode edges
  · simpa only [actual] using
      SourceSynthesisHereditaryProgramFields.makeNode_fields valid literal edges before facts resident fields

/-- Actual annotation-only Required work preserves every recursive Program field and the Mu store. -/
theorem node (valid : Guard → Prop) (literal : String → Symbol)
    {entries : List (Int × Needed)} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode (.node entries) value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (closed : value.free = []) (stored : MuStored valid before) (fields : ValueFields valid literal value)
    (only : AnnotationOnly entries) : MuStored valid after ∧ ValueFields valid literal result := by
  cases fields with
  | empty =>
      cases actual with
      | identity | empty => exact ⟨stored, .empty⟩
      | recursive nonempty recursive head body => cases recursive
  | node entry edges depth free checked =>
      cases actual with
      | identity => exact ⟨stored, .node entry edges depth free checked⟩
      | ordinary nonempty projected made =>
          have facts := semantic.ready.semantic.1.normal.facts
          have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
          have closedRows := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
          have retained := rows valid literal projected semantic costs resident closedRows stored checked only
          have physical := SourceCurrentRequiredHeapEffects.rows (fun _ => True) projected semantic costs
            (by intro _ _ _; trivial) resident
          exact node_rebuilt valid literal made physical.2.1.ready.semantic.1.normal.facts
            physical.2.2.2.2 retained.1 retained.2
      | recursive nonempty recursive head body => cases recursive

end MicroCFTA.SourceSynthesisHereditaryProgramRequired
