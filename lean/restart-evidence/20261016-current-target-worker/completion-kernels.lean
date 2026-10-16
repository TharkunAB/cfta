import MicroCFTA.SourceCurrentAllocatedTargetWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedTargetComplete

namespace MicroCFTA.AllocatedTargetCompletionKernels
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedTargetGraph (Operand Fold Target TargetRanges)
open SourceCurrentAllocatedTargetQuery (Step)
open SourceCurrentAllocatedTargetWorker
open SourceCurrentAllocatedTargetWorkerCompletion
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The second selected path executes before the first seed, then the checked intersection. -/
theorem two_path_source_order
    {values : List (Value Symbol Guard)} {seed path : List Int}
    {before middle later after : Checked width} {memo current saved : Memo}
    {head tail result : Value Symbol Guard}
    (first : Operand path values before memo head middle current)
    (last : Operand seed values middle current tail later saved)
    (native : Step head tail later result after) :
    StableRun (fun p h m s n => target p h m s n values [seed, path] before memo) result after saved :=
  target_complete (.nonempty (.cons first (.nil last) native))

/-- Three paths retain the actual memo at each operand and intersect the inner pair first. -/
theorem three_path_memo_and_native_order
    {values : List (Value Symbol Guard)} {seed path nextPath : List Int}
    {before firstState secondState seedState innerState after : Checked width}
    {memo firstMemo secondMemo saved : Memo} {head next seedValue inner result : Value Symbol Guard}
    (first : Operand path values before memo head firstState firstMemo)
    (second : Operand nextPath values firstState firstMemo next secondState secondMemo)
    (last : Operand seed values secondState secondMemo seedValue seedState saved)
    (innerNative : Step next seedValue seedState inner innerState)
    (outerNative : Step head inner innerState result after) :
    StableRun (fun p h m s n => target p h m s n values [seed, path, nextPath] before memo) result after saved :=
  target_complete (.nonempty (.cons first (.cons second (.nil last) innerNative) outerNative))

/-- An arbitrary successful fuel choice agrees with the actual completed graph in every state component. -/
theorem literal_success_matches_actual_graph
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after later : Checked width}
    {memo saved current : Memo} {result expected : Value Symbol Guard} {p h m s n : Nat}
    (actual : Target values paths before memo expected later current)
    (done : target p h m s n values paths before memo = .done result after saved) :
    result = expected ∧ after = later ∧ saved = current := by
  obtain ⟨a, b, c, d, e, stable⟩ := target_complete actual
  exact target_done_unique done (stable a b c d e (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _))

/-- Initial physical facts construct the graph and stable worker, rather than assume future target success. -/
theorem initial_facts_derive_stable_worker_and_same_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked width) (memo : Memo) (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ paths, SourceEqualityProjectionPathDomain.ForestClosed path values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values paths before memo) (memos : EndpointMemoGateTrace.Memos)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ result after saved next final,
      StableRun (fun p h m s n => target p h m s n values paths before memo) result after saved ∧
      ∃ actual : Target values paths before memo result after saved,
        SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final ∧
        SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values paths before memo result after saved memos final := by
  obtain ⟨result, after, saved, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedTargetComplete.target_complete formulas solver inventory values paths before memo
      ready admitted available domains stored covered ranges memos valid
  exact ⟨result, after, saved, next, final, target_complete actual, actual, reads, receipt⟩

/-- A warm selected hit keeps the entire checked state with an unrelated open sibling. -/
theorem warm_hit_stable_with_open_sibling
    (input : Value Symbol Guard) (name : InternedBinderProtocol.Reference) (before : Checked width) (memo : Memo)
    (entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard) (found : memo input.referenceOf = some entry) :
    StableRun (fun p h m s n => target p h m s n [input, .reference name] [[0]] before memo)
      entry.result before memo := by
  have actual : Operand [0] [input, .reference name] before memo entry.result before memo :=
    .force (.selected (by rfl) .root) (.done (.hit found))
  exact target_complete (.nonempty (.nil actual))

omit [DecidableEq Symbol] in
/-- A successful recursive projection retains its literal read effects at larger independent bounds. -/
theorem recursive_projection_success_stable
    {p h largerP largerH : Nat} {index : Int} {path : List Int}
    {entry : Cache.Interned InternedBinderProtocol.NodeKey} {body result depthShape ordinaryShape : Value Symbol Guard} {before after : InternedConstructorTemplates.State Symbol Guard}
    (done : SourceEqualityProjectionWorker.forest p h (0 :: index :: path)
      [.mu entry body depthShape ordinaryShape] before = .done result after)
    (moreProjection : p ≤ largerP) (moreRead : h ≤ largerH) :
    SourceEqualityProjectionWorker.forest largerP largerH (0 :: index :: path)
      [.mu entry body depthShape ordinaryShape] before = .done result after :=
  forest_done_stable done moreProjection moreRead

/-- Successful native execution is stable without inventing a physical trace from that success. -/
theorem native_success_stable_without_physical_oracle
    {n larger : Nat} {left right result : Value Symbol Guard} {before after : Checked width} (memo : Memo)
    (done : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done result after)
    (enough : n ≤ larger) : leaf larger left right before memo = .done result after memo := by
  have completed : leaf n left right before memo = .done result after memo := by simp only [leaf, done]
  exact leaf_done_stable completed enough

/-- A failed tail retains its full reached state and memo and skips the final native request. -/
theorem failed_tail_skips_native
    {p h m s n : Nat} {values : List (Value Symbol Guard)} {seed path : List Int} {paths : List (List Int)}
    {before middle after : Checked width} {memo current saved : Memo} {head : Value Symbol Guard} {fault : Fault width}
    (first : operand p h m s path values before memo = .done head middle current)
    (failed : fold p h m s n values seed paths middle current = .failed fault after saved) :
    fold p h m s n values seed (path :: paths) before memo = .failed fault after saved := by
  simp only [fold, first, Outcome.bind, failed]

#print axioms two_path_source_order
#print axioms three_path_memo_and_native_order
#print axioms literal_success_matches_actual_graph
#print axioms initial_facts_derive_stable_worker_and_same_receipt
#print axioms warm_hit_stable_with_open_sibling
#print axioms recursive_projection_success_stable
#print axioms native_success_stable_without_physical_oracle
#print axioms failed_tail_skips_native
set_option pp.explicit true
#check @two_path_source_order
#check @three_path_memo_and_native_order
#check @literal_success_matches_actual_graph
#check @initial_facts_derive_stable_worker_and_same_receipt
#check @warm_hit_stable_with_open_sibling
#check @recursive_projection_success_stable
#check @native_success_stable_without_physical_oracle
#check @failed_tail_skips_native
end MicroCFTA.AllocatedTargetCompletionKernels
