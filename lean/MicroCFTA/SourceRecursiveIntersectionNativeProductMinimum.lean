import MicroCFTA.SourceRecursiveIntersectionNativeColdProduct
import MicroCFTA.SourceRowsMinimumPublic

/-!
# Finite actual native overlap minima from original input language

The minimum worker ignores constraints and reads the actual finite native
cold table. Its root entry is the least common structural node count.
The root-row precheck and productive Boolean have the same exact witness.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Language RecursiveSize InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView (Original)
open SourceFreshOrdinaryColdSharedRows (Trace keys)
open SourcePreparedSharedRows (encode)

/-- Actual finite native product tables supply the exact least common size and structural overlap Boolean. -/
theorem constructed_product_minimum [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (builtValue : Value Symbol Guard)
    (source : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done builtValue source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ fuel value after rows final outer inner,
      execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after ∧
      Trace after.machine.heap (fun _ => none) [value] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner after.machine.heap (fun _ => none) [value] = .done rows final) ∧
      (let raw := SourceColdSharedRows.table rows (keys final rows) value
       let A := SourceRowsMinimumAdapter.automaton raw
       let minimum := SourceRowsMinimumAdapter.minimumSizes raw
       ∃ minimumFuel, MinimumSize.sweeps A (raw.map Prod.fst) minimumFuel (fun _ => none) = minimum ∧
         MinimumSize.sweep A (raw.map Prod.fst) minimum = minimum ∧
         (∀ size, minimum (encode value) = some size ↔
           (∃ term, InternedGuardedLanguage.meaning (fun _ _ => true) ambient left term ∧
             InternedGuardedLanguage.meaning (fun _ _ => true) ambient right term ∧ nodeSize term = size) ∧
           (∀ term, InternedGuardedLanguage.meaning (fun _ _ => true) ambient left term →
             InternedGuardedLanguage.meaning (fun _ _ => true) ambient right term → size ≤ nodeSize term)) ∧
         (SourceRowsMinimumAdapter.productiveRows raw (encode value) = true ↔
           ∃ term, InternedGuardedLanguage.meaning (fun _ _ => true) ambient left term ∧
             InternedGuardedLanguage.meaning (fun _ _ => true) ambient right term)) := by
  obtain ⟨fuel, value, after, rows, final, outer, inner, done, _, _, trace, _, _, _, rowStable, language⟩ :=
    constructed_node_table_product expression builtValue source built domains domainsValid holds emptyGuard conjoin left right
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  let raw := SourceColdSharedRows.table rows (keys final rows) value
  have structural (term : Term Symbol) : Accepts (SourceRowsMinimumAdapter.automaton raw) (encode value) term ↔
      InternedGuardedLanguage.meaning (fun _ _ => true) ambient left term ∧
        InternedGuardedLanguage.meaning (fun _ _ => true) ambient right term := by
    rw [SourceRowsMinimumPublic.ordinary_readback]
    exact language (fun _ _ => true) (by intros; rfl) ambient term
  dsimp only [raw] at structural
  obtain ⟨minimumFuel, reached, stable⟩ := SourceRowsMinimumAdapter.finite raw
  refine ⟨fuel, value, after, rows, final, outer, inner, done, trace, rowStable, minimumFuel, reached, stable, ?_, ?_⟩
  · intro size
    rw [SourceRowsMinimumAdapter.minimum_exact]
    simp only [structural, and_assoc, and_imp]
  · rw [SourceRowsMinimumAdapter.productive_exact]
    simp only [structural]

end MicroCFTA.SourceRecursiveIntersectionNative
