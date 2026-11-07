import MicroCFTA.SourceSynthesisUniverseColdProbe
import MicroCFTA.SourceSynthesisUniverseBody
import MicroCFTA.InternedFreshOrdinaryReadback

/-!
# Actual cold universe record and body

The original top guard and catalog determine a completed Mu construction.
The proof derives the reservation miss from both actual probes. It derives
the ordinary body from the actual callback and then proves that cleanup
retains the binder. The endpoint starts with empty caches. General incoming
cache histories and generated intersection closure remain separate obligations.
-/
namespace MicroCFTA.SourceSynthesisUniverseColdReadback
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome request finish)
open InternedBinderProtocol (Reference NodeKey)
open SourceSynthesisTypeSyntax

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

omit [DecidableEq (EdgeKey String Guard)] in
/-- The actual normalized body is recursive and cannot trigger either cleanup branch. -/
theorem finish_shaped_mu (top : Guard) (catalog : List (String × Nat))
    (entry : Interned NodeKey) (body depth ordinary : Value String Guard)
    (shape : SourceSynthesisUniverseBody.Shape top catalog (.interned entry.identity) body) :
    finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
  obtain ⟨bodyEntry, marker, arrow, rest, same, _⟩ := shape
  simp [finish, cleanup, same, Value.free, Value.referenceOf]

/-- Original universe inputs derive a closed Mu with its exact resident body and probe key. -/
theorem allTypes_cold_mu (top : Guard) (catalog : List (String × Nat)) :
    ∃ entry body depth ordinary final,
      InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] empty =
        .done (.mu entry body depth ordinary) final ∧
      Facts final ∧ Available final (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top catalog (.interned entry.identity) body ∧
      entry.key = muKey depth ordinary ∧
      final.nodes.table (muKey depth ordinary) = some entry ∧
      final.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      (Value.mu entry body depth ordinary).free = [] := by
  obtain ⟨value, final, done, facts, available, _, _⟩ :=
    SourceSynthesisUniverseNativeInput.allTypes_closed_verified_complete top catalog
  obtain ⟨depth, afterDepth, ordinary, afterOrdinary, _, _, probeFacts, _, _, missing, expanded⟩ :=
    SourceSynthesisUniverseColdProbe.allTypes_cold_probes top catalog
  have requested : request true depth ordinary
      (InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) []) afterOrdinary =
      .done value final := expanded.symm.trans done
  obtain ⟨actual, afterBody, bodyDone, _, finished⟩ :=
    InternedFreshOrdinaryReadback.request_miss_record true (allTypesBody top catalog) []
      depth ordinary afterOrdinary probeFacts.coherent missing value final requested
  let reserved := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).1
  let allocated := {afterOrdinary with nodes := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).2}
  have allocatedFacts : Facts allocated := reserve_facts (muKey depth ordinary) afterOrdinary probeFacts
  have localAvailable : Available allocated (.reference (.interned reserved.identity)) :=
    (InternedConstructionProvenance.reserve_available (muKey depth ordinary) afterOrdinary
      probeFacts.coherent probeFacts.cached).2
  obtain ⟨shaped, _, shapedDone, bodyShape, _, _⟩ :=
    SourceSynthesisUniverseBody.callback_readback top catalog (.interned reserved.identity)
      allocated allocatedFacts localAvailable
  have same : actual = shaped := (Outcome.done.inj (bodyDone.symm.trans shapedDone)).1
  have actualShape : SourceSynthesisUniverseBody.Shape top catalog (.interned reserved.identity) actual :=
    same.symm ▸ bodyShape
  have valueIs : value = .mu reserved actual depth ordinary :=
    finished.trans (finish_shaped_mu top catalog reserved actual depth ordinary actualShape)
  have muAvailable : Available final (.mu reserved actual depth ordinary) := valueIs ▸ available
  obtain ⟨key, table, record⟩ := SourceSynthesisUniverseNativeInput.available_mu_key_readback
    final facts reserved actual depth ordinary muAvailable
  refine ⟨reserved, actual, depth, ordinary, final, valueIs ▸ done, facts, muAvailable,
    actualShape, key, table, record, ?_⟩
  obtain ⟨bodyEntry, marker, arrow, rest, bodyEq, _⟩ := actualShape
  simp [Value.free, bodyEq]

omit [DecidableEq (EdgeKey String Guard)] in
/-- The original library and query derive the closed default universe and its actual body. -/
theorem typesOf_cold_mu
    [DecidableEq (EdgeKey String SourceSynthesisGeneralizeSyntax.Guard)]
    (lib : Library) (query : Query) :
    ∃ entry body depth ordinary final,
      InternedFreshOrdinaryConstruction.build
        (SourceSynthesisFirstOrderConstruction.typesOf lib query) [] empty =
        .done (.mu entry body depth ordinary) final ∧
      Facts final ∧ Available final (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape SourceSynthesisGeneralizeSyntax.top
        (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
        (.interned entry.identity) body ∧
      (Value.mu entry body depth ordinary).free = [] := by
  obtain ⟨entry, body, depth, ordinary, final, done, facts, available, shape, _, _, _, closed⟩ :=
    allTypes_cold_mu SourceSynthesisGeneralizeSyntax.top
      (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
  exact ⟨entry, body, depth, ordinary, final, done, facts, available, shape, closed⟩

end MicroCFTA.SourceSynthesisUniverseColdReadback
