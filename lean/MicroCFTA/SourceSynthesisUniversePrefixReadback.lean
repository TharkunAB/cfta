import MicroCFTA.SourceSynthesisUniversePrefixSeed

/-!
# Complete universe readback after an actual constructor prefix

Record growth retains the exact seed payload.
Current cache facts derive its complete availability from that payload.
No issued-name growth follows from record growth alone.
The three raw row packets also remain resident in the current heap.
-/
namespace MicroCFTA.SourceSynthesisUniversePrefixSeed
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedFreshProbeKeys
open InternedBinderProtocol (Reference NodeKey)
open SourceSynthesisUniverseResidentRows (Rows)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]
variable {top : Guard} {catalog : List (String × Nat)}

/-- Current cache facts recover all provenance from the retained complete Mu record. -/
theorem Seed.available_after (seed : Seed top catalog)
    (current : InternedConstructorTemplates.State String Guard) (facts : Facts current)
    (ready : Ready (some seed) current) : Available current seed.value := by
  have resident : Resident current seed.value :=
    resident_grows seed.builtHeap current ready seed.value seed.available.resident
  exact facts.cached.nodes seed.entry.key seed.value (resident seed.entry rfl)

/-- Record growth preserves all raw rows from the retained actual build. -/
theorem Seed.rows_after (seed : Seed top catalog)
    (current : InternedConstructorTemplates.State String Guard) (ready : Ready (some seed) current) :
    Rows top catalog (.interned seed.entry.identity) seed.body current ∧
    Rows top catalog .depth seed.depth current ∧
    Rows top catalog (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel seed.depth))
      seed.ordinary current :=
  ⟨seed.bodyRows.grows ready, seed.depthRows.grows ready, seed.ordinaryRows.grows ready⟩

/-- The retained actual body rows derive the full normalized universe shape. -/
theorem Seed.body_shape (seed : Seed top catalog) :
    SourceSynthesisUniverseBody.Shape top catalog (.interned seed.entry.identity) seed.body := by
  obtain ⟨entry, marker, arrow, rest, same, markerRead, arrowChildren, arrowKey, aligned,
      _resident, _closed, _markerAvailable, _guards, _kinds, live, _retained, _nonempty⟩ :=
    seed.bodyRows.readback seed.facts
  have survive : surviving (arrow :: rest) = arrow :: rest := by
    unfold surviving
    apply List.filter_eq_self.mpr
    intro row member
    change (!EqualityLeafProjectionPhysical.dead row) = true
    simp only [live row member, Bool.not_false]
  exact ⟨entry, marker, arrow, rest, by simpa only [survive] using same,
    markerRead, arrowChildren, arrowKey, aligned⟩

end MicroCFTA.SourceSynthesisUniversePrefixSeed

namespace MicroCFTA.SourceSynthesisUniversePrefixReadback
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedFreshProbeKeys SourceSynthesisUniversePrefixSeed
open InternedBinderProtocol (Reference NodeKey)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]
variable {top : Guard} {catalog : List (String × Nat)}

/-- An available Mu with the selected identity is the exact complete seed value. -/
theorem available_mu_eq_seed (seed : Seed top catalog)
    (current : InternedConstructorTemplates.State String Guard) (entry : Interned NodeKey)
    (body depth ordinary : Value String Guard) (facts : Facts current)
    (ready : Ready (some seed) current) (available : Available current (.mu entry body depth ordinary))
    (same : entry.identity = seed.entry.identity) :
    Value.mu entry body depth ordinary = seed.value :=
  resident_identity_unique current facts.coherent (.mu entry body depth ordinary) seed.value
    available.resident (seed.available_after current facts ready).resident entry seed.entry rfl rfl same

end MicroCFTA.SourceSynthesisUniversePrefixReadback
