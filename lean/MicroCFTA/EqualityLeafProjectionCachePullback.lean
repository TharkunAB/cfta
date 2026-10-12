import MicroCFTA.EqualityLeafProjectionPhysicalTargets

/-!
# Constructor replay in an earlier resident cache

A complete resident node record determines a node cache hit. A later
closed constructor result can therefore replay in the actual earlier
cache without retaining proof-only allocations.
-/
namespace MicroCFTA.EqualityLeafProjectionCachePullback
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedBinderProtocol (NodeKey)
open InternedFreshProbeKeys InternedEdgeResidency

/-- A later closed node request is already a cache hit wherever its exact output is resident. -/
theorem nodeStep_pullback (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (before after : State Symbol Guard) (beforeCoherent : Coherent before) (afterCoherent : Coherent after)
    (value : Value Symbol Guard) (resident : Resident before value)
    (closed : nodeStep key identify after = (value, after)) : nodeStep key identify before = (value, before) := by
  have stored : after.nodeRecords key = some value := by
    have correct := (nodeStep_correct key identify after afterCoherent.valid).2.2
    rw [closed] at correct
    exact correct
  obtain ⟨entry, present, fields⟩ := afterCoherent.nodes key value stored
  have entryKey : entry.key = key := (afterCoherent.valid.2.2 key entry present).1
  have valueEntry := fields_entry key entry value fields
  have earlierStored := resident entry valueEntry
  have earlierEntry := resident_entry before beforeCoherent value resident entry valueEntry
  rw [entryKey] at earlierStored earlierEntry
  simp only [nodeStep, Cache.intern, earlierEntry, keepFirst, earlierStored, Option.getD_some]

/-- A later closed ordinary parent constructor replays in the cache that retains its output record. -/
theorem makeNode_pullback [DecidableEq (EdgeKey Symbol Guard)] (rows : List (EdgeValue Symbol Guard))
    (before after : State Symbol Guard) (beforeCoherent : Coherent before) (afterCoherent : Coherent after)
    (value : Value Symbol Guard) (resident : Resident before value)
    (closed : run (makeNode rows) after = (value, after)) : run (makeNode rows) before = (value, before) := by
  unfold makeNode at closed ⊢
  cases kept : canonicalEdges (surviving rows) with
  | nil =>
      simp only [kept, run] at closed ⊢
      exact Prod.ext (Prod.mk.inj closed).1 rfl
  | cons first rest =>
      simp only [kept, run] at closed ⊢
      exact nodeStep_pullback _ _ before after beforeCoherent afterCoherent value resident closed

end MicroCFTA.EqualityLeafProjectionCachePullback
