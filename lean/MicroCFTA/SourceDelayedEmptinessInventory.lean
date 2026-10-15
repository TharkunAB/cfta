import MicroCFTA.DelayedEmptinessExplore
import MicroCFTA.SourceEmptinessInventory
import MicroCFTA.SourceEqualityRequiredCache

/-!
# Physical inventory from reached delayed exploration

Each reached force and exposure supplies its own heap effects. Trace
induction preserves the earlier complete records and certifies each actual
admission. The final inventory uses the returned entry list. No final heap
or inventory invariant is assumed. Native task laws and the machine-Int
identity correspondence remain separate obligations.
-/
namespace MicroCFTA.SourceDelayedEmptinessInventory
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceEmptinessKeys DelayedEmptinessExplore

variable {Task Heap Symbol Guard : Type}

/-- Keep the actual key and complete value of each delayed table entry. -/
def entries (seen : Table Task (Value Symbol Guard)) : List (Int × Value Symbol Guard) :=
  seen.map (fun entry => (entry.key, entry.value))

/-- Taking entry records retains the exact ordered key list. -/
theorem entries_keys (seen : Table Task (Value Symbol Guard)) :
    (entries seen).map Prod.fst = seen.map Entry.key := by
  simp only [entries, List.map_map, Function.comp_def]

/-- Local completed operations supply effects only for their actual current ready heap. -/
structure Laws (heap : Heap → State Symbol Guard) (ready : Heap → Prop)
    (force : Task → Heap → Value Symbol Guard → Heap → Prop)
    (expose : Value Symbol Guard → Heap → List (List Task) → Heap → Prop)
    (encode : Value Symbol Guard → ConservativeEmptinessExplore.Item) : Prop where
  ready_heap : ∀ state, ready state → SourceEqualityRequiredCache.Ready (heap state)
  force : ∀ task before value after, ready before → force task before value after →
    ready after ∧ SourceEqualityRequiredCache.Keeps (heap before) (heap after) ∧
      Available (heap after) value ∧ value.free = []
  expose : ∀ value before rows after, ready before → expose value before rows after →
    ready after ∧ SourceEqualityRequiredCache.Keeps (heap before) (heap after)
  encoded : ∀ value identity, encode value = .resident identity true → key value = some identity

/-- Physical heap effects retain every previously certified entry record. -/
theorem records_keeps {before after : State Symbol Guard}
    (keeps : SourceEqualityRequiredCache.Keeps before after)
    (values : List (Int × Value Symbol Guard)) (records : SourceEmptinessInventory.Records before values) :
    SourceEmptinessInventory.Records after values := by
  intro entry member
  have original := records entry member
  exact ⟨keeps.available entry.2 original.1, original.2⟩

/-- Actual trace leaves derive final readiness, heap preservation, and all stored entry records. -/
theorem trace_effects {heap : Heap → State Symbol Guard} {ready : Heap → Prop}
    {force : Task → Heap → Value Symbol Guard → Heap → Prop}
    {expose : Value Symbol Guard → Heap → List (List Task) → Heap → Prop}
    {encode : Value Symbol Guard → ConservativeEmptinessExplore.Item}
    (laws : Laws heap ready force expose encode)
    (trace : Trace force expose encode budget seen pending before final after) :
    ready before → SourceEmptinessInventory.Records (heap before) (entries seen) →
      ready after ∧ SourceEqualityRequiredCache.Keeps (heap before) (heap after) ∧
        SourceEmptinessInventory.Records (heap after) (entries final) := by
  induction trace with
  | done =>
      intro initial records
      exact ⟨initial, SourceEqualityRequiredCache.pure_keeps _ (laws.ready_heap _ initial), records⟩
  | empty forced encoded rest ih =>
      intro initial records
      obtain ⟨forcedReady, forcedKeeps, _, _⟩ := laws.force _ _ _ _ initial forced
      obtain ⟨finalReady, restKeeps, finalRecords⟩ := ih forcedReady (records_keeps forcedKeeps _ records)
      exact ⟨finalReady, forcedKeeps.trans restKeeps, finalRecords⟩
  | skipped forced encoded skipped rest ih =>
      intro initial records
      obtain ⟨forcedReady, forcedKeeps, _, _⟩ := laws.force _ _ _ _ initial forced
      obtain ⟨finalReady, restKeeps, finalRecords⟩ := ih forcedReady (records_keeps forcedKeeps _ records)
      exact ⟨finalReady, forcedKeeps.trans restKeeps, finalRecords⟩
  | @admit task before value forcedHeap identity closed budget seen rows exposedHeap pending final after
      forced encoded fresh exposed rest ih =>
      intro initial records
      obtain ⟨forcedReady, forcedKeeps, available, valueClosed⟩ := laws.force _ _ _ _ initial forced
      obtain ⟨exposedReady, exposedKeeps⟩ := laws.expose _ _ _ _ forcedReady exposed
      have actualKey : key value = some identity := laws.encoded value identity (by
        simpa only [(admitted budget seen identity closed fresh).2.2] using encoded)
      have earlier := records_keeps (forcedKeeps.trans exposedKeeps) _ records
      have admittedRecords : SourceEmptinessInventory.Records (heap exposedHeap)
          (entries ((⟨identity, value, rows⟩ : Entry Task (Value Symbol Guard)) :: seen)) := by
        intro entry member
        rcases List.mem_cons.mp member with same | old
        · cases same
          exact ⟨exposedKeeps.available value available, valueClosed, actualKey⟩
        · exact earlier entry old
      obtain ⟨finalReady, restKeeps, finalRecords⟩ := ih exposedReady admittedRecords
      exact ⟨finalReady, forcedKeeps.trans (exposedKeeps.trans restKeeps), finalRecords⟩

/-- The returned records are derived from the actual local leaves of the completed trace. -/
theorem final_records {heap : Heap → State Symbol Guard} {ready : Heap → Prop}
    {force : Task → Heap → Value Symbol Guard → Heap → Prop}
    {expose : Value Symbol Guard → Heap → List (List Task) → Heap → Prop}
    {encode : Value Symbol Guard → ConservativeEmptinessExplore.Item}
    (laws : Laws heap ready force expose encode)
    (trace : Trace force expose encode budget seen pending before final after)
    (initial : ready before) (records : SourceEmptinessInventory.Records (heap before) (entries seen)) :
    SourceEmptinessInventory.Records (heap after) (entries final) :=
  (trace_effects laws trace initial records).2.2

/-- The actual final entry list covers every key in an exact completed table readout. -/
theorem covered {heap : Heap → State Symbol Guard} {ready : Heap → Prop}
    {force : Task → Heap → Value Symbol Guard → Heap → Prop}
    {expose : Value Symbol Guard → Heap → List (List Task) → Heap → Prop}
    {encode : Value Symbol Guard → ConservativeEmptinessExplore.Item}
    (laws : Laws heap ready force expose encode)
    (trace : Trace force expose encode budget seen pending before final after)
    (initial : ready before) (records : SourceEmptinessInventory.Records (heap before) (entries seen))
    (table : ConservativeEmptinessExplore.Table) (sameKeys : table.map Prod.fst = final.map Entry.key) :
    SourceEmptinessKeys.Covered table
      (SourceEmptinessInventory.inventory (heap after) (entries final) (final_records laws trace initial records)) := by
  apply SourceEmptinessInventory.covered
  exact sameKeys.trans (entries_keys final).symm

/-- Local operation laws and actual completion derive literal complete-record table readback. -/
theorem readback {heap : Heap → State Symbol Guard} {ready : Heap → Prop}
    {force : Task → Heap → Value Symbol Guard → Heap → Prop}
    {expose : Value Symbol Guard → Heap → List (List Task) → Heap → Prop}
    {encode : Value Symbol Guard → ConservativeEmptinessExplore.Item}
    (laws : Laws heap ready force expose encode)
    (trace : Trace force expose encode budget seen pending before final after)
    (initial : ready before) (records : SourceEmptinessInventory.Records (heap before) (entries seen))
    (table : ConservativeEmptinessExplore.Table) (sameKeys : table.map Prod.fst = final.map Entry.key)
    (ops : EqualityReduction.Operations (Closed (heap after)) Symbol)
    (emptyField : ops.empty = SourceEmptinessKeys.empty (heap after)) :
    ConservativeEmptinessRows.Readback ops
      (SourceEmptinessInventory.read (heap after) (entries final) (final_records laws trace initial records) table)
      (SourceEmptinessKeys.classify table) := by
  have coherent := (trace_effects laws trace initial records).2.1.ready.semantic.1.normal.facts.coherent
  exact SourceEmptinessInventory.readback (heap after) coherent (entries final)
    (final_records laws trace initial records) table (sameKeys.trans (entries_keys final).symm) ops emptyField

end MicroCFTA.SourceDelayedEmptinessInventory
