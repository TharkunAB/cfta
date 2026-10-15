import MicroCFTA.SourceEmptinessKeys
import MicroCFTA.ConservativeEmptinessTableSoundness
import MicroCFTA.InternedGuardedLanguage

/-!
# Finite table soundness with derived physical record readback

The common coherent heap and certified inventory derive raw-key readback.
Actual table entries derive the finite carrier. Local row exposure and
primitive graph laws then give one-sided soundness at the original guarded
meaning. Native supply construction and inventory coverage remain premises.
-/
namespace MicroCFTA.SourceEmptinessTableSoundness
open Language InternedConstructorTemplates InternedRecordCoherence
open SourceEmptinessKeys ConservativeEmptinessExplore

/-- Actual coherent closed records discharge the table theorem's complete physical readback premise. -/
theorem excludes (heap : State Symbol Guard) (coherent : Coherent heap)
    (table : Table) (inventory : List (Closed heap)) (covered : SourceEmptinessKeys.Covered table inventory)
    (ops : EqualityReduction.Operations (Closed heap) Symbol)
    (laws : ConservativeEmptinessRows.PrimitiveLaws ops) (emptyField : ops.empty = SourceEmptinessKeys.empty heap)
    (exposed : Int → List (ConservativeEmptinessRows.Row (Closed heap)))
    (stored : ConservativeEmptinessTableSoundness.StoredSupply table
      (ConservativeEmptinessTableSoundness.rowSupply ops SourceEmptinessKeys.item exposed))
    (exposure : ConservativeEmptinessRows.Exposure ops (SourceEmptinessKeys.read table inventory)
      (fun state => exposed state.val))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (denotation : ops.meaning = fun value term => InternedGuardedLanguage.meaning holds ambient value.val term)
    (query : Closed heap) (empty : ConservativeEmptinessTable.provablyEmpty table (SourceEmptinessKeys.item query) = true) :
    ∀ term, ¬InternedGuardedLanguage.meaning holds ambient query.val term := by
  have readback := SourceEmptinessKeys.readback heap coherent table inventory covered ops emptyField
  have sound := ConservativeEmptinessTableSoundness.provablyEmpty_sound table ops laws SourceEmptinessKeys.item
    exposed stored (SourceEmptinessKeys.read table inventory) readback exposure query empty
  simpa only [denotation] using sound

/-- Empty-start exploration derives the stored-row receipt before physical readback supplies source soundness. -/
theorem explored_excludes (heap : State Symbol Guard) (coherent : Coherent heap)
    (ops : EqualityReduction.Operations (Closed heap) Symbol)
    (laws : ConservativeEmptinessRows.PrimitiveLaws ops) (emptyField : ops.empty = SourceEmptinessKeys.empty heap)
    (exposed : Int → List (ConservativeEmptinessRows.Row (Closed heap))) (budget : Nat) (pending : List Item)
    (inventory : List (Closed heap))
    (covered : SourceEmptinessKeys.Covered
      (explore (ConservativeEmptinessTableSoundness.rowSupply ops SourceEmptinessKeys.item exposed) budget [] pending) inventory)
    (exposure : ConservativeEmptinessRows.Exposure ops
      (SourceEmptinessKeys.read
        (explore (ConservativeEmptinessTableSoundness.rowSupply ops SourceEmptinessKeys.item exposed) budget [] pending) inventory)
      (fun state => exposed state.val))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (denotation : ops.meaning = fun value term => InternedGuardedLanguage.meaning holds ambient value.val term)
    (query : Closed heap)
    (empty : ConservativeEmptinessTable.provablyEmpty
      (explore (ConservativeEmptinessTableSoundness.rowSupply ops SourceEmptinessKeys.item exposed) budget [] pending)
      (SourceEmptinessKeys.item query) = true) :
    ∀ term, ¬InternedGuardedLanguage.meaning holds ambient query.val term :=
  excludes heap coherent _ inventory covered ops laws emptyField exposed
    (ConservativeEmptinessTableSoundness.entered_rows _ budget pending) exposure holds ambient denotation query empty

end MicroCFTA.SourceEmptinessTableSoundness
