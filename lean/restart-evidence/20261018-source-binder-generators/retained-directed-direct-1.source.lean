import MicroCFTA.SourceCurrentRetainedProbeSchedule
import MicroCFTA.SourceCurrentPublicationSharedReplacements

/-!
# Actual source generators for retained Mu reconstructions

The relation contains equality and actual filtered source reconstructions.
Recursive membership occurs only in the resolved lexical inputs. Live
alias tests remain explicit. A selected writer supplies both directions
of its actual body and ordinary reconstruction generator. Its expression
can differ from the current requester's expression. This module proves
membership, not the directional simulation laws for every generator.
-/
namespace MicroCFTA.SourceCurrentRetainedMuDirectedCase
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedFreshOrdinaryLiveInputs (input liftInput local_inputs)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuGrowthHistory (Path)
open SourceCurrentNativeMuGrowthWriters (Written)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentReaderReplacementSlots (Paired Slot)
open SourceCurrentPublicationSharedReplacements (shared)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceEqualityRequiredCache (Ready Keeps)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Equality and actual filtered source calls generate pairs before any observation law is proved. -/
inductive Generated (reader : State Symbol Guard) : Value Symbol Guard → Value Symbol Guard → Prop where
  /-- One immutable value supplies reflexive membership. -/
  | refl (value) : Generated reader value value
  /-- Historical source calls, live aliases and paired lexical inputs supply one reconstructed pair. -/
  | filtered {Atom : Type} (expression : Syntax Symbol Guard)
      (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
      (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
      (firstBefore secondBefore firstRawHeap secondRawHeap firstFilterHeap secondFilterHeap : State Symbol Guard)
      (firstRaw secondRaw firstFiltered secondFiltered left right : Value Symbol Guard)
      (ready : Ready reader)
      (firstContext : Context firstBefore (inputs.map (input firstNames)))
      (secondContext : Context secondBefore (inputs.map (input secondNames)))
      (aliases : Aliases expression inputs firstNames secondNames)
      (selfTests : ∀ label ∈ Scope expression inputs,
        Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn)
      (paired : Paired (Generated reader) firstMap secondMap
        (inputs.map (input firstNames)) (inputs.map (input secondNames)))
      (firstReplacements : Replacements reader firstMap) (secondReplacements : Replacements reader secondMap)
      (firstAvailable : Available reader firstFiltered) (secondAvailable : Available reader secondFiltered)
      (firstBuild : build expression (inputs.map (input firstNames)) firstBefore = .done firstRaw firstRawHeap)
      (secondBuild : build expression (inputs.map (input secondNames)) secondBefore = .done secondRaw secondRawHeap)
      (firstFilter : run (withoutSelfReference firstOwn firstRaw) firstRawHeap = (firstFiltered,firstFilterHeap))
      (secondFilter : run (withoutSelfReference secondOwn secondRaw) secondRawHeap = (secondFiltered,secondFilterHeap))
      (firstGrowth : Grows firstRawHeap reader) (secondGrowth : Grows secondRawHeap reader)
      (firstFilteredGrowth : Grows firstFilterHeap reader) (secondFilteredGrowth : Grows secondFilterHeap reader)
      (firstWarmBuild : build expression (inputs.map (input firstNames)) reader = .done firstRaw reader)
      (secondWarmBuild : build expression (inputs.map (input secondNames)) reader = .done secondRaw reader)
      (firstWarmFilter : run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered,reader))
      (secondWarmFilter : run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered,reader))
      (firstDone : execute firstFiltered firstMap reader = .done left reader)
      (secondDone : execute secondFiltered secondMap reader = .done right reader) :
      Generated reader left right

private theorem same_inputs (event : Publication (Symbol := Symbol) (Guard := Guard))
    (own : Reference) :
    (.inr (.inl ()) :: (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput).map
      (input (Sum.elim (fun _ : Unit => own) (fun _ : Unit => .depth))) = .reference own :: event.environment := by
  rw [local_inputs]
  simp [input,List.map_map,Function.comp_def]

private theorem replacements (reader : State Symbol Guard)
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (value : Value Symbol Guard) (available : Available reader value) :
    Replacements reader (shared event value value (fun _ => none)) := by
  intro name output found
  dsimp only [shared,SourceCurrentStoredMuBinderChildLineage.bind] at found
  split at found
  · cases found; exact available
  · split at found
    · cases found; exact available
    · cases found

private theorem paired_reverse (reader : State Symbol Guard)
    (event : Publication (Symbol := Symbol) (Guard := Guard)) (value : Value Symbol Guard) :
    Paired (Generated reader) (shared event value value (fun _ => none)) (shared event value value (fun _ => none))
      (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
      (.reference (.interned event.entry.identity) :: event.environment) := by
  have original := SourceCurrentPublicationSharedReplacements.paired event (Generated reader)
    (Generated.refl reader) value value (fun _ => none) (Generated.refl reader value)
  cases original with
  | cons head tail =>
      refine .cons ?_ tail
      simpa only [Slot,shared,SourceCurrentStoredMuBinderChildLineage.bind,ite_true,
        reduceCtorEq,ite_false,Option.getD_some] using Generated.refl reader value

end MicroCFTA.SourceCurrentRetainedMuDirectedCase
