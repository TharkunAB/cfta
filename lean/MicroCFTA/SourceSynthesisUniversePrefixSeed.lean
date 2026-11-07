import MicroCFTA.SourceSynthesisUniverseFirstFrame
import MicroCFTA.InternedFreshOrdinaryReplay
import MicroCFTA.InternedBoundaryAtoms

/-!
# The first universe in an actual constructor prefix

A prefix can allocate ordinary records before its first universe call.
The first call supplies the actual Mu identity and its resident rows.
Later calls replay that complete build through actual heap growth.
These predicates are internal conditions for constructor induction.
-/
namespace MicroCFTA.SourceSynthesisUniversePrefixSeed
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (Reference NodeKey)
open InternedRecordCoherence (Covered)
open InternedShallowHeap (NoNewMu noNewMu_trans)
open SourceSynthesisTypeSyntax
open SourceSynthesisUniverseResidentRows (Rows)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- A seed retains one actual complete build and its three resident row packets. -/
structure Seed (top : Guard) (catalog : List (String × Nat)) where
  entry : Interned NodeKey
  body : Value String Guard
  depth : Value String Guard
  ordinary : Value String Guard
  start : InternedConstructorTemplates.State String Guard
  builtHeap : InternedConstructorTemplates.State String Guard
  startFacts : Facts start
  built : InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] start =
    .done (.mu entry body depth ordinary) builtHeap
  bodyRows : Rows top catalog (.interned entry.identity) body builtHeap
  depthRows : Rows top catalog .depth depth builtHeap
  ordinaryRows : Rows top catalog
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary builtHeap

variable {top : Guard} {catalog : List (String × Nat)}

/-- The value is the literal complete Mu from the retained source build. -/
def Seed.value (seed : Seed top catalog) : Value String Guard :=
  .mu seed.entry seed.body seed.depth seed.ordinary

/-- The retained actual build derives all final record invariants. -/
theorem Seed.facts (seed : Seed top catalog) : Facts seed.builtHeap := by
  have checked := InternedFreshOrdinaryFacts.build_verified (allTypes top catalog) []
    seed.start seed.startFacts (by intro value member; cases member)
  simpa only [seed.built, Outcome.state] using checked.facts

/-- The retained source computation derives complete Mu availability. -/
theorem Seed.available (seed : Seed top catalog) : Available seed.builtHeap seed.value := by
  have checked := InternedFreshOrdinaryFacts.build_verified (allTypes top catalog) []
    seed.start seed.startFacts (by intro value member; cases member)
  exact checked.result seed.value seed.builtHeap seed.built

/-- The retained source computation preserves every earlier record. -/
theorem Seed.growth (seed : Seed top catalog) : Grows seed.start seed.builtHeap := by
  have checked := InternedFreshOrdinaryFacts.build_verified (allTypes top catalog) []
    seed.start seed.startFacts (by intro value member; cases member)
  simpa only [seed.built, Outcome.state] using checked.growth

/-- A prefix either has no Mu record or retains its selected complete build. -/
def Ready (pick : Option (Seed top catalog)) (current : InternedConstructorTemplates.State String Guard) : Prop :=
  match pick with
  | none => NoNewMu empty current
  | some seed => Grows seed.builtHeap current

/-- Every boundary atom must refer to the selected actual universe. -/
def Allowed (pick : Option (Seed top catalog)) (value : Value String Guard) : Prop :=
  match pick with
  | none => ∀ atom ∈ InternedBoundaryAtoms.atoms value, False
  | some seed => ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu seed.entry.identity

/-- A prefix selects its first seed once and retains that seed afterward. -/
def Advances (old new : Option (Seed top catalog)) : Prop := old = none ∨ new = old

/-- Retaining a selection satisfies the source selection relation. -/
theorem advances_refl (pick : Option (Seed top catalog)) : Advances pick pick :=
  Or.inr rfl

/-- Consecutive source prefixes retain the first selected seed. -/
theorem advances_trans {old middle new : Option (Seed top catalog)}
    (first : Advances old middle) (second : Advances middle new) : Advances old new := by
  rcases first with absent | same
  · exact Or.inl absent
  · subst middle
    exact second

/-- Earlier output atoms remain allowed after the first seed is selected. -/
theorem allowed_advances {old new : Option (Seed top catalog)} {value : Value String Guard}
    (advance : Advances old new) (allowed : Allowed old value) : Allowed new value := by
  rcases advance with absent | same
  · subst old
    cases new with
    | none => exact allowed
    | some seed =>
        intro atom member
        exact False.elim (allowed atom member)
  · subst new
    exact allowed

/-- Empty has no boundary atom for any seed selection. -/
theorem allowed_empty (pick : Option (Seed top catalog)) : Allowed pick (.empty : Value String Guard) := by
  cases pick <;> simp [Allowed, InternedBoundaryAtoms.atoms]

/-- The retained literal Mu has exactly its selected boundary identity. -/
theorem allowed_value (seed : Seed top catalog) : Allowed (some seed) seed.value := by
  intro atom member
  simpa only [Seed.value, InternedBoundaryAtoms.atoms, List.mem_singleton] using member

/-- Ordinary growth preserves both possible prefix states. -/
theorem ready_grows {pick : Option (Seed top catalog)}
    {before after : InternedConstructorTemplates.State String Guard}
    (ready : Ready pick before) (growth : Grows before after) (muFree : NoNewMu before after) :
    Ready pick after := by
  cases pick with
  | none => exact noNewMu_trans ready muFree
  | some seed => exact grows_trans ready growth

/-- An actual edge request changes no Mu record. -/
theorem ready_makeEdge (pick : Option (Seed top catalog)) (symbol : String) (constraint : Guard)
    (children : List (Value String Guard)) (current : InternedConstructorTemplates.State String Guard)
    (valid : Valid current) (ready : Ready pick current) :
    Ready pick (run (makeEdge symbol constraint children) current).2 := by
  have muFree : NoNewMu current (run (makeEdge symbol constraint children) current).2 := by
    intro key entry body depth ordinary stored
    exact stored
  exact ready_grows ready (run_correct (makeEdge symbol constraint children) current valid).2 muFree

/-- Actual node normalization preserves the selected universe history. -/
theorem ready_makeNode (pick : Option (Seed top catalog)) (rows : List (EdgeValue String Guard))
    (current : InternedConstructorTemplates.State String Guard) (valid : Valid current)
    (ready : Ready pick current) : Ready pick (run (makeNode rows) current).2 :=
  ready_grows ready (run_correct (makeNode rows) current valid).2
    (InternedShallowHeap.makeNode_noNewMu rows current)

/-- Every actual union branch preserves the selected universe history. -/
theorem ready_makeUnion (pick : Option (Seed top catalog)) (values : List (Value String Guard))
    (current : InternedConstructorTemplates.State String Guard) (valid : Valid current)
    (ready : Ready pick current) : Ready pick (run (makeUnion values) current).2 :=
  ready_grows ready (run_correct (makeUnion values) current valid).2
    (InternedShallowHeap.makeUnion_noNewMu values current)

/-- The actual atom call selects its first seed or replays the selected build. -/
theorem atom_complete (top : Guard) (catalog : List (String × Nat))
    (pick : Option (Seed top catalog)) (current : InternedConstructorTemplates.State String Guard)
    (facts : Facts current) (covered : Covered [] current) (ready : Ready pick current) :
    ∃ (seed : Seed top catalog) (after : InternedConstructorTemplates.State String Guard),
      InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] current = .done seed.value after ∧
      Ready (some seed) after ∧ Advances pick (some seed) ∧ Allowed (some seed) seed.value ∧
      Grows current after := by
  cases pick with
  | none =>
      obtain ⟨entry, body, depth, ordinary, after, built, _afterFacts, _available, _shape,
          bodyRows, depthRows, ordinaryRows, growth, _history⟩ :=
        SourceSynthesisUniverseFirstFrame.allTypes_first_frame top catalog current facts covered ready
      let seed : Seed top catalog := {
        entry := entry
        body := body
        depth := depth
        ordinary := ordinary
        start := current
        builtHeap := after
        startFacts := facts
        built := built
        bodyRows := bodyRows
        depthRows := depthRows
        ordinaryRows := ordinaryRows }
      exact ⟨seed, after, built, grows_refl after, Or.inl rfl, allowed_value seed, growth⟩
  | some seed =>
      have replayed := InternedFreshOrdinaryReplay.build_replay (allTypes top catalog) []
        seed.start current seed.value seed.builtHeap seed.startFacts.coherent.valid seed.built ready
      exact ⟨seed, current, replayed, ready, advances_refl (some seed), allowed_value seed, grows_refl current⟩

end MicroCFTA.SourceSynthesisUniversePrefixSeed
