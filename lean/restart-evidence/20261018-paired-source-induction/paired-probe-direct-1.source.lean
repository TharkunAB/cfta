import MicroCFTA.SourceCurrentStoredPairedOrdinaryLineage
import MicroCFTA.SourceCurrentNativeNormalizationFreshness

/-!
# Lexical compatibility on actual live probe support

Unused captures can contain the chosen ordinary marker. The actual Depth
callback proves freshness on live source support. This support suffices
for compatible lexical extension. The Depth marker requires a separate
live alias condition. This module does not compare completed Mu results.
-/
namespace MicroCFTA.SourceCurrentStoredProbeCompatibility
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryLiveInputs
open InternedStoredSubstitution (Environment)
open InternedBinderProtocol (Reference)
open SourceCurrentNativeNormalizationInputs (support)
open SourceCurrentStoredMuBinderChildLineage (Paired Slot bind)
open SourceCurrentNativeMuPublication (Publication)
open Language

variable {Atom : Type}

/-- Only surviving fixed names and varying labels constrain the two lexical maps. -/
def Compatible (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Environment Symbol Guard) : Prop :=
  (∀ name, .inl name ∈ support expression inputs → first name = second name) ∧
  ∀ atom, .inr atom ∈ support expression inputs →
    (first (firstNames atom)).getD (.reference (firstNames atom)) =
      (second (secondNames atom)).getD (.reference (secondNames atom))

private theorem varying_origin (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (atom : Atom)
    (member : .inr atom ∈ support expression inputs) : .inr atom ∈ inputs := by
  obtain ⟨names,present,included⟩ := InternedFreeNameSemantics.evaluate_origins expression
    (inputs.map inputProfile) (inputs.map SourceCurrentNativeNormalizationInputs.inputNames) (.inr atom) member
  obtain ⟨selected,source,same⟩ := List.mem_map.mp present
  rw [← same] at included
  cases selected with
  | inl value =>
      obtain ⟨name,_,impossible⟩ := List.mem_map.mp included
      cases impossible
  | inr other =>
      have same : other = atom := by simpa only [SourceCurrentNativeNormalizationInputs.inputNames,
        List.mem_singleton,Sum.inr.injEq] using included
      exact same ▸ source

private theorem compatible_inputs (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Environment Symbol Guard)
    (fixed : ∀ value, .inl value ∈ inputs → ∀ name ∈ value.free, first name = second name)
    (varying : ∀ atom, .inr atom ∈ inputs →
      (first (firstNames atom)).getD (.reference (firstNames atom)) =
        (second (secondNames atom)).getD (.reference (secondNames atom)))
    (expression : Syntax Symbol Guard) : Compatible expression inputs firstNames secondNames first second := by
  constructor
  · intro name member
    obtain ⟨value,present,included⟩ := SourceCurrentNativeNormalizationInputs.fixed_origin expression inputs name member
    exact fixed value present name included
  · intro atom member
    exact varying atom (varying_origin expression inputs atom member)

private theorem presentation (first second : Environment Symbol Guard)
    (left right : List (Value Symbol Guard)) (paired : Paired first second left right) :
    ∃ inputs : List (Sum (Value Symbol Guard) (Reference × Reference)),
      inputs.map (input Prod.fst) = left ∧ inputs.map (input Prod.snd) = right ∧
      (∀ value, .inl value ∈ inputs → ∀ name ∈ value.free, first name = second name) ∧
      (∀ atom, .inr atom ∈ inputs →
        (first atom.1).getD (.reference atom.1) = (second atom.2).getD (.reference atom.2)) := by
  induction paired with
  | nil => exact ⟨[],rfl,rfl,by simp,by simp⟩
  | @cons left right lefts rights slot tail ih =>
      obtain ⟨inputs,leftSame,rightSame,fixed,varying⟩ := ih
      cases left <;> cases right
      all_goals try {cases slot}
      case reference.reference a b =>
        refine ⟨.inr (a,b) :: inputs,by simpa [input] using leftSame,
          by simpa [input] using rightSame,?_,?_⟩
        · intro value member name free
          exact fixed value (by simpa only [List.mem_cons,Sum.inr_ne_inl,false_or] using member) name free
        · intro atom member
          rcases List.mem_cons.mp member with same | later
          · cases same
            exact slot
          · exact varying atom later
      all_goals obtain ⟨same,agree⟩ := slot
      all_goals cases same
      all_goals
        refine ⟨.inl _ :: inputs,
          by simpa only [List.map_cons,input] using congrArg (List.cons _) leftSame,
          by simpa only [List.map_cons,input] using congrArg (List.cons _) rightSame,?_,?_⟩
        · intro value member name free
          rcases List.mem_cons.mp member with same | later
          · cases same
            exact agree name free
          · exact fixed value later name free
        · intro atom member
          exact varying atom (by simpa only [List.mem_cons,Sum.inl_ne_inr,false_or] using member)

/-- Paired lexical inputs supply one presentation with compatible support for every source expression. -/
theorem paired_inputs (first second : Environment Symbol Guard)
    (left right : List (Value Symbol Guard)) (paired : Paired first second left right) :
    ∃ inputs : List (Sum (Value Symbol Guard) (Reference × Reference)),
      inputs.map (input Prod.fst) = left ∧ inputs.map (input Prod.snd) = right ∧
      ∀ expression : Syntax Symbol Guard, Compatible expression inputs Prod.fst Prod.snd first second := by
  obtain ⟨inputs,leftSame,rightSame,fixed,varying⟩ := presentation first second left right paired
  exact ⟨inputs,leftSame,rightSame,compatible_inputs inputs Prod.fst Prod.snd first second fixed varying⟩

/-- Synchronized aliases extend compatibility on the exact support of the entered body. -/
theorem extend (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Environment Symbol Guard)
    (compatible : Compatible (.binder true body) inputs firstNames secondNames first second)
    (firstArgument secondArgument : Reference) (replacement : Value Symbol Guard)
    (aliases : ∀ label ∈ support (.binder true body) inputs,
      Sum.elim id firstNames label = firstArgument ↔ Sum.elim id secondNames label = secondArgument) :
    Compatible body (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ => firstArgument) firstNames) (Sum.elim (fun _ => secondArgument) secondNames)
      (bind firstArgument replacement first) (bind secondArgument replacement second) := by
  constructor
  · intro name member
    have captured := (SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inl name)).mp member
    have alias := aliases (.inl name) captured
    change name = firstArgument ↔ name = secondArgument at alias
    by_cases left : name = firstArgument
    · have right := alias.mp left
      simp only [bind,left,right,ite_true]
    · have right : name ≠ secondArgument := fun same => left (alias.mpr same)
      simp only [bind,left,right,ite_false,compatible.1 name captured]
  · intro atom member
    cases atom with
    | inl token => simp only [Sum.elim_inl,bind,ite_true,Option.getD_some]
    | inr atom =>
        have captured := (SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inr atom)).mp member
        have alias := aliases (.inr atom) captured
        change firstNames atom = firstArgument ↔ secondNames atom = secondArgument at alias
        by_cases left : firstNames atom = firstArgument
        · have right := alias.mp left
          simp only [Sum.elim_inr,bind,left,right,ite_true,Option.getD_some]
        · have right : secondNames atom ≠ secondArgument := fun same => left (alias.mpr same)
          simpa only [Sum.elim_inr,bind,left,right,ite_false] using compatible.2 atom captured

/-- Both actual Depth callbacks derive the live freshness needed for ordinary-probe extension. -/
theorem publication_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (firstEvent secondEvent : Publication (Symbol := Symbol) (Guard := Guard))
    (sameBody : secondEvent.expression = firstEvent.expression)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstInputs : inputs.map (input firstNames) = firstEvent.environment)
    (secondInputs : inputs.map (input secondNames) = secondEvent.environment)
    (first second : Environment Symbol Guard)
    (compatible : Compatible (.binder true firstEvent.expression) inputs firstNames secondNames first second)
    (replacement : Value Symbol Guard) :
    Compatible firstEvent.expression (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ => .uninterned (InternedNestedConstruction.ordinaryLevel firstEvent.depth)) firstNames)
      (Sum.elim (fun _ => .uninterned (InternedNestedConstruction.ordinaryLevel secondEvent.depth)) secondNames)
      (bind (.uninterned (InternedNestedConstruction.ordinaryLevel firstEvent.depth)) replacement first)
      (bind (.uninterned (InternedNestedConstruction.ordinaryLevel secondEvent.depth)) replacement second) := by
  have firstFresh := SourceCurrentNativeNormalizationFreshness.ordinary firstEvent.expression inputs firstNames
    firstEvent.before firstEvent.afterDepth (firstInputs ▸ firstEvent.context.base) firstEvent.depth
    (firstInputs ▸ firstEvent.depthDone)
  have secondFresh := SourceCurrentNativeNormalizationFreshness.ordinary firstEvent.expression inputs secondNames
    secondEvent.before secondEvent.afterDepth (secondInputs ▸ secondEvent.context.base) secondEvent.depth
    (by rw [← sameBody,secondInputs]; exact secondEvent.depthDone)
  apply extend firstEvent.expression inputs firstNames secondNames first second compatible _ _ replacement
  intro label member
  constructor
  · intro same
    exact False.elim (firstFresh (List.mem_map.mpr ⟨label,member,same⟩))
  · intro same
    exact False.elim (secondFresh (List.mem_map.mpr ⟨label,member,same⟩))

end MicroCFTA.SourceCurrentStoredProbeCompatibility
