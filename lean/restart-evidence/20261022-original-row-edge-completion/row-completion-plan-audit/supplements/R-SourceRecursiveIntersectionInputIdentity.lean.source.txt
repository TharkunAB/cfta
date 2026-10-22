import MicroCFTA.SourceRecursiveIntersectionInputBounds

/-!
# Canonical identities of closed original physical inputs

Actual payload reads select the canonical representative of each reachable
identity. Recursive references select their original Mu record. The finite
tagged carrier supplies a bound, not a validity assertion for every tag.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule

/-- Read the actual canonical constructor at an issued identity. -/
def representative (state : InternedConstructorTemplates.State Symbol Guard) (name : Nat) : Input :=
  inputOf ((SourcePreparedSharedRows.read state name).getD .empty)

/-- Nonprimitive original payloads retain their exact canonical source identity. -/
theorem representative_record (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (available : Available state value) (name : Nat)
    (reference : SourcePreparedSharedRows.reference value = some name) :
    representative state name = inputOf value := by
  simp only [representative, SourcePreparedSharedRows.read_identity state facts value available name reference, Option.getD_some]

/-- A closed-root reachable input has its actual constructor as the canonical identity representative. -/
theorem closed_representative (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (root input : Input) (original : OriginalInput state root)
    (isClosed : closed (view state holds) root = true) (reachable : InputReach (view state holds) root input)
    (nonempty : input ≠ .empty) : representative state (identity input) = inputRepresentative input := by
  have current := closed_reach_original state facts holds root input original isClosed reachable
  cases input with
  | empty => exact False.elim (nonempty rfl)
  | ref name =>
      have binder := closed_reach_original state facts holds root (.mu name) original isClosed (.reference reachable)
      obtain ⟨value, original, available, complete⟩ := binder
      cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
      case mu entry body depth ordinary original =>
        cases complete
        exact representative_record state facts _ available entry.identity rfl
  | node name | mu name | union name =>
      obtain ⟨value, original, available, complete⟩ := current
      cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
      all_goals
        cases complete
        exact representative_record state facts _ available _ rfl

/-- The actual reachable input domain of two roots excludes unused tagged carrier entries. -/
def Reachable (state : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (leftRoot rightRoot input : Input) : Prop :=
  InputReach (view state holds) leftRoot input ∨ InputReach (view state holds) rightRoot input

/-- Two closed original roots give canonical representatives throughout their actual reachable domain. -/
theorem reachable_identity (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (leftRoot rightRoot : Input)
    (leftOriginal : OriginalInput state leftRoot) (rightOriginal : OriginalInput state rightRoot)
    (leftClosed : closed (view state holds) leftRoot = true) (rightClosed : closed (view state holds) rightRoot = true)
    (input : Input) (reachable : Reachable state holds leftRoot rightRoot input) (nonempty : input ≠ .empty) :
    representative state (identity input) = inputRepresentative input := by
  rcases reachable with left | right
  · exact closed_representative state facts holds leftRoot input leftOriginal leftClosed left nonempty
  · exact closed_representative state facts holds rightRoot input rightOriginal rightClosed right nonempty

/-- Direct Mu body reads remain in the actual reachable domain of two roots. -/
theorem Reachable.body (state : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (leftRoot rightRoot : Input) (name : Nat) (reachable : Reachable state holds leftRoot rightRoot (.mu name)) :
    Reachable state holds leftRoot rightRoot ((view state holds).body name) := by
  rcases reachable with left | right
  · exact .inl (.body left)
  · exact .inr (.body right)

/-- Recursive reference resolution remains in the actual reachable domain of two roots. -/
theorem Reachable.reference (state : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (leftRoot rightRoot : Input) (name : Nat) (reachable : Reachable state holds leftRoot rightRoot (.ref name)) :
    Reachable state holds leftRoot rightRoot (.mu name) := by
  rcases reachable with left | right
  · exact .inl (.reference left)
  · exact .inr (.reference right)

/-- Actual ordered row children remain in the reachable domain of two roots. -/
theorem Reachable.child (state : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (leftRoot rightRoot : Input) (name : Nat) (reachable : Reachable state holds leftRoot rightRoot (.node name))
    (row : Row Symbol) (present : row ∈ (view state holds).rows name) (input : Input) (member : input ∈ row.children) :
    Reachable state holds leftRoot rightRoot input := by
  rcases reachable with left | right
  · exact .inl (.child left present member)
  · exact .inr (.child right present member)

/-- Actual union members remain in the reachable domain of two roots. -/
theorem Reachable.member (state : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (leftRoot rightRoot : Input) (name : Nat) (reachable : Reachable state holds leftRoot rightRoot (.union name))
    (input : Input) (member : input ∈ (view state holds).members name) : Reachable state holds leftRoot rightRoot input := by
  rcases reachable with left | right
  · exact .inl (.member left member)
  · exact .inr (.member right member)

end MicroCFTA.SourceRecursiveIntersectionInputView
