import MicroCFTA.SourceCurrentInheritedOwnerProgress
import MicroCFTA.SourceCurrentNativeWriterChildOrigins

/-!
# Stored class origins in actual joined native rows

The full joined guard retains every active stored operand class inside an
effective own component, unless its accessor is contradictory. An actual
native writer supplies both original full fields. Two original paths in
one child therefore construct nonempty inherited data at that child.
New guard-only classes and transport across later class phases stay separate.
-/
namespace MicroCFTA.SourceCurrentOwnClassOrigin
open EqualityNormalize SourceEqualityClassOrder SourceEqualityConstraintAllocation
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "prefix" => SourceCurrentAllocatedInheritedPrefix.run

private theorem combine_covers (first second : Option Constraints)
    (firstActive : SourceCompactGuards.ActiveOption first)
    (secondActive : SourceCompactGuards.ActiveOption second)
    (output : Constraints) (actual : SourceCompactGuards.combineEqualities first second = some output) :
    Covers (first.getD [] ++ second.getD []) output := by
  cases first with
  | none => cases second <;> cases actual
  | some first =>
      cases second with
      | none => cases actual
      | some second =>
          have active : Active (first ++ second) := by
            intro paths member
            rcases List.mem_append.mp member with member | member
            · exact firstActive first rfl paths member
            · exact secondActive second rfl paths member
          cases first with
          | nil =>
              cases second with
              | nil =>
                  cases actual
                  intro paths impossible
                  cases impossible
              | cons head rest => exact SourceCurrentOuterOriginDependencies.normalize_covers _ _ actual active
          | cons head rest =>
              cases second <;> exact SourceCurrentOuterOriginDependencies.normalize_covers _ _ actual active

private theorem positive_active (guard : SourceGuards.Guard FullSyntax.Formula)
    (added : Option Constraints) (found : SourceCompactGuards.positiveNormalized guard = some added) :
    SourceCompactGuards.ActiveOption added := by
  have supported : (SourceCompactGuards.positive guard).isSome = true := by
    rw [← SourceCompactGuards.positiveNormalized_support guard, found]
    rfl
  obtain ⟨raw,extracted⟩ := Option.isSome_iff_exists.mp supported
  obtain ⟨result,actual,active,_⟩ := SourceCompactGuards.positiveNormalized_exact
    (Symbol := Unit) guard raw extracted
  have same := Option.some.inj (actual.symm.trans found)
  exact same ▸ active

private theorem source_covers (original : Guard)
    (active : SourceCompactGuards.ActiveOption original.equalities)
    (output : Constraints) (actual : SourceCompactGuards.sourceEqualities original = some output) :
    ∃ stored, original.equalities = some stored ∧ Covers stored output := by
  cases raw : original.equalities with
  | none =>
      have impossible : (none : Option Constraints) = some output := by
        cases found : SourceCompactGuards.positiveNormalized original.guard with
        | none => simpa only [SourceCompactGuards.sourceEqualities,found,raw] using actual
        | some added =>
            cases added with
            | none => simpa only [SourceCompactGuards.sourceEqualities,found,raw,
                SourceCompactGuards.combineEqualities] using actual
            | some added =>
                cases added <;> simpa only [SourceCompactGuards.sourceEqualities,found,raw,
                  SourceCompactGuards.combineEqualities] using actual
      cases impossible
  | some stored =>
      refine ⟨stored,rfl,?_⟩
      cases found : SourceCompactGuards.positiveNormalized original.guard with
      | none =>
          have same : stored = output := by
            simpa only [SourceCompactGuards.sourceEqualities,found,raw,Option.some.injEq] using actual
          subst output
          exact fun paths member => ⟨paths,member,fun _ present => present⟩
      | some added =>
          cases added with
          | none => simp only [SourceCompactGuards.sourceEqualities,found,raw,
              SourceCompactGuards.combineEqualities] at actual; cases actual
          | some added =>
              cases added with
              | nil =>
                  have same : stored = output := by
                    simpa only [SourceCompactGuards.sourceEqualities,found,raw,Option.some.injEq] using actual
                  subst output
                  exact fun paths member => ⟨paths,member,fun _ present => present⟩
              | cons head rest =>
                  have covered := combine_covers original.equalities (some (head :: rest)) active
                    (positive_active original.guard _ found) output
                    (by simpa only [SourceCompactGuards.sourceEqualities,found] using actual)
                  intro paths member
                  exact covered paths (List.mem_append_left _ (by simpa only [raw,Option.getD_some] using member))

/-- Effective joined own classes cover both original stored fields whenever the accessor is live. -/
theorem effective_covers (first second : Guard)
    (firstActive : SourceCompactGuards.ActiveOption first.equalities)
    (secondActive : SourceCompactGuards.ActiveOption second.equalities)
    (output : Constraints)
    (actual : SourceCompactGuards.sourceEqualities (SourceEqualityPCSNativeEdge.conjoin first second) = some output) :
    Covers (first.equalities.getD [] ++ second.equalities.getD []) output := by
  obtain ⟨stored,raw,covered⟩ := source_covers (SourceEqualityPCSNativeEdge.conjoin first second)
    (SourceCompactGuards.combine_active first.equalities second.equalities) output actual
  exact covers_trans _ _ _ (combine_covers first.equalities second.equalities firstActive secondActive stored raw) covered

private theorem contradictory_split (original : Guard) (inherited : Value) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (ready : Ready before.constraints inherited)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (contradictory : SourceCompactGuards.sourceEqualities original = none) (index : Nat) :
    ∃ combined,
      (prefix original inherited before).1 = .ok (some combined) ∧
      let middle := (prefix original inherited before).2
      SourceEqualityConstraintMemoAllocation.Valid middle ∧ Ready middle.constraints combined ∧
      SourceEqualityConstraintMemoAllocation.Grows before middle ∧
      let child := SourceEqualityConstraintMemoAllocation.descend combined index middle
      SourceEqualityConstraintMemoAllocation.Valid child.2 ∧ Ready child.2.constraints child.1 ∧
      SourceEqualityConstraintMemoAllocation.Grows middle child.2 ∧ child.1.payload ≠ some [] := by
  cases inherited with
  | contradiction =>
      exact ⟨.contradiction,rfl,valid,ready,SourceEqualityConstraintMemoAllocation.grows_refl _,
        valid,ready,SourceEqualityConstraintMemoAllocation.grows_refl _,by
          change (none : Option (List SourceEqualityClassOrder.Record)) ≠ some []
          simp⟩
  | live identity records =>
      obtain ⟨own,loaded,accessorValid,ownReady,classes,_,growth⟩ :=
        SourceCurrentConjunctionEquality.accessor_correct original before valid field
      have ownIsContradiction : own = .contradiction := by
        cases own with
        | contradiction => rfl
        | live identity records => simp only [SourceEqualityInheritedPayload.classes,Value.payload,
            Option.map_some] at classes; rw [contradictory] at classes; cases classes
      subst own
      have actual := SourceCurrentAllocatedInheritedPrefix.run_combine original identity records before .contradiction loaded
      simp only [SourceEqualityConstraintMemoAllocation.combine,Except.map] at actual
      refine ⟨.contradiction,congrArg Prod.fst actual,?_⟩
      simp only [actual,SourceEqualityConstraintMemoAllocation.descend]
      exact ⟨accessorValid,ownReady,growth,accessorValid,ownReady,
        SourceEqualityConstraintMemoAllocation.grows_refl _,by simp [Value.payload]⟩

open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- An actual joined row derives its child obligation from either captured stored field. -/
theorem native_split (reader : Checked width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good reader)
    (handle : Nat) (request : SourceRecursiveIntersectionThunks.EdgeRequest Symbol Guard)
    (result : EdgeValue Symbol Guard)
    (written : SourceCurrentNativeEdgeWriterGrowth.Written (width := width) handle request result reader.native.machine.heap)
    (resident : EdgeResident reader.native.machine.heap result)
    (survives : Value.empty ∉ result.children)
    (inherited : SourceEqualityConstraintAllocation.Value)
    (ready : SourceEqualityConstraintAllocation.Ready reader.operations.constraints inherited)
    (paths : Class)
    (origin : paths ∈ request.left.entry.key.constraint.equalities.getD [] ++
      request.right.entry.key.constraint.equalities.getD [])
    (index : Nat) (left right : Path) (first : index :: left ∈ paths)
    (second : index :: right ∈ paths) (different : left ≠ right) :
    result.entry.key.constraint = SourceEqualityPCSNativeEdge.conjoin
      request.left.entry.key.constraint request.right.entry.key.constraint ∧
    ∃ combined,
      (prefix result.entry.key.constraint inherited reader.operations).1 = .ok (some combined) ∧
      let middle := (prefix result.entry.key.constraint inherited reader.operations).2
      SourceEqualityConstraintMemoAllocation.Valid middle ∧ SourceEqualityConstraintAllocation.Ready middle.constraints combined ∧
      SourceEqualityConstraintMemoAllocation.Grows reader.operations middle ∧
      let child := SourceEqualityConstraintMemoAllocation.descend combined index middle
      SourceEqualityConstraintMemoAllocation.Valid child.2 ∧ SourceEqualityConstraintAllocation.Ready child.2.constraints child.1 ∧
      SourceEqualityConstraintMemoAllocation.Grows middle child.2 ∧ child.1.payload ≠ some [] := by
  obtain ⟨before,_,_,_,beforeGood,beforeReady,_,_,_,_,_,_,_,_,_,_,guard⟩ :=
    SourceCurrentNativeWriterChildOrigins.live written survives
  refine ⟨guard,?_⟩
  have field := good.fields _ _ resident
  by_cases contradictory : SourceCompactGuards.sourceEqualities result.entry.key.constraint = none
  · exact contradictory_split _ _ _ good.operations ready field contradictory index
  · obtain ⟨output,actual⟩ := Option.ne_none_iff_exists.mp contradictory
      have covered := effective_covers request.left.entry.key.constraint request.right.entry.key.constraint
        (SourceEqualityGuardReadback.active (beforeGood.fields _ _ beforeReady.2.1).1)
        (SourceEqualityGuardReadback.active (beforeGood.fields _ _ beforeReady.2.2).1) output
        (by simpa only [← guard] using actual)
      obtain ⟨component,member,included⟩ := covered paths origin
      exact SourceCurrentInheritedOwnerProgress.selected_split _ _ _ good.operations ready field component
        (by simpa only [actual,Option.getD_some] using member) index left right
        (included _ first) (included _ second) different

end MicroCFTA.SourceCurrentOwnClassOrigin
