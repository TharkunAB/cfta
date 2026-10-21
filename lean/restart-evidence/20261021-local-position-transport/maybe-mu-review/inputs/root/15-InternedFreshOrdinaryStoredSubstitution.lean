import MicroCFTA.InternedFreshOrdinaryConstruction
import MicroCFTA.MergedPhysicalWarmup

/-!
# Repaired stored substitution agrees on prepared binder-free plans

Preparation retains closed Mu records as input leaves. No binder request
occurs in this fragment, so changing ordinary probe selection cannot change
any returned value, failure, or cache effect of stored reconstruction.
-/
namespace MicroCFTA.InternedFreshOrdinaryStoredSubstitution
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedStoredSubstitution (Environment leaves input encode)
open InternedStoredShallowCompletion (BinderFree ManyBinderFree EdgesBinderFree)
open InternedStoredClosedMuCompletion (PreparedWithoutMu encode_withoutMu)
open MergedPhysicalWarmup

mutual
/-- A plan with no binder requests has exactly the same execution in both schedulers. -/
theorem build_eq [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (free : BinderFree expression) :
    InternedFreshOrdinaryConstruction.build expression environment state =
      InternedNestedConstruction.build expression environment state := by
  cases expression with
  | empty | var => simp only [InternedFreshOrdinaryConstruction.build, InternedNestedConstruction.build]
  | binder => simp [BinderFree] at free
  | node edges =>
      simp only [BinderFree] at free
      simp only [InternedFreshOrdinaryConstruction.build, InternedNestedConstruction.build,
        buildEdges_eq edges environment state free]
  | union members =>
      simp only [BinderFree] at free
      simp only [InternedFreshOrdinaryConstruction.build, InternedNestedConstruction.build,
        buildMany_eq members environment state free]
termination_by sizeOf expression

/-- Ordered child plans retain identical intermediate and final caches. -/
theorem buildMany_eq [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (free : ManyBinderFree expressions) :
    InternedFreshOrdinaryConstruction.buildMany expressions environment state =
      InternedNestedConstruction.buildMany expressions environment state := by
  cases expressions with
  | nil => simp only [InternedFreshOrdinaryConstruction.buildMany, InternedNestedConstruction.buildMany]
  | cons first rest =>
      simp only [ManyBinderFree] at free
      simp only [InternedFreshOrdinaryConstruction.buildMany, InternedNestedConstruction.buildMany,
        build_eq first environment state free.1]
      cases done : InternedNestedConstruction.build first environment state with
      | pending => rfl
      | done value after => simp only [Outcome.bind, buildMany_eq rest environment after free.2]
termination_by sizeOf expressions

/-- Ordered edge plans use the identical ordinary constructors in both schedulers. -/
theorem buildEdges_eq [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (free : EdgesBinderFree expressions) :
    InternedFreshOrdinaryConstruction.buildEdges expressions environment state =
      InternedNestedConstruction.buildEdges expressions environment state := by
  cases expressions with
  | nil => simp only [InternedFreshOrdinaryConstruction.buildEdges, InternedNestedConstruction.buildEdges]
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesBinderFree] at free
          simp only [InternedFreshOrdinaryConstruction.buildEdges, InternedNestedConstruction.buildEdges,
            buildMany_eq children environment state free.1]
          cases done : InternedNestedConstruction.buildMany children environment state with
          | pending => rfl
          | done values after =>
              simp only [Outcome.bind, work,
                buildEdges_eq rest environment (run (makeEdge symbol constraint values) after).2 free.2]
termination_by sizeOf expressions
end

/-- Execute the same stored plan with the repaired ordinary-probe scheduler. -/
def execute [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  InternedFreshOrdinaryConstruction.build (encode (leaves value) [] value) ((leaves value).map (input environment)) state

/-- Repaired source unfolding replaces the same outer recursive reference. -/
def unfold [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (state : State Symbol Guard) :
    Outcome Symbol Guard (Value Symbol Guard) :=
  match value with
  | .mu entry body _ _ => execute body (fun name => if name = .interned entry.identity then some value else none) state
  | _ => .done value state

/-- Preparation derives exact stored-executor equality without cache assumptions. -/
theorem execute_eq [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (prepared : PreparedWithoutMu value) :
    execute value environment state = InternedStoredSubstitution.execute value environment state :=
  build_eq _ _ state (encode_withoutMu (leaves value) [] value prepared)

/-- A prepared outer Mu has identical actual unfolding and cache effects after the repair. -/
theorem unfold_mu_eq [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (prepared : PreparedWithoutMu body) :
    unfold (.mu entry body depth ordinary) state = InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state :=
  execute_eq body _ state prepared

/-- Every available record in the prepared fragment has the same repaired cold unfolding. -/
theorem unfold_eq [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard) (state : State Symbol Guard)
    (prepared : Prepared state) (available : Available state value) :
    unfold value state = InternedStoredSubstitution.unfold value state := by
  cases value with
  | empty | reference | node | union => rfl
  | mu entry body depth ordinary =>
      exact unfold_mu_eq entry body depth ordinary state
        (prepared entry.key entry body depth ordinary (available.resident entry rfl))

end MicroCFTA.InternedFreshOrdinaryStoredSubstitution
