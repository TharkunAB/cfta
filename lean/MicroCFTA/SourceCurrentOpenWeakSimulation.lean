import MicroCFTA.SourceCurrentOpenOriginSteps
import MicroCFTA.SourceCurrentReaderObservations

/-!
# Local weak simulation at one reader

A simulation preserves literal references and physical rows. Each left
epsilon step can use any finite right path. Counted paths derive complete
reference and row observations. Two directions give every finite Same
observation. Physical Empty agreement remains a separate premise.
The reader does not change. No source alignment instance is assumed.
-/
namespace MicroCFTA.SourceCurrentOpenWeakSimulation
open InternedConstructorTemplates InternedEdgeResidency
open InternedBinderProtocol (Reference)
open MergedFreshOrdinaryGraph (Origin successors)
open SourceCurrentOpenObservations (ReferenceOrigin RowMatch Same)
open SourceCurrentOpenOriginSteps (Path path_of_reachable)
open Productivity (Reachable)
open Language

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Local laws match references, physical rows, and each immediate epsilon step. -/
def Forward (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) : Prop :=
  ∀ first second, relation first second →
    (∀ name : Reference, first = .reference name → ReferenceOrigin reader [second] name) ∧
    (∀ row ∈ nodeEdges first, ∃ other, Origin reader [second] other ∧ RowMatch relation row other) ∧
    ∀ next ∈ successors reader first, ∃ later,
      Reachable (successors reader) [second] later ∧ relation next later

/-- A counted left path has a reached right endpoint in the local relation. -/
theorem Forward.path (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Forward reader relation)
    {steps : Nat} {first second last : Value Symbol Guard} (related : relation first second)
    (actual : Path reader steps first last) :
    ∃ later, Reachable (successors reader) [second] later ∧ relation last later := by
  induction steps generalizing first second with
  | zero =>
      cases actual
      exact ⟨second,.seed List.mem_cons_self,related⟩
  | succ steps ih =>
      obtain ⟨next,member,tail⟩ := actual
      obtain ⟨middle,reached,nextRelated⟩ := (simulation first second related).2.2 next member
      obtain ⟨later,following,lastRelated⟩ := ih nextRelated tail
      exact ⟨later,EpsilonUnion.reach_trans _ second middle later reached following,lastRelated⟩

/-- Local simulation preserves every complete bare-reference observation. -/
theorem Forward.reference (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Forward reader relation)
    {first second : Value Symbol Guard} (related : relation first second) (name : Reference)
    (origin : ReferenceOrigin reader [first] name) : ReferenceOrigin reader [second] name := by
  obtain ⟨source,member,steps,path⟩ := path_of_reachable reader [first] (.reference name) origin
  obtain rfl := List.mem_singleton.mp member
  obtain ⟨later,reached,lastRelated⟩ := simulation.path reader relation related path
  exact EpsilonUnion.reach_trans _ second later (.reference name) reached
    ((simulation _ later lastRelated).1 name rfl)

/-- Local simulation preserves complete row origins with full fields and ordered related children. -/
theorem Forward.row (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (simulation : Forward reader relation)
    {first second : Value Symbol Guard} (related : relation first second) (row : EdgeValue Symbol Guard)
    (origin : Origin reader [first] row) :
    ∃ other, Origin reader [second] other ∧ RowMatch relation row other := by
  obtain ⟨last,actual,physical⟩ := origin
  obtain ⟨source,member,steps,path⟩ := path_of_reachable reader [first] last actual
  obtain rfl := List.mem_singleton.mp member
  obtain ⟨later,reached,lastRelated⟩ := simulation.path reader relation related path
  obtain ⟨other,found,fields⟩ := (simulation last later lastRelated).2.1 row physical
  exact ⟨other,found.from_seeds reader [later] [second]
    (fun value member => (List.mem_singleton.mp member) ▸ reached) other,fields⟩

/-- Simulations in both directions give every finite observation at the same reader. -/
theorem same (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (forward : Forward reader relation)
    (backward : Forward reader (fun right left => relation left right)) (depth : Nat) :
    ∀ first second, relation first second → Same depth reader [first] [second] := by
  induction depth with
  | zero =>
      intro first second related name
      exact ⟨forward.reference reader relation related name,
        backward.reference reader (fun right left => relation left right) related name⟩
  | succ depth ih =>
      intro first second related
      refine ⟨?_,?_,?_⟩
      · intro name
        exact ⟨forward.reference reader relation related name,
          backward.reference reader (fun right left => relation left right) related name⟩
      · intro row origin
        obtain ⟨other,found,fields⟩ := forward.row reader relation related row origin
        exact ⟨other,found,fields.1,fields.2.1,All₂.imp (fun _ _ pair => ih _ _ pair) fields.2.2⟩
      · intro row origin
        obtain ⟨other,found,fields⟩ := backward.row reader (fun right left => relation left right) related row origin
        exact ⟨other,found,fields.1,fields.2.1,All₂.imp (fun _ _ pair => (ih _ _ pair).symm) fields.2.2⟩

/-- Physical Empty agreement adds survival to the observations supplied by both simulations. -/
theorem related (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (forward : Forward reader relation)
    (backward : Forward reader (fun right left => relation left right))
    (first second : Value Symbol Guard) (paired : relation first second)
    (empty : first.referenceOf = .empty ↔ second.referenceOf = .empty) :
    SourceCurrentReaderObservations.Related reader first second :=
  ⟨empty,fun depth => same reader relation forward backward depth first second paired⟩

end MicroCFTA.SourceCurrentOpenWeakSimulation
