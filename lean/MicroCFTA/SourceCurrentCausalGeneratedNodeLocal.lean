import MicroCFTA.SourceCurrentCausalGeneratedEmpty
import MicroCFTA.SourceCurrentGeneratedNodeSchedules
import MicroCFTA.SourceCurrentSourceDirectedCases

/-!
# Causal local simulation for historical node calls

Actual source rows supply ordered generated child pairs at the reader.
Causal Empty agreement keeps the opposite reconstructed row alive. The
local clauses retain the full symbol and guard and mutual child pairs.
No child result law or source induction hypothesis is required.
-/
namespace MicroCFTA.SourceCurrentCausalGeneratedNodeLocal
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildEdges)
open InternedFreshOrdinaryFacts (buildEdges_verified)
open InternedFreshOrdinaryLiveInputs (input)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready Ordinary)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentUsedBinderAliasTransport (Aliases)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentSourceDirectedCases (Local)
open SourceCurrentOpenPreorderSimulation (Mutual)
open SourceCurrentOpenObservations (RowMatch)
open SourceCurrentStoredNodeExpansion (RowCalls)
open MergedFreshOrdinaryGraph (Origin)
variable {Atom : Type}

private theorem reverse_inputs [DecidableEq (EdgeKey Symbol Guard)] {reader : State Symbol Guard}
    {first second : Environment Symbol Guard} {left right : List (Value Symbol Guard)}
    (paired : Inputs reader first second left right) : Inputs reader second first right left := by
  refine Inputs.rec (motive_1 := fun _ _ _ => True)
    (motive_2 := fun first second left right _ => Inputs reader second first right left)
    (fun _ => True.intro) ?_ (fun first second => .nil second first) ?_ ?_ paired
  · intros
    trivial
  · intro first second a b left right forward backward tail _ _ ih
    exact .reference backward forward ih
  · intro first second left right value agree tail ih
    exact .fixed value (fun name member => (agree name member).symm) ih


private theorem node_parts [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (before after : State Symbol Guard) (value : Value Symbol Guard)
    (actual : build (.node expressions) inputs before = .done value after) :
    ∃ rows middle, buildEdges expressions inputs before = .done rows middle ∧
      run (makeNode rows) middle = (value,after) := by
  cases built : buildEdges expressions inputs before with
  | pending key state => simp only [build,built,Outcome.bind] at actual; cases actual
  | done rows middle =>
      have same := Outcome.done.inj (by simpa only [build,built,Outcome.bind,InternedNestedConstruction.work] using actual)
      exact ⟨rows,middle,rfl,Prod.ext same.1 same.2⟩

private theorem raw_ordinary [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (context : Context before inputs) (value : Value Symbol Guard)
    (actual : build (.node expressions) inputs before = .done value after) : Ordinary value := by
  obtain ⟨rows,middle,called,made⟩ := node_parts expressions inputs before after value actual
  have checked := buildEdges_verified expressions inputs before context.base.normal.facts context.base.inputs
  have facts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
  have ordinary := SourceEqualityRequiredCache.node_ordinary rows middle facts (checked.result rows middle called)
  simpa only [made] using ordinary

private theorem stored_ordinary [DecidableEq (EdgeKey Symbol Guard)] (raw result : Value Symbol Guard)
    (environment : Environment Symbol Guard) (reader : State Symbol Guard) (ready : Ready reader)
    (ordinary : Ordinary raw) (available : Available reader raw) (replacements : Replacements reader environment)
    (called : execute raw environment reader = .done result reader) : Ordinary result := by
  cases raw with
  | empty =>
      have same := (Outcome.done.inj ((SourceCurrentStoredUnionObservations.closed .empty environment reader rfl).symm.trans called)).1
      subst result
      trivial
  | node entry rows level free =>
      obtain ⟨_,_,plain,_⟩ := SourceCurrentStoredNodeExpansion.node_warm entry rows level free environment reader
        ready.semantic.1.normal available replacements result called
      exact plain
  | reference | union | mu => cases ordinary


private theorem literal_row (value : Value Symbol Guard) (row : EdgeValue Symbol Guard)
    (ordinary : Ordinary value) : SourceCurrentLiteralRootParts.Row value row ↔ row ∈ nodeEdges value := by
  cases value with
  | empty =>
      constructor
      · intro impossible; cases impossible
      · intro impossible; cases impossible
  | node => exact SourceCurrentLiteralRootParts.row_node _ _ _ _ _
  | reference | union | mu => cases ordinary

private theorem no_atom (value : Value Symbol Guard) (ordinary : Ordinary value) :
    ∀ atom, ¬ SourceCurrentLiteralRootParts.Literal value atom := by
  cases value with
  | empty | node => intro atom impossible; cases impossible
  | reference | union | mu => cases ordinary

private theorem row_unique [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard)
    (ready : Ready reader) (environment : Environment Symbol Guard) (raw first second : EdgeValue Symbol Guard)
    (left : RowCalls environment reader raw first) (right : RowCalls environment reader raw second) : first = second := by
  have same := SourceCurrentStoredCallsReplay.same left.1 right.1 reader
    ready.semantic.1.normal.facts.coherent.valid ready.semantic.1.normal.facts.coherent.valid (grows_refl _) (grows_refl _)
  have made := left.2.1
  rw [same] at made
  exact congrArg Prod.fst (made.symm.trans right.2.1)

private theorem any_empty {first second : List (Value Symbol Guard)}
    (paired : All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second) :
    first.any (fun value => value.referenceOf == .empty) = second.any (fun value => value.referenceOf == .empty) := by
  induction paired with
  | nil => rfl
  | cons head tail ih => simp only [List.any_cons,head,ih]

private theorem row [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader before after later final : State Symbol Guard)
    (ready : Ready reader) (history : History empty reader)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (aliases : Aliases (.node expressions) inputs firstNames secondNames)
    (paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (firstBuild : build (.node expressions) (inputs.map (input firstNames)) before = .done rawFirst after)
    (secondBuild : build (.node expressions) (inputs.map (input secondNames)) later = .done rawSecond final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (firstAvailable : Available reader rawFirst) (secondAvailable : Available reader rawSecond)
    (firstDone : execute rawFirst first reader = .done left reader)
    (secondDone : execute rawSecond second reader = .done right reader)
    (row : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges left) :
    ∃ other ∈ nodeEdges right, RowMatch (Mutual (Generated reader)) row other := by
  have firstPlain := raw_ordinary expressions _ before after firstContext rawFirst firstBuild
  have secondPlain := raw_ordinary expressions _ later final secondContext rawSecond secondBuild
  have leftPlain := stored_ordinary rawFirst left first reader ready firstPlain firstAvailable firstReplacements firstDone
  have rightPlain := stored_ordinary rawSecond right second reader ready secondPlain secondAvailable secondReplacements secondDone
  have firstParts := SourceCurrentStoredLiteralExecutionParts.parts rawFirst left first reader ready firstAvailable firstReplacements firstDone
  obtain ⟨raw,rawPart,actual,alive⟩ := ((firstParts.2 row).mp ((literal_row left row leftPlain).mpr selected)).resolve_left
    (by rintro ⟨atom,part,_,_,_⟩; exact no_atom rawFirst firstPlain atom part)
  have rawMember := (literal_row rawFirst raw firstPlain).mp rawPart
  obtain ⟨firstRows,firstAfter,secondRows,secondAfter,index,symbol,guard,children,firstRow,secondRow,
      _firstRowsDone,_firstMade,_secondRowsDone,_secondMade,same,secondMember,_firstWarm,_secondWarm,
      firstOutput,secondOutput,firstCalls,secondCalls,generated⟩ := SourceCurrentGeneratedNodeSchedules.node expressions inputs firstNames secondNames
    first second reader before after later final ready firstContext secondContext aliases paired firstReplacements
    secondReplacements rawFirst rawSecond left right firstBuild secondBuild firstGrowth secondGrowth
    firstAvailable secondAvailable firstDone secondDone raw rawMember
  have childrenEmpty := All₂.imp (fun _ _ pair => SourceCurrentCausalGeneratedEmpty.generated reader history pair.1) generated
  have equal := row_unique reader ready first raw row firstOutput actual firstCalls
  subst firstOutput
  have rightAlive : (!(secondOutput.children.any (fun value => value.referenceOf == .empty))) = true := by
    rw [←any_empty childrenEmpty]
    exact alive
  have secondParts := SourceCurrentStoredLiteralExecutionParts.parts rawSecond right second reader ready secondAvailable secondReplacements secondDone
  have survives := (secondParts.2 secondOutput).mpr (.inr ⟨secondRow.output,
    (literal_row rawSecond secondRow.output secondPlain).mpr secondMember,secondCalls,rightAlive⟩)
  refine ⟨secondOutput,(literal_row right secondOutput rightPlain).mp survives,?_,?_,generated⟩
  · exact actual.2.2.1.trans (same ▸ firstRow.symbol_eq) |>.trans (secondRow.symbol_eq.symm.trans secondCalls.2.2.1.symm)
  · exact actual.2.2.2.1.trans (same ▸ firstRow.guard_eq) |>.trans (secondRow.guard_eq.symm.trans secondCalls.2.2.2.1.symm)

private theorem terminal_local [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard)
    (first second : Value Symbol Guard) (plain : Ordinary first)
    (rows : ∀ row ∈ nodeEdges first, ∃ other ∈ nodeEdges second, RowMatch (Mutual (Generated reader)) row other) :
    Local reader (Generated reader) first second := by
  refine ⟨?_,?_,?_⟩
  · intro name same
    subst first
    cases plain
  · intro row member
    obtain ⟨other,present,fields⟩ := rows row member
    exact ⟨other,⟨second,.seed List.mem_cons_self,present⟩,fields⟩
  · intro next member
    cases first <;> try cases plain <;> cases member

/-- Historical node calls derive both local simulation clauses with full rows and ordered mutual children. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader before after later final : State Symbol Guard)
    (ready : Ready reader) (history : History empty reader)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (aliases : Aliases (.node expressions) inputs firstNames secondNames)
    (paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (firstBuild : build (.node expressions) (inputs.map (input firstNames)) before = .done rawFirst after)
    (secondBuild : build (.node expressions) (inputs.map (input secondNames)) later = .done rawSecond final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (firstAvailable : Available reader rawFirst) (secondAvailable : Available reader rawSecond)
    (firstDone : execute rawFirst first reader = .done left reader)
    (secondDone : execute rawSecond second reader = .done right reader) :
    Local reader (Generated reader) left right ∧ Local reader (Generated reader) right left := by
  have firstPlain := raw_ordinary expressions _ before after firstContext rawFirst firstBuild
  have secondPlain := raw_ordinary expressions _ later final secondContext rawSecond secondBuild
  have leftPlain := stored_ordinary rawFirst left first reader ready firstPlain firstAvailable firstReplacements firstDone
  have rightPlain := stored_ordinary rawSecond right second reader ready secondPlain secondAvailable secondReplacements secondDone
  exact ⟨terminal_local reader left right leftPlain
      (row expressions inputs firstNames secondNames first second reader before after later final ready history
        firstContext secondContext aliases paired firstReplacements secondReplacements rawFirst rawSecond left right
        firstBuild secondBuild firstGrowth secondGrowth firstAvailable secondAvailable firstDone secondDone),
    terminal_local reader right left rightPlain
      (row expressions inputs secondNames firstNames second first reader later final before after ready history
        secondContext firstContext (fun a ha b hb => (aliases a ha b hb).symm) (reverse_inputs paired)
        secondReplacements firstReplacements rawSecond rawFirst right left secondBuild firstBuild secondGrowth firstGrowth
        secondAvailable firstAvailable secondDone firstDone)⟩

end MicroCFTA.SourceCurrentCausalGeneratedNodeLocal
