import MicroCFTA.SourceCurrentStoppingBuildRootedWriters
import MicroCFTA.SourceCurrentNativeMuOptionalSite

/-!
# Generated source writers at actual native optional-binder sites

Every stopping optional-binder call retains its generated source writer.
An actual yielded trace supplies the same generating instruction. The
captured compiler owner and terminal blocked instruction remain separate.
-/
namespace MicroCFTA.SourceCurrentNativeMuOptionalGeneration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedStoredSubstitution (leaves encode leaves_available)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- An arbitrary selected full Mu at an optional-binder stop is initial or has its same generated rooted writer. -/
theorem maybeMu [DecidableEq (EdgeKey Symbol Guard)]
    (pair : Nat × Nat) (parent : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (available : Available before parent)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (selected : (SourceRecursiveIntersectionMaybeMu.maybeMu pair parent before).state.nodeRecords key =
      some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
    Reference.intersection pair.1 pair.2 ∈ parent.free ∧
    Context before (leaves parent) ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu pair parent before =
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves parent) [.intersection pair.1 pair.2] parent)) (leaves parent) before ∧
    Written (.binder true (encode (leaves parent) [.intersection pair.1 pair.2] parent)) (leaves parent)
      before (SourceRecursiveIntersectionMaybeMu.maybeMu pair parent before).state key (.mu entry body depth ordinary) := by
  by_cases used : Reference.intersection pair.1 pair.2 ∈ parent.free
  · have context : Context before (leaves parent) :=
      ⟨SourceRecursiveIntersectionSemanticHeap.context before semantic (leaves parent)
        (leaves_available parent before available),semantic.2⟩
    have compiled : SourceRecursiveIntersectionMaybeMu.maybeMu pair parent before =
        InternedFreshOrdinaryConstruction.build
          (.binder true (encode (leaves parent) [.intersection pair.1 pair.2] parent)) (leaves parent) before := by
      rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq pair parent before before
        semantic.1.normal.facts available,ite_eq_left used]
    have atBuild : (InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves parent) [.intersection pair.1 pair.2] parent))
        (leaves parent) before).state.nodeRecords key = some (.mu entry body depth ordinary) := by
      rw [←compiled]
      exact selected
    rcases SourceCurrentStoppingBuildRootedWriters.build_writer_or_prior _ _ before context
        key entry body depth ordinary atBuild with prior | written
    · exact .inl prior
    · exact .inr ⟨used,context,compiled,by rw [compiled]; exact written⟩
  · exact .inl (by
      simpa only [SourceRecursiveIntersectionMaybeMu.unused pair parent before used,
        InternedNestedConstruction.Outcome.state] using selected)

open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {A : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The same recovered native instruction supplies the actual generated build and rooted selected writer. -/
theorem trace {fuel : Nat} {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after) (semantic : SemanticHeap before.native.machine.heap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (selected : after.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary) ∨
    ∃ prefixFuel suffixFuel pair parent next siteBefore siteAfter result heap,
      fuel = prefixFuel + 1 + suffixFuel ∧
      Trace prefixFuel control before (.code (.optionalBinder pair parent next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap parent ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair parent siteBefore.native.machine.heap = .done result heap ∧
      siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩ ∧
      step (.code (.optionalBinder pair parent next)) siteBefore = .yielded (.code (next result)) siteAfter ∧
      Trace suffixFuel (.code (next result)) siteAfter rest after ∧
      siteBefore.native.machine.heap.nodeRecords key = none ∧
      heap.nodeRecords key = some (.mu entry body depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows heap after.native.machine.heap ∧ Extends heap.nodes.issued after.native.machine.heap.nodes.issued ∧
      Reference.intersection pair.1 pair.2 ∈ parent.free ∧
      Context siteBefore.native.machine.heap (leaves parent) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves parent) [.intersection pair.1 pair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap = .done result heap ∧
      Written (.binder true (encode (leaves parent) [.intersection pair.1 pair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap heap key (.mu entry body depth ordinary) := by
  rcases SourceCurrentNativeMuOptionalSite.trace actual semantic key entry body depth ordinary selected with prior | site
  · exact .inl prior
  · obtain ⟨prefixFuel,suffixFuel,pair,parent,next,siteBefore,siteAfter,result,heap,fuelEq,earlierTrace,
      siteSemantic,siteAvailable,called,advanced,one,suffix,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued⟩ := site
    have atCall : (SourceRecursiveIntersectionMaybeMu.maybeMu pair parent siteBefore.native.machine.heap).state.nodeRecords key =
        some (.mu entry body depth ordinary) := by
      simpa only [called,InternedNestedConstruction.Outcome.state] using present
    rcases maybeMu pair parent siteBefore.native.machine.heap siteSemantic siteAvailable
        key entry body depth ordinary atCall with prior | generated
    · rw [missing] at prior
      cases prior
    · obtain ⟨used,context,compiled,written⟩ := generated
      have built := compiled.symm.trans called
      have writer : Written (.binder true (encode (leaves parent) [.intersection pair.1 pair.2] parent)) (leaves parent)
          siteBefore.native.machine.heap heap key (.mu entry body depth ordinary) := by
        simpa only [called,InternedNestedConstruction.Outcome.state] using written
      exact .inr ⟨prefixFuel,suffixFuel,pair,parent,next,siteBefore,siteAfter,result,heap,fuelEq,earlierTrace,
        siteSemantic,siteAvailable,called,advanced,one,suffix,missing,present,prefixGrowth,prefixIssued,
        suffixGrowth,suffixIssued,used,context,built,writer⟩

end MicroCFTA.SourceCurrentNativeMuOptionalGeneration

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentNativeMuOptionalGeneration.maybeMu
#print MicroCFTA.SourceCurrentNativeMuOptionalGeneration.maybeMu
#print axioms MicroCFTA.SourceCurrentNativeMuOptionalGeneration.maybeMu

#check @MicroCFTA.SourceCurrentNativeMuOptionalGeneration.trace
#print MicroCFTA.SourceCurrentNativeMuOptionalGeneration.trace
#print axioms MicroCFTA.SourceCurrentNativeMuOptionalGeneration.trace
