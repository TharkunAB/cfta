import MicroCFTA.SourceCurrentPublicationBodySourceRows
import MicroCFTA.SourceCurrentRootedRowChildOrigins

/-!
# Actual selected binder-child resumption

A completed source build retains the exact initial cell or derives one
selected historical publication. The same event supplies its raw source
row and the rooted child call or explicit capture or binder stop.
-/
namespace MicroCFTA.SourceCurrentSelectedBinderChildResume
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (NodeKey)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentRootedRowChildOrigins (Origin from_source_row)

/-- One actual completed call derives the selected body's rooted child origin or its exact initial cell. -/
theorem selected_body_child_or_prior [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before initial)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : build root initial before = .done result after)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (selected : after.nodeRecords key = some (.mu entry body depth ordinary))
    (parentRow : EdgeValue Symbol Guard) (inside : RowAt body parentRow)
    (childIndex : Nat) (child : Value Symbol Guard)
    (childSelected : parentRow.children[childIndex]? = some child) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
        Reached root initial (.binder event.smart event.expression) event.environment event.before ∧
        key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
        event.afterBody.nodeRecords event.key = none ∧
        Nonempty (Path before event.before) ∧
        Nonempty (Path event.before event.afterDepth) ∧
        Nonempty (Path event.afterDepth event.cut) ∧
        Nonempty (Path event.allocated event.afterBody) ∧
        Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued ∧
        ∃ raw rawAfter,
          build event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated = .done raw rawAfter ∧
          run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
          Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
          Reached root initial event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated ∧
          RowAt raw parentRow ∧
          SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated raw rawAfter parentRow ∧
          Origin root initial event.expression parentRow childIndex child := by
  rcases SourceCurrentCompletedBuildRootedWriters.build_writer_or_prior root initial before context
      result after actual key entry body depth ordinary selected with old | written
  · exact .inl old
  · obtain ⟨event,eventReached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
      earlier,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,built,filtered,
      allocatedContext,callbackReached,rawRow,source⟩ :=
        SourceCurrentPublicationBodySourceRows.written_body_origin written parentRow inside
    exact .inr ⟨event,eventReached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
      earlier,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,built,filtered,
      allocatedContext,callbackReached,rawRow,source,
      from_source_row allocatedContext callbackReached source childIndex child childSelected⟩

end MicroCFTA.SourceCurrentSelectedBinderChildResume
