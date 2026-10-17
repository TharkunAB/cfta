import MicroCFTA.SourceCurrentConstrainedCapNativeCache

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.NativeCapCacheKernels
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentConstrainedCap (Cap)
variable {Symbol Guard : Type} {width : Nat}

/-- A real warm lookup applies the positive cap law even when the original row is not hereditary. -/
theorem warm_constrained_row
    (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (edge : EdgeValue Symbol Guard) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (level : Nat) (free : List InternedBinderProtocol.Reference)
    (children : edge.children = []) (outside : ¬ annotation edge.entry.key.constraint)
    (before chosen after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (handle : Nat) (result : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before)
    (stored : SourceCurrentConstrainedCapNativeCache.Stored annotation source before)
    (ready : NodeReady before.machine ⟨IntersectionEmptyDomain.emptyDomain,
      .node entry [edge] level free, .node entry [edge] level free⟩)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width IntersectionEmptyDomain.emptyDomain
      (.node entry [edge] level free) (.node entry [edge] level free))
    (selected : lookupNode width ⟨IntersectionEmptyDomain.emptyDomain, .node entry [edge] level free,
      .node entry [edge] level free⟩ before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready result, after)) :
    ¬ SourceEqualityAnnotationLanguage.Annotated annotation (.node entry [edge] level free) ∧
      Cap annotation 1 result ∧ SourceCurrentConstrainedCapNativeCache.Stored annotation source after ∧
      after = chosen ∧ Available after.machine.heap result := by
  have bounded : Cap annotation 1 (.node entry [edge] level free) := by
    apply Cap.node 0
    intro value member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, children, List.not_mem_nil] at member
  have notHereditary : ¬ SourceEqualityAnnotationLanguage.Annotated annotation (.node entry [edge] level free) := by
    intro annotated
    exact outside (SourceCurrentHereditaryConstructors.node_edge annotated edge List.mem_cons_self).1
  have observed := SourceCurrentConstrainedCapNativeCache.node_observed_ready annotation source
    ⟨IntersectionEmptyDomain.emptyDomain, .node entry [edge] level free, .node entry [edge] level free⟩
    before chosen after handle result physical stored ready safe selected demanded
  exact ⟨notHereditary, observed.1 1 (SourceCurrentHereditaryNativeScope.empty annotation source) bounded bounded,
    observed.2⟩

end MicroCFTA.NativeCapCacheKernels

#print axioms MicroCFTA.NativeCapCacheKernels.warm_constrained_row
#check @MicroCFTA.NativeCapCacheKernels.warm_constrained_row
