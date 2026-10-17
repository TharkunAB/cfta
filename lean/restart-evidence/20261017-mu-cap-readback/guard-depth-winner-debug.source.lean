import MicroCFTA.SourceCurrentConstrainedCapGuardDepth
open MicroCFTA MicroCFTA.InternedConstructorTemplates MicroCFTA.InternedNestedConstruction
#reduce match InternedFreshOrdinaryConstruction.build (.binder false (.union [.var 0, .node [.mk 0 false []]]): Syntax Nat Bool) [] empty with
 | .done value _ => value
 | .pending .. => .empty
