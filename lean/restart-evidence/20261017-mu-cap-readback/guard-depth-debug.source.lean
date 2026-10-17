import MicroCFTA.SourceCurrentConstrainedCapGuardDepth
open MicroCFTA MicroCFTA.InternedConstructorTemplates MicroCFTA.InternedNestedConstruction
#reduce match InternedFreshOrdinaryConstruction.build (.node [.mk 0 true [.node [.mk 1 false []]]] : Syntax Nat Bool) [] empty with
 | .done value _ => value
 | .pending .. => .empty
