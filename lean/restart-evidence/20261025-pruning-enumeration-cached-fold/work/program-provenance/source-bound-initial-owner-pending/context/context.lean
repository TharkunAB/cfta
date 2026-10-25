import MicroCFTA.SourcePruningEnumerationCachedAdapter
import MicroCFTA.SourcePruningEnumerationFoldInvariants

namespace MicroCFTA.SourcePruningEnumerationCachedFold
open EnumerationState
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}
