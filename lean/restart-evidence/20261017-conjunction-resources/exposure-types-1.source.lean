import MicroCFTA.SourceCurrentProjectionUnionResources
import MicroCFTA.SourceCurrentConjunctionRowsWorker
namespace MicroCFTA.SourceCurrentConjunctionExposureResources
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
variable [DecidableEq (EdgeKey Symbol Guard)]
set_option pp.explicit true
set_option pp.fullNames true
#check @SourceCurrentConjunctionCompletionReads.Exposures
example {nodes : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {rows : List (List (EdgeValue Symbol Guard))}
    (actual : SourceCurrentConjunctionCompletionReads.Exposures nodes before rows after) : True := by trivial
end MicroCFTA.SourceCurrentConjunctionExposureResources
