import MicroCFTA.SourceCurrentConjunctionGuardUniverse
namespace Probe
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsAllocation (Ready Effects Tuple Tuples Rows)
section Rows
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
variable [DecidableEq (EdgeKey Symbol Guard)]
#synth DecidableEq (EdgeKey Symbol Guard)
#check fun {edges : List (EdgeValue Symbol Guard)} {before after : Physical} {values : Option (List (List (Value Symbol Guard)))} (actual : Tuple edges before values after) => actual
end Rows
end Probe
