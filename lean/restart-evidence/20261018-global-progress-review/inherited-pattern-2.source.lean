import MicroCFTA.SourceEqualityInheritedGrowthBoundary
open MicroCFTA MicroCFTA.EqualityNormalize
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private def norm (input : Constraints) : Option Constraints :=
  match mkEqConstraints 32 input with
  | .normalized result => some result
  | _ => none
private def walk : Nat → Option Constraints
  | 0 => some []
  | n + 1 => do
    let inherited ← walk n
    let own ← norm SourceEqualityInheritedGrowthBoundary.raw
    let combined ← norm (inherited ++ own)
    pure (eqConstraintsDescend 1 combined)
#eval (List.range 6).map walk
