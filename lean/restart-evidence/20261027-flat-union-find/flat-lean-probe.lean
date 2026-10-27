import MicroCFTA.FlatUnionFindSemantics
open MicroCFTA.FlatUnionFind
private def states : List Forest :=
  [(0, 1), (2, 3), (2, 0), (8, 9), (8, 2), (10, 2), (10, 10)].scanl
    (fun forest request => union forest request.1 request.2) (withInitialValues [0, 1, 1, 2, 3])
#eval states.map fun forest => (List.range 11).map (root forest)
#eval (entryOf (states.getLast!) 2)
#eval (states.getLast! 1)
#eval (states.getLast! 9)
