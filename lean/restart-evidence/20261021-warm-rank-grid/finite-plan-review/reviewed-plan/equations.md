Concrete proposed equations. These equations are not a proof implementation.

For seed s, let M = s.profile.mass.
G(s) = (range (M+1)).flatMap (fun count => (range (M+1)).map (fun mass => (count,mass))).
For q = (count,mass), O(b,q,s) = C b count mass s.
T(b,q,s) = SourceCurrentOuterInitialSchedule.node O(b,q,s).W b s.
J(b,q,s) = (O(b,q,s).output.alphabet ++ T(b,q,s).alphabet,
  cover [O(b,q,s).output.profile] T(b,q,s).profile).

stage b initial 0 = initial.
For current = stage b initial i and cases = (G(current)).map (fun q => J(b,q,current)),
stage b initial (i+1) = (current.alphabet ++ cases.flatMap (fun one => one.alphabet),
  cover (cases.map (fun one => one.profile)) current.profile).
The list of ranks and every case in this step use the same current seed.

For each i in range N, put current = stage b initial i.
Map every q in G(current) to (O(b,q,current).W,
  SourceCurrentOuterInitialFuel.nodeNeed O(b,q,current).W b current).
Let allBounds be the flatMap of these lists over range N.
fuelBounds b N initial = (maximum (allBounds.map Prod.fst), maximum (allBounds.map Prod.snd)).
At N = 0 both maxima are zero. The case-bound part of stage_bounds is then vacuous.

These definitions enumerate finite lists. They do not inspect a caller or execute the worker.
A later module can use private grid/case definitions in bodies, with no private names in public types.
