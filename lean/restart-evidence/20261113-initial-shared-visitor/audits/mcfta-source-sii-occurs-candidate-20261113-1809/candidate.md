# S I I candidate: source equations, not an execution claim

Status: bounded read-only candidate audit. No probe or Lean proof was run.
Library s:(a→b→c)→(a→b)→a→c and i:d→d; goal Int→Int; size3;
query arguments=[], avoid rules=[]. The two uses of i have fresh d and e.

1. The expected finite-type obstruction is precise.
   First application requires d→d = a→(b→c): d=a and d=b→c, hence a=b→c.
   Second application requires e→e = a→b: e=a=b, hence a=b.
   Together these require a=a→c, which has no finite simple-Type solution.
   The concrete goal additionally fixes a=Int and c=Int. If all these equations
   are actually propagated, the contradiction also has the anchored form
   Int = Int→Int. Therefore the candidate does not force the implementation's
   rejection to use a nonliteral cycle test rather than ordinary mismatch.
   A native result could still encode that contradiction nonliterally; the
   algebra alone does NOT prove its actual representation or rejection path.

2. Source syntax does not reject the spelling by an explicit occurs test.
   FirstOrderConstruction.application:47-49 supplies the fixed THREE app classes;
   GeneralizeSyntax.occurrences/equalityClasses/generalize:56/83/109 supplies
   repeated scheme-variable equalities. With no avoids, termsRows:84-103 retains
   the ordinary size2 fallback and size3 positive splits. CurrentContext uses
   these existing evaluators. Front-end totality supplies .ok at size3, but that
   alone does not certify this particular expression/Program in its language.
   No actual candidate-membership or traversal receipt was constructed here.

3. Existing logic distinguishes semantic impossibility from actual rejection.
   SymbolicNormalization.occurs_constructor_reject:454 rules out a finite
   assignment satisfying the constructor occurrence, in its symbolic engine.
   RootTyping.firstOrderRaw_typed:29 would return finite ordinary typing from
   an accepted finite source term. Neither theorem observes a native eager
   rejection of this source choice or constructs a model for a surviving hole.
   IncomingNode.finish:30-35 rejects a literal-empty replacement regardless of
   checkEmpty; a terminal merge that actually produces such a result is covered.
   The remaining obligation is to trace the SAME actual class sharing, terminal
   intersections, opacity and query goal. A frontend expression, type algebra,
   or unrelated symbolic count cannot supply that receipt.

Conclusion: this is a valid finite-Type inconsistency candidate, not an emitted
counterexample, a source-reachability proof, or grounds for changing mode scope.
The Bool/Int literal-empty exclusion and the frozen90/14 joint-witness audit
remain unchanged. No broader runtime search or old erase/f-f probe was repeated.
