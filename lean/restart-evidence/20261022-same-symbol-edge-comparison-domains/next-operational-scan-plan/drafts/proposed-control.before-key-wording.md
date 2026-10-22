# Proposed source-level control

These are exact proposed shapes and transition equations, not Lean declarations or implemented bodies.
Working namespace: MicroCFTA.SourceCurrentOriginalRowClusterScan.
State is SourceCurrentSameSymbolEdgeControl.State width without a wrapper record.
Edge is the existing physical EdgeValue at the same Symbol and Guard types.

| Control phase | Stored fields |
| --- | --- |
| cluster | candidates : List Edge; keptReversed : List Edge |
| scan | pivot : Edge; remaining : List Edge; incomparableReversed : List Edge; keptReversed : List Edge |
| comparison | pivot candidate : Edge; tail : List Edge; incomparableReversed : List Edge; keptReversed : List Edge; inner : H7.Control |

| Input to step | Exact output |
| --- | --- |
| cluster([], kept), state | done(reverse kept, state) |
| cluster(pivot::tail, kept), state | yielded(scan(pivot, tail, [], kept), state) |
| scan(pivot, [], inc, kept), state | yielded(cluster(reverse inc, pivot::kept), state) |
| scan(pivot, candidate::tail, inc, kept), state | yielded(comparison(pivot, candidate, tail, inc, kept, H7.call(pivot,candidate,[])), state) |
| comparison(frame, inner), state; H7.step(inner,state)=yielded(next,after) | yielded(comparison(frame,next), after) |
| comparison(frame, inner), state; H7.step(inner,state)=done(common,after); common.id=candidate.id | yielded(scan(pivot,tail,inc,kept), after) |
| Same, first test false and common.id=pivot.id | yielded(cluster(candidate::(reverse inc ++ tail),kept), after) |
| Same, both tests false | yielded(scan(pivot,tail,candidate::inc,kept), after) |
| comparison(frame,inner), state; H7.step returns failed(reason,after) | failed(reason,after) |
| comparison(frame,inner), state; H7.step returns constraintError(message,after) | constraintError(message,after) |
| comparison(frame,inner), state; H7.step returns blocked(reason,next,after) | blocked(reason,comparison(frame,next),after) |

Outcome width has yielded(Control,State), done(List Edge,State), failed(Kernel.Failure,State), constraintError(String,State) and blocked(H7.Blocked,Control,State).
execute 0 returns yielded(control,state). execute(fuel+1) uses step and recurses only on yielded; every terminal tag and state is returned unchanged.
On yield or blockage, frame includes all pending reconstruction and the original requested pair. On failure/error, the H7 API exposes no next inner control; the scanner must not invent one.
The identity tests use entry.identity equality, not structural EdgeValue equality. The initial ordered cache key, native pending handles and native residual belong to H7 and are not reimplemented.
