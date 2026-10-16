# Independent projection reservation review

Reviewed: 2026-10-16 19:45 CEST.
Verdict: No material defect found in the checked component.

Occurrences counts literal source record positions. One ordinary node contributes one node occurrence; each edge contributes one edge occurrence and every nested child occurrence. Repeated rows and child values are added again. Mu/reference/union records contribute no ordinary count, but the projection accounting requires finite ordinary domain inputs and excludes those branches. The count is a static recursive function of the original records. It is not a heap-counter difference.

ConstructorWorkTrace.Trace.work records a literal Work job, its exact initial heap, the actual run heap, and observe(job,heap). The observer records typed request keys and each initial lookup miss. Trace.trans retains exact intermediate heaps and list concatenation order. next_exact derives counter increments from these primitive jobs and observed misses. next_le then uses misses at most requests. Neither theorem defines an action count by subtracting counters. The trace is an operational receipt for constructor jobs; it does not itself give a unique host instruction or forcing schedule.

ProjectionReservations constructs this receipt from the supplied actual Project/ProjectRows/Forest recursors. Union uses the exact edges shared by its ReadAll and makeNode equation. Ordinary read-domain inversion establishes literal direct read branches and unchanged heaps. Selected-row recursion uses the actual signed select equation and selected child's membership. Existing physical Projection effects derive availability and SemanticReady for that child's returned heap and grow the original suffix edge residency into it. The receipt then appends selected-child Work, remaining-row Work, and the actual final union Work in source order. It does not join jobs from another existential projection endpoint.

Every visited ordinary Project contributes at most one final node request. Its recursive selected child calls fit the full original row/child occurrence count. Missing positions skip those calls. Each source child occurrence is selected at most once per reached row; repeated source rows remain separate occurrences in the bound. The forest-root union has its separate one-request bound. Signed missing forest positions use Trace.refl. No raw makeEdge occurs in this finite ordinary projection graph, so edgeRequests is zero and the actual edge supply is unchanged.

No public endpoint assumes a future result profile, semantic answer, completed child callback, final readiness, final supply bound, or desired request list. The graph is a supplied actual completed operational graph; the theorem does not by itself construct projection completion. Initial physical facts only justify reached reads and current child availability. ConstructorWorkTrace remains a sequential Work model and does not count host races, losing concurrent candidates, equality-interner allocation, or unrelated effects.

Independent validation:
- Root canonical constructor-trace-projection-reservations-build-3.log: terminal exit 0, 1119 jobs, only the existing dependency warning.
- reservation-independent-public-1.log: all 21 public declaration axiom/full-signature pairs pass, including Trace and its constructors.
- reservation-independent-kernels-2.log: four integration pairs pass without warnings, errors, or sorryAx.
- Static duplicate-count kernel gives (5,2) for repeated rows and (10,4) for two repeated roots.
- Warm replay kernel proves one observed node request with zero node reservations at the unchanged whole heap. This distinguishes requests from counter changes.
- Same-forest kernel combines the profile, height, Work trace, request count, and supplies for one supplied actual result and heap.
- Serial-projection kernel derives the second semantic/availability/domain entry facts from the actual first return and preserves exact request concatenation and unchanged edge supply. Its second occurrence count is still the actual generated input's count; it is not advertised as an initial-only cumulative Target bound.

No production source or prior evidence was edited. No Lake, Haskell, Git, or board operation ran in this review. The first warning-only external kernel log remains diagnostic evidence.
