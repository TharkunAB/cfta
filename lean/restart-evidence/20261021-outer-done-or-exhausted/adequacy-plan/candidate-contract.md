# Concrete controlled-envelope obligations

No public Lean header is proposed. The candidate below is a mathematical design, not a proved specification or an implementation authorization.

Let Seed = List Guard × Profile. Let r=(n,m), with the strict lexicographic Nat relation used by ActualChildRank.
The proposed C takes budget, r, and a Seed. It returns work and an output Seed. If controlled-to-root fuel domination is not proved, also accumulate L: the maximum of every predicted Parent lower-fuel bound in the finite recipe. A nested natural product suffices; no new resource type is needed. It takes no actual state, run, trace, call graph, supplied growth function, or future capacity function.
At the initial node request use r=(PositiveQuotientCount.count (request.inherited.payload.getD []) request.value, InternedValueMass.value request.value).
For a current seed s, define the finite child-rank image as all (a,b) with a≤n, b≤s.profile.mass, and (a<n OR (a=n AND b<m)).
For each image member, the recursive C call uses THAT rank and the SAME current s. All such rank calls are strictly smaller. C must be defined as a rank recursion with Seed as a further argument.
Join all predicted output profiles and the entry profile using the existing cover; join all predicted guard lists and the entry alphabet by finite concatenation/union. Take a maximum of the predicted child work.
A child-slot iteration updates s to this joined seed. Recompute its finite rank image at the next slot. Do not substitute the literal original prepared heap or reuse the first slot's profile after earlier siblings.
One row first uses Schedule.parent budget s. Freeze the returned child-list upper bound B from that Parent forecast's mass, apply the child-slot transformer B times, and use Schedule.rebuild for the final edge.
An ordinary owner has at most its mass many literal original rows. Iterate this row transformer with evolving seed, then use Schedule.rebuild for the final node. Empty/union/Mu branches and warm hits require no recursive ordinary child expansion.
The work component must include local body, row and walk decrements as well as each selected recursive child's work. A maximum of child depth alone is insufficient. Use an explicit sum or another proved bound on the literal nested decrements.

Required arithmetic results are finite image coverage, componentwise and alphabet inclusion of each join, seed retention, finite iteration composition, and the worker-fuel inequalities. No desired output-support or completion callback can replace these results.
Required physical connection is SAME-cut entry Fits/known guards and actual strict child rank; the existing local Parent result supplies the next bounded state. Warm cache hits use their genuine available returned payload and perform no new recursive body.
An implementation must settle whether concrete C seed monotonicity is needed. A slotwise finite join can avoid assuming it; this still needs a proof that the selected child's actual poststate fits the joined output seed.
C remains undefined; no F is constructed in this report. After an actual definition and proof, compute F from the initial rank and seed. Root Room at Schedule.node F enables the existing Prefix/rank APIs, but local Parent.complete at a controlled seed needs its OWN UniformReserved.
Settle this by proving every controlled Parent forecast is dominated by the root Schedule.node F profile, or by computing an initial finite profile join of root Schedule.node F and C.output and proving C.output retains every controlled Parent forecast. Then one initial Room test can imply both families of reservations.
That retention proof is a required new numeric bridge, not an inference from actual completion or growth. Root phaseNeed(F) alone does not establish the lower-fuel bound for a larger controlled Parent seed. Prove domination, or require all nine fuels to exceed max(phaseNeed(F),L), with L accumulated from initial data in C. The genuine initial semantic/closure/store/idle packet remains explicit. No check asserts that F succeeds.
C and the initial capacity checks do not prove that an arbitrary fixed-width state has enough room. Choosing or transferring width is a separate construction problem.

This design still needs an actual definition and soundness proof. A function type returning Nat × Seed alone would be vacuous, so this report does not publish one as an adequacy theorem.
