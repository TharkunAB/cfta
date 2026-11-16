# Pending evaluator congruence

Status: HEADER FROZEN. No compiler was run.

The existing EnumerationPendingAssignment module has finite evaluation and fuel stabilization. EnumerationAssignment has fill_holes_congr. EnumerationPendingAgreement transfers actual stored pending buckets when assignments already agree on pending roots. No existing evaluateSlotsWith congruence across changed base functions was found. This theorem reuses the original evaluator and fill_holes_congr.

kept is an ordinary predicate on raw slot indices. dependencies states that every hole of the actual expanded fragment looked up at roots uv stays in kept when uv is kept. agree states that the two supplied bases agree at every kept raw slot. The conclusion uses the same supplied evaluator fuel on both sides, including zero. No datatype, runtime evaluator, semantic model, future output, termination or cache law is introduced.

The evaluator returns base uv at zero fuel and at an unresolved lookup. It does not return base (roots uv). Therefore base agreement is on raw uv. Root closure of kept is not needed for this evaluator's control. Stored-fragment dependency closure is needed. For example, a slot0 that stores hole1 can evaluate differently after one step when bases differ at1, even if they agree at0. This is only a generic dependency example, not an actual-source defect or counterexample.

The generic dependency/base-agreement conditions must remain auxiliary facts. Root and Footprint own the authentic source producer work that derives an applicable set and base agreement from actual state/history receipts. This theorem does not discharge those producers or permit a future closure/model provider at the original global goal.

The theorem preserves every finite evaluator budget. It is equality across two bases at the same budget, not fuel stability, satisfaction, compatible-model existence, complete output agreement or full system correctness. Full906 and the original one-compatible-finite-completion target remain unchanged.
