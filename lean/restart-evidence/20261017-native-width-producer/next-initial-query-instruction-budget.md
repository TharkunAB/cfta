# Next proof: an initial checked-query instruction budget

Continue the full-library goal. Read NEXT-PROMPT.md, HANDOFF.md, and root
FINDINGS.md first. Read lean/notes-current-native-width-producer.md for the
top-level target and current boundaries. Preserve all proofs, counterexamples,
repairs, and marked drafts. Keep the optimized interned core and older
constructor and equality work. Refresh upstream without losing these files.
Publication remains restricted to formalize under the active goal.

## Completed producer

The five modules in this checkpoint derive quantitative code safety from
initial ready operands and initial physical stores. They cover every node
compiler branch, both checked edge branches, ordered walks, direct requests,
warm hits, miss publication, and protected finish frames. On the same actual
physical trace, they derive every reached width check, store bound, and
constructor allocation bound. Do not repeat these proofs.

The actual physical trace and its length remain inputs. This checkpoint
does not construct complete generated queries from initial resources.

## First target

Read initial-query-step-bound-survey.md in this directory. It identifies the
exact source APIs. Derive a checked instruction budget from initial semantic
rank and initial source branching. Do not select the budget from a completed
Receipt or assume the later instruction count.

Within one query, recursive operands remain in the fixed original source.
Returned values feed constructor continuations. They do not change the
original row, member, or child schedules. Let R, M, and A be the initial
SourceProfile row, member, and arity limits. A proposed conservative bound is:

```
L = max 1 (max (R * R) (max M A))
T 0 = 0
T (h + 1) = 4 + L * T h
```

This recurrence is proposed, not proved. Count yielded checked instructions.
The final execute instruction that observes done costs one more. A Work or
optionalBinder instruction counts once. Its internal constructor execution
and solver work need separate bounds.

IntersectSchedule.requiredFuel gives the least successful semantic rank.
It is not an instruction count. Initial semantic completeness already follows
from original source Facts and closed operands. Each recursive request has
strictly smaller requiredFuel. Preserve original NodeScope and EdgeScope
through current reads and entered Mu domains. Use the actual checked edge
child and body bounds, rather than the eager edge compiler.

Add an instruction-credit certificate for actual code and control. Prove
bind and ordered-walk addition. Charge each recursive request by its smaller
rank. Retain the captured owner and exact continuation of both native finish
frames. Each actual yielded step must consume at least one credit. Below
alone cannot bound code length because reads and Work need no child request.

Use the existing complete physical request theorem and bound that same
constructed trace. Do not copy completion only to add a length field. Good
alone admits a matching evaluating cell. Keep Idle or the appropriate
ActiveAbove condition for complete-query admission.

## Composition and validation

Derive WordRanges from the existing initial source counters and finite
domain-inventory headroom. Avoid an assumed all-prefix capacity condition.
Prove monotonicity in the instruction count for massAfter and credit. Then
combine the same bounded trace with NativeWidthTrace to obtain initial-only
store and constructor-supply bounds. Retain current operation fields and
physical finish ownership.

Verify the full semantic request family. Include Mu, references, unions,
ordinary row joins, checked accepted and rejected edges, direct returns,
warm tables, and finish frames. Use strict empty-log checks, complete imported
signatures and axiom checks, and constructive integration proofs. Preserve
failed attempts. Update all restart authorities and frozen evidence.

A computed syntax-only bound on semantic rank is a further obligation.
Result-fed serial queries with newly generated operands, general Target and
Force misses, editor/class completion, arbitrary constrained Mu bodies,
outer descent producers, convergence, current adapters, concrete capacity,
and complete public Haskell correspondence remain open.

## Haskell handoff

Root FINDINGS keeps current repair status first. The recursive field-pool
report is repaired by b9219b9e in source main c0cc8a05. No new Haskell defect
or source change occurs here. Reuse unchanged source validation. Record each
later repair with its failure, reproducer, affected paths, commit, checks,
and upstream status so external work can use it.
