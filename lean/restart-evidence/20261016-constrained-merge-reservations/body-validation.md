# General ordinary Merge body resource validation

Date: 2026-10-16 20:23 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryMergeBudgetBody.lean`.
The source has 356 lines. Its SHA256 is `7b55de3942ee94e3c9130d8aa05af52bd22bdcdbc596048f1505e8a2049a4a8b`.
The evidence copy is byte-identical. The production source is frozen.

## Checks

- Final direct source check 2: terminal exit 0, no diagnostics.
- Parent canonical build: terminal exit 0, 1134 jobs. Parent confirmed the terminal result. `budget-body-build-1.log` retains the historical unused-input dependency warning. The new module has no diagnostics.
- Imported public checks: terminal exit 0. All 6 public declarations have an axiom probe and a full signature probe.
- Imported integration checks 1: terminal exit 0. All 4 kernels have an axiom probe and a full signature probe.
- Final imported logs contain no warnings, errors, or `sorryAx`. The axiom reports contain only standard `propext`, `Classical.choice`, and `Quot.sound` where used.

Direct draft 1 retains nil-case simplification errors, arithmetic normalization errors, equality-elimination errors, and a branch proof parse error. Final direct source check 2 fixes them. No production source changed after that check.

## General local certificate

The six public endpoints are `small_certified`, `column_certified`, `large_certified`, `group_certified`, `root_certified`, and `body_certified`.

The body endpoint takes only the initial semantic heap, stored cost heap, input availability, and original uniform profile. It derives a Budget between the same initial and returned heaps at `nodeBudget R A (height input)` and `edgeBudget R A (height input)`. It takes no successful body, returned count, output profile, or recursive-body certificate premise.

Every Budget contains an ordered ConstructorWorkTrace and two request bounds. The proof composes these traces at their literal intermediate heaps. It does not derive counts from final counter differences or transport a prefix Budget through heap growth without recording the later Work.

For child ceiling H, the lower recursive budgets use squared rows: `Nrec = nodeBudget (R * R) A H` and `Erec = edgeBudget (R * R) A H`. Original direct-child profiles widen from R to R squared. The exact child-relative resource contract then applies at height H.

Small rows charge their ordered child requests, then one raw edge request. Large rows charge each original column at `1 + Nrec` nodes and `Erec` edges, then one raw Top edge request. A retained singleton performs no constructor Work. Other retained columns run their literal ordinary union before requesting the exact union output at its returned heap. The original column count bounds the union profile before that recursive request.

Ordinary selection returns at the same complete heap at every comparison fuel. Its definition has no recursive comparison candidates for these inputs. Its contribution is zero constructor Work. This fact is specific to ordinary selection; unchanged heap counters alone are not used as a general zero-request rule.

The group proof bounds either source threshold branch by its original row count L: `L * (A * (1 + Nrec))` nodes and `L * (1 + A * Erec)` edges. The root map adds those variable group costs through actual intermediate heaps. Their sum uses the flattened original row count, bounded by R. The final node Work adds at most one node request. This gives exactly the declared recurrences:

- `N(R,A,0) = 0` and `N(R,A,H+1) = 1 + R * A * (1 + N(R*R,A,H))`.
- `E(R,A,0) = 0` and `E(R,A,H+1) = R + R * A * E(R*R,A,H)`.

Ordered map relations retain available closed values or resident closed-child edges through later effects. Constructor certificates use those actual records. All guards and equality classes remain unrestricted.

## Integration checks

1. Five source rows with two child positions take the column branch. At child height 1, the local branch derives the sharper Budget of 104 node requests and 51 edge requests. The rows retain arbitrary guards.
2. Ordinary selection at comparison fuel zero returns the literal distinct input list at the unchanged heap with a zero-request Budget.
3. The recurrence computes one-layer bounds and the complete two-layer bounds `N(5,2,2) = 521` and `E(5,2,2) = 255`.
4. The general producer interprets this body's certificate on the same actual five-row body Run. It derives both stored invariants, a real Work trace within the 521/255 request limits, and both final supply bounds. No intermediate profile, successful subcall, output count, or desired result law is supplied.

## Scope

This module is the complete local body resource certificate. The separate actual Run/Call producer discharges its universal recursive resource contract. This module alone does not assert recursive execution completion.

The counts concern node and edge constructor requests. A warm constructor hit still counts as a request; its actual reservation can be zero. Equality-field allocation in the allocated graph, comparison resources outside ordinary selection, instruction counts, host evaluation counts, lazy publication, and whole recursive caller budgets remain separate.

No older source, Haskell, Audit, root document, or earlier frozen evidence file was edited. This owner ran no Git or Lake command. New owned text has one final newline and no blank line at EOF. Derived compiled objects remain outside the evidence directory.
