# Actual stored literal-call cuts

Reviewed and frozen at 2026-10-18 09:17 CEST.

Production: `lean/MicroCFTA/SourceCurrentStoredLiteralCalls.lean`.
SHA-256: `b5f049a31c89dee1fb1f4d2fa9c37523eddc3bc022c9ff0f7cc7407083a03ba8`.

The module exports three producer theorems: `execute`, `indexed`, and `union_row`. It uses the repaired stored executor. All results retain the original replacement environment. The source values and their children may contain arbitrary nested Mu records.

`execute` starts with SemanticHeap before, source availability, replacement availability, and one literal successful stored execution equation. It derives SemanticHeap after, four-table Grows, issued-reference Extends, result availability, and replacement availability at after. SemanticHeap source preservation and repaired build_verified supply these facts. The theorem does not need Covered or a supplied final semantic law. It does not establish completion without the actual successful equation.

The private ordered-calls induction derives these same semantic and physical effects for each completed source list. It transports the original suffix and replacement values through the exact earlier calls. It also derives availability of every returned value at the final list state.

`indexed` consumes the existing actual Calls graph, initial SemanticHeap, available originals, available replacements, and one indexed output. Calls.indexed supplies the same original source index and the literal prefix, source execution, and suffix. The private ordered-calls induction derives the current semantic entry from that actual prefix. Physical growth transports the selected original source to that entry. Actual execution then supplies the next semantic state, output availability, and replacement availability. Actual suffix effects give next-to-final Grows and issued Extends. The receipt retains before-to-current and current-to-next growth and issued transport too. No future per-child output relation, semantic context, or desired row law is supplied.

`union_row` applies to an available open stored union and one literal RootParts.Row of its actual returned result. Existing StoredSubstitutionOrigins.union derives the actual ordered member calls and final makeUnion pair. Its epsilon-Origin consequence is not used. The proof derives the middle SemanticHeap and available outputs from the actual Calls schedule. LiteralUnionParts.row then identifies an actual member output with the exact same complete literal row. The indexed producer supplies the corresponding original source occurrence and exact call states. The receipt retains the full Calls schedule, makeUnion pair, original and output indices, literal row, prefix and suffix, derived current/next semantic facts, and growth through the actual union return.

Literal Row traverses root unions only. It does not unfold a Mu atom. Its complete EdgeValue preserves symbol, full guard, and ordered children. The theorem does not identify a changed child with its original value. It does not prove retained-used Mu callback correspondence. It assumes no initial publication History and produces no unrelated final History. The caller can compose the exact captured cuts with its separately derived final-reader History.

The union theorem has an explicit open-root condition. Closed stored unions use the executor's literal closed-capture shortcut and remain a separate source-induction case. There is no BinderFree, NoDeep, finite Cap, whole-forest closure, semantic Ready, or Covered restriction.

Selected receipts:

- `literal-calls-direct-1`: exit 0; actual raw log has 0 bytes; immutable executed source matches production.
- `literal-calls-canonical-1`: exit 0; warning-free successful canonical build with 559 jobs.
- `literal-calls-public-1`: exit 0; all three public declarations have full #check @, #print, and #print axioms output. All eight required options are explicit. The hardened checker found no omitted terms, printer failures, warnings, errors, or sorryAx. Axioms are limited to propext, Classical.choice, and Quot.sound.

Each run uses pinned Lean 4.34.1 and a five-minute heavy-management wrapper. Effective inner memory.max and memory.high are 4294967296, and memory.swap.max is 0. Direct and public commands execute numbered immutable sources with -Dlinter.all=true and the compiled LEAN_PATH.

There are no failed attempts in this component. Counts are three public pairs and zero constructed pairs. Root owns the recursive original-source lineage integration. The explicit manifest allowlist pins only owned evidence and frozen source dependencies. It excludes root working fixtures and shared mutable files.
