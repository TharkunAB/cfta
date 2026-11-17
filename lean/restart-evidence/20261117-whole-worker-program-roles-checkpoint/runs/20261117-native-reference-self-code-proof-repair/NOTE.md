# Reference self compiler repair

Status: FROZEN UNCOMPILED. This packet replaces only reference_self_code.
The exact private header457849ef remains unchanged. Root owns all compilation.

The cf68 helper is at1266–1275. The log's first873/875/876 diagnostics concern
body_mu_enter_admission. Those sites remain outside this packet's scope.
The helper's own diagnostics are no-progress simp_all calls at1275.

The original broad split enters the outer compiler Branch match. It can create
many irrelevant alternatives. The replacement first computes the actual
reference/ref decision, then splits only membership in domain.key.seen.
Empty and reset are false. The open reference does not take closedSelf.
The checked reference_interned comparison law proves that no swap is needed.
The seen case returns pure repeatedValue. The unseen case retains the literal
compileReference binding read. No free-name or alias shortcut is assumed.

The complete original context is recorded in CONTEXT.lean.txt. Replace only
the helper region with REFERENCE-SELF.lean.txt in the main owner's NEW repair.
No new import is needed. The existing source already imports the Schedule API.
The source, log, Control, Compile, Schedule, and public reference-control proof
are pinned. No complete module clone or independent native proof is proposed.

No premise, source operand, domain, fuel, runtime, linter, checking cap, or other
helper changes. No Source edit, compiler, Git, board, or temporary-directory
action was performed. This packet does not discharge full363 or original441e.
