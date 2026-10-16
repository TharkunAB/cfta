# Independent actual-prefix budget review

Reviewed 2026-10-16 18:59 CEST. Source `SourceCurrentAllocatedFiniteOrdinaryNativeBudgetExecution.lean`, SHA256 `c684e8259fa296f376325ae3f93de5018515e2d42dcad40c569de12030d05bd0`. No material defect was found in the reviewed bytes.

The interpreter theorem keeps its component assumptions explicit (`:57`): a scheme's admitted node requests have a compiled code budget, and actual checked edge-body yields preserve the edge budget. These are local code-potential laws. They are not successful query receipts or desired returned-state invariants. The concrete compiler module must instantiate both laws. The initial Origins, word certificate, and ControlBound remain separate inputs.

The Work branch consumes the actual combined node and edge request count at the current literal heap. It applies the uniform Work bound there and retains only the continuation budget. The quantity counted is requests, not just misses. This is a safe upper bound for reservations. Equality-operation allocations do not affect the two constructor supplies and are outside this resource measure.

Memo hits skip the producer budget and retain the uniform continuation bound. Starts use `Origins.node_started` or `edge_started` before compiling or entering the captured owner. Thus the proof does not charge one candidate while executing an unrelated stored request. Direct node requests compile that exact request. Absent and busy observations cannot satisfy a yielded-step premise. Finish instructions retain the current budget and change no constructor supply.

The checked edge-body case has no constructor Work at the dispatch step. Its local body certificate accounts for the yielded sentinel or accepted child code. The one-step bound then composes over arbitrary finite actual Steps. The prefix theorem retains a nonnegative remaining budget and adds actual request counts in source order. It uses the old word-preservation theorem only to transport Origins and the word certificate. It does not substitute an older execution.

`prefix_supplies` combines this potential decrease with exact existing reservation accounting. Each supply is at most its initial value plus the initial combined budget. No final counter difference, supplied actual-request-list bound, completed query, body success callback, or final semantic heap is used. The theorem applies to finite yielded prefixes and does not itself establish termination or a whole caller budget. Unsupported enter/read/optionalBinder remain excluded by ControlBound.

Canonical `budget-execution-build-1.log` passed1107 jobs with only the historical unused `inputs` dependency warning. This task reviewed source and evidence only. It did not edit the root module or run another build. General recursive input structures, whole reduction resource envelopes, other identity families, and GHC demand and publication remain separate.
