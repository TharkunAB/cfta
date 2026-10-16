# Checked edge structural certificate validation

Timestamp: 2026-10-16 16:21 CEST.

The new source is `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryEdge.lean`.
Its SHA-256 is `abf6ddc23b9979e541d0dea54e4a682618dda69de9a7ec7f220b4c145990582b`.
The source has 241 lines. Its frozen copy has the same bytes.

## Established local results

`children_certified request inputs combined machine valid semantic` certifies the literal current `checkedCode.children`. `EdgeInputs` gives an empty incoming seen list and both finite ordinary child forests. Each literal zipped child request has these same structural inputs. Its continuation receives the conditional `NodeCertificate` for that exact request, plus the actual available output in its current machine. The private source-order walk retains both the ordered `All₂` structural bounds and availability through all later extensions.

The final raw constructor uses its actual complete child records. Coherent readback derives the finite ordinary result domain. Each child's bounds imply an edge height no greater than either original edge height. This result requires neither equal arity nor a law for the combined field. Raw child code uses the literal zip, including its truncation behavior. Actual accepted body admission still occurs only after the source arity and constraint checks.

`sentinel_certified request machine valid semantic` certifies the literal singleton-Empty sentinel. It needs no original child domain, field load, or child completion law. Its result has domain children and edge height zero. It returns the same conditional `EdgeCertificate` type as the accepted code.

`body_yielded_code request next before after rest yielded` derives that every actual yielded checked body continuation is code. It does not require physical validity or structural inputs. It does not convert a blocked or failed body to a yield.

`body_certified request inputs before after next rest good semantic yielded post continuation` certifies the exact emitted code at the actual returned native machine. It splits the current body branches and retains the literal operation-state return in the supplied yield equation. Errors and missing fields cannot match that equation. Mismatch and rejection bind the sentinel certificate. Ready conjunction binds the actual selected combined field and ordered child code. The native machine is unchanged by this prefix. The continuation receives the exact local edge certificate, physical result residency, and the reached machine's validity, extension, and semantic readiness.

The continuation is a static code-certificate composition premise. It is not an assumed successful child trace, a parent result law, or a completion callback. The initial `Good` and `SemanticReady` premises remain explicit. This module does not derive a final checked-state invariant or a full trace result certificate by itself.

## Physical record issue handled in the proof

`makeEdge` instructions are indexed by child references. Equal instruction indices do not by themselves identify the complete child records used to form those references. Direct elimination of `WorkInputs` therefore cannot recover availability for an arbitrarily selected literal child list. The first draft failed at that elimination. The final proof derives availability from the actual node continuations and transports it through later extensions. It does not add an injectivity axiom, assume metadata equality, or transfer an older eager execution.

## Validation

The root canonical build passed with 1098 jobs in `edge-build-1.log`. The only warning is the older `InternedFreshOrdinaryClosedCompletion` unused-variable warning. The final direct source check, `edge-direct-4.log`, passed with exit code 0 and no output.

The final external check, `edge-checks-1.log`, passed with exit code 0 and no errors, warnings, or `sorryAx`. It imports the final canonical module and contains four public axiom/full-signature pairs. Four independently checked integration theorem pairs also pass:

1. An actual yielded body with a pure continuation derives its own emitted code certificate. The integration supplies no desired parent certificate or future continuation result.
2. Actual arity mismatch emits certified sentinel code with the literal `emptyField before.operations` state. No field load or original child-domain premise appears.
3. Actual checked conjunction rejection retains its precise returned equality-operation state, then the literal empty-field allocation. It emits certified sentinel code without a child law.
4. Actual checked conjunction acceptance emits code for the selected combined constraint and exact original child zip. The returned native state remains the initial native state. The local structural certificate follows from the original `EdgeInputs`, current valid machine, and semantic readiness.

Earlier raw logs remain available. The first records notation elaboration and the rejected noninjective-index elimination. The second compiled but reported one unused section instance. The third records the Lean placement rule for a documentation comment before `omit`. The fourth is the final clean source check. No older source was changed.

## Remaining scope

These theorems certify local current source code. They do not execute the recursive requests or prove termination. The actual trace interpreter must derive child certificates, preserve the conditional returned-cell invariant, and use exact driver finish ownership. General recursive input domains, nonempty seen lists, Mu traversal, explicit unions, runtime publication, GHC demand order, and concrete machine identity remain separate. Guards are unrestricted here. No Haskell source changed.
