# Retain the narrowed value beside the returned action

This additive source-only clarification leaves the original frozen assessment unchanged. It proposes no declaration, action body, or compiler job.
An action-only native success payload is insufficient: Enumeration.hs990 passes the actual narrowed Node to Right after the conditional slot action. The callback type at951–959 also receives Node, not Unit.
Retain the actual result Value alongside the optional existing EnumerateM Unit action, using existing Prod inside the existing Output-polymorphic MergedSourceComparison.Result. Keep the native heap in Result as before.
The conceptual payload is Value paired with Option of the action. This is ordinary output data, not product state or a new carrier. It retains the actual value even when encoding fails.
Test Empty first. Its payload contains Empty and the actual reject action; rejection remains the empty List, so the following Right callback does not run.
For a nonempty result, compute the model encoding once. None selects the absent-action marker while retaining the actual result and native heap. It is not Empty rejection or a native fault.
On an encoded nonempty result, select pure Unit for equal handles or the existing representative-bind-write action for changed handles. The action can capture its computed handle; an extra returned handle field is not required for the native Right continuation.
Forward an actual native failed constructor with its actual fault and heap. An enumeration error remains an error of the returned action. Neither is replaced by the absent-action marker.
After an actual successful action, the native continuation can observe the same retained result Value. It must not call narrow again or replace the actual returned heap or final enumeration state.
The current pure-Nat Lean Oracle is a separate interface. Retaining a model handle does not establish its Value/Graph correspondence. Do not claim that this payload makes that Oracle directly reusable.
The concrete template oracle currently ignores Right input, but the generic source driver still passes the exact node. Preserve that driver contract rather than specialize away the value.
Ready/availability/closure and current derived readback rule out encoding absence on the chosen completed run. They are proof premises for that run, not requirements on the executable stage's arbitrary inputs.
All other original boundaries remain: this is only the postread/pre-Right suffix; full driver, cached classification, native NodeId extraction, and typedTypes composition remain open.

Exact full-source and line-cut identities are in input-identities.json. The original plan and controls are pinned there. No old owner was edited.
