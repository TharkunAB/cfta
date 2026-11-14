# Off-diagonal native reference control repair

Status: UNCOMPILED. Root must check the candidate. This packet claims no proof credit.

The exact input and log are copied from Root's off-diagonal-control check.
The first branch reduction leaves a match on the local `referenceValue`.
The lookup simplification therefore does not reach the actual reference call.
The candidate uses `change` to expose the exact reference call with fuel 2, the original domain, the original heap, and left=true.
The existing bound/read simplification can then apply.
A second `change` states the resulting Mu/reference request explicitly before `rw [execute]`.

The Mu step retains its exact entered domain and complete-machine continuation.
The candidate replaces `.bind _` with the full optional-Mu continuation for `pair u.identity u.identity`.
The final repeated branch retains the old off-diagonal cutoff.
The unused diagonal Mu is rewritten with the existing `unused` law, then `rfl` reduces the final machine update.
This avoids an unnecessary `simpa` and retains the exact reached domain cache.

The candidate removes only the logged unused `bodyValue` and `payload` arguments in the branch-selection proofs.
Both theorem headers are byte-for-byte equal to the input.
No assumptions, imports, operational definitions, result values, final machines, or eight-step stability statement change.
This file proves model-level control only. It does not prove the source body-alias wrapper, the full two-alias theorem, the joint original-root witness, or the full original objective.

No live repository file was edited. No compilation, Nix/Lake/heavy job, Git write, push, or board write ran.
