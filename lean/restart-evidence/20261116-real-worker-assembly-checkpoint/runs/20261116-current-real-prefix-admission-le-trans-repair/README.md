# Real-prefix admission inequality repair

Status: UNCOMPILED. Root owns the compiler and publication.

This packet retains the original 252-line candidate and all its premises,
conclusions, state endpoints, and runtime budgets. It changes two proof terms.
It replaces `mass.trans originalMass` with `Nat.le_trans mass originalMass`.
It replaces `lengthBound.trans originalMass` with
`Nat.le_trans lengthBound originalMass`.

The complete public header is byte-identical to the original header.
Its SHA256 remains `17eac8b14fce65d0b3ab754ed5f545aee99ca7b7beaf0f0246fe71c85e0c7a08`.
The appendable probes are byte-identical. They contain no imports.
PROOF-ONLY.diff records exactly the two changes.

The failed original candidate, its packet, and its log remain unchanged.
The original check reported only these two primary errors. It provides no
proof credit for the whole theorem. Root separately checked and applied the
three visibility-only dependency exports. This packet requires those exports.
It does not change any live source or repeat that patch.

The scope remains actual continuing real-prefix admission at the original
workFuel. It is not the full real-worker induction or the same-root finite
accepted-completion theorem.
