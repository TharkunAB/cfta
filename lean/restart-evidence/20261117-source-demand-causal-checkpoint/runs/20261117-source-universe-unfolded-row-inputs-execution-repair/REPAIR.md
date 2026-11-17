# Explicit selected-unfold proof repair

Status: FROZEN, UNCOMPILED. The original failed packet and strict-check log remain unchanged.

The public header 514c8cf3 and probes are byte-identical.

Proof edits:

- Omit the unused EdgeKey DecidableEq instance from the two pure membership helpers.
- Follow the actual stored-unfold outcome with its explicit equation. Use the existing SelectedValue.run equation to identify the same value and endpoint.
- Rename the reserved proof-local identifier `universe` to `fullUniverse`.
- Project the child-kind conjunct from the existing source row fact. Its first conjunct is the Top guard equality.

No premise, result, operation, fuel, proof limit or linter setting changes.
