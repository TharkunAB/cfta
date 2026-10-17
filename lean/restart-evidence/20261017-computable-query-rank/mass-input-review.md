# Recursive mass input bounds

The final production source is `SourceRecursiveIntersectionMassInputBounds.lean`.
Its SHA256 is `432abb1050b697392922ecb64c58d9659fbecc8013505a4668dbf3af1ca30aaa`.
The module has 184 lines and 13 public declarations.
No older production source changed in this component.

`mass` at line 20 computes structural mass from the actual tagged payload read.
It counts all three stored Mu fields.
It does not count keys, free metadata, cached depth, symbols, or guards.
It does not compare the older sizeOf input rank with mass.
The only use of sizeOf is the existing termination argument of the imported pure mass definition.

Actual readback gives mass equality for complete available inputs.
Unsupported references can map to Empty and retain unit mass.
`body_mass` at line 56 proves strict descent into an original Mu body.
`rows_mass` at line 97 and `members_mass` at line 112 cover every actual total-view row or member.
They first recover its stored payload and use the same actual child occurrence.
Their proofs retain all guards and ordered children.
They do not require a completed query or a later output property.

`mass_inputBounds` at line 133 returns the SAME `finiteInput` as the older InputExact interface.
It constructs the bounds with `structuralInputBounds`.
The size field is definitionally `mass state`.
The local weight value is definitionally `localSize (mass state)`.
The pair list is definitionally `inputPairs (inventory state)`.
Closed reference reachability follows the existing exact free-variable and payload-reachability proof.
It is not assumed as a new input law.
The carrier has `1 + 4*N` entries and its literal ordered pair list has the square of that length.
Canonical pair duplicates remain counted.

`mass_stored` at line 151 bounds EVERY input tag by the same causal Stored bound.
An unissued reference is handled by unit mass.
It is not treated as Available.
A successful recorded read uses actual Facts and the current store bound.
`local_stored` then bounds the Mu-stopping local size by the same number.
The first failed draft tried to prove availability for every payload tag.
That statement is false for unissued reference tags.
The final proof removes it and proves the numeric statement directly.
Both failed strict drafts and logs remain preserved.

The final absolute strict check exited zero with an empty log.
The delegated canonical target completed 1177 jobs.
Its only warning is the replayed historical ClosedCompletion warning.
All 13 public axiom and full signature pairs passed imported strict checks.
Both integration pairs passed on their first imported check with no diagnostics.
All reported axioms are standard: propext, Classical.choice, and Quot.sound.

The main integration constructs its own closed union with a recursive Mu member.
It derives the actual Mu body row, an interned reference child, and reference unfolding back to the Mu.
It applies strict body, row, and union descent to these same source reads.
It checks the bounds record field equalities by reflexivity.
It derives closed-root reachability bounds and causal uniform mass bounds without supplying source completion as a premise.
The second integration proves that the next unissued reference has unit bounded mass while it is not physically Available.

This component supplies the mass-based termination interface.
It does not flatten the termination tuple, prove an executable semantic-fuel ceiling, or produce a serial query resource forecast.
Those remain separate downstream obligations.
