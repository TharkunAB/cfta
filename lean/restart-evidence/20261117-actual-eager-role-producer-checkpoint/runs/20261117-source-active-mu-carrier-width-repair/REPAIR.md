# Explicit carrier width

UNCOMPILED. Original f7fae392/21b2c3c7 and failure log remain unchanged.
The first ten diagnostics report unresolved width in carrier recursive calls.
Add `(width := width)` at all 8 such calls in CodeAdmission/ControlAdmission.
No logical field, public theorem header, proof body, probe or budget changes.
The remaining proof diagnostics may be consequences of the invalid definition.
Do not change their proofs until this exact definition repair is checked.
