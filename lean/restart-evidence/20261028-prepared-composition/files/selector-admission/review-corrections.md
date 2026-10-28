# Prefix review correction

The preliminary review of PreparedPrefixOrigins v1 missed a changed conjunction association. Its literal inverse removed grouping parentheses too broadly. Comparing the resulting declaration string with the old source therefore did not certify the retained Lean conjunction subtree.

Root's actual prepared-prefix-v1 strict check rejected the mismatch. The supplied `retained.left` had `(PrefixValid ∧ Resources ∧ packetMatch) ∧ forallModels`. The draft expected `PrefixValid ∧ Resources ∧ packetMatch ∧ forallModels` at a different structural position. The full failed source, report and raw output are retained in checks/prepared-prefix-v1. The early report and reviewed v1 source remain unchanged as historical preliminary evidence.

The final review must compare the old retained grouping without globally removing parentheses and must read the complete actual checked public type. Only the new appended observer's exact parentheses may be removed in a literal inverse. No final CLEAR is issued for the failed v1. This was a review miss; the compiler prevented the malformed wrapper from passing. The intended counter equality and same-assignment argument are separate from that statement assembly error.

CheckedProjection v3 independently passed Root's strict check with empty raw output. Its exact installed/draft/snapshot identity is recorded in checked-status-v3.json. All earlier failed versions remain.
