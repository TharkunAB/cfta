SOURCE-ONLY repair of the one actual failed root strict check. No retry has run here.
The complete raw mismatch is retained under root-failed-check with its actual input, receipt, usage and effective limits.
The generic dedup helper elaborated before Item was known, so its equality was Classical.propDecidable(a=b).
The existing count definition elaborates equality on Quotient using Quotient.decidableEq, so eraseDups had a different instance argument.
Add only [DecidableEq Item] to the LOCAL helper binder. Its proof is then polymorphic in that equality instance.
At the quotient and path call sites, Lean can select the existing concrete equality instances used by the definitions.
Prelude1069–1070 derives BEq from that DecidableEq. Core812–814 derives LawfulBEq, which the reused nodup/membership APIs require.
Core2241–2248 defines Quotient.decidableEq using the relation's decidability. Classical81–84 defines the previous fallback.
No public premise or type changes. No original declaration changes. The complete private candidate-length proof remains unchanged.
The one-line reverse transformation recovers the actual failed257 source; deleting the full append recovers the original195 source.
Root and independent source/delta review and a separate activation must precede any next compiler command.
