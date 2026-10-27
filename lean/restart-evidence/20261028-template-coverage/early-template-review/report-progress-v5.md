# Revision V5

Status: OPEN. Root strict check 2 failed on V4. Its complete source, report and 6989-byte log are retained. Every reported error treats the function-valued term macro as a proposed simp theorem. The actual private function is now correctly named in the term-level conversion receipt; the final definitional change no longer fails.

V5 retains that exact imported-function term macro. It adds two proof-local tactic macros. They construct an actual identifier before simp inspects its arguments. The first invokes simp with the actual private definition. The second invokes simp only with that definition, before explicit branch-condition rewrites. No recursive helper copy, new evaluator, axiom, or operational definition is present.

The constructors and public structuralTemplate_matches statement remain unchanged. All five immutable draft versions are retained. V5 is UNTESTED until Root sends its actual compiler receipt. The source assessment and public-grammar origin limitation remain as in the initial report.
