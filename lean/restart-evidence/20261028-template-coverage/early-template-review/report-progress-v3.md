# Revision V3

Status: OPEN. Root strict check 1 failed on V2. The failure is retained in checks/structural-template-meaning-strict-1. Its 6764-byte log reports missing constructor documentation, marker-match case splitting, an unresolved Matches.node pattern-list argument, and failure of the copied recursive helper to be definitionally equal to the actual private source helper. The V2 name-only text comparison remains a historical record. It is not a successful definitional-equality proof.

Root then checked a proof-local macro that constructs the actual private Lean name with Lean.Name.num. The successful template-private-macro-1 receipt and exact probe source are retained. V3 uses this macro to refer to the imported private constant. It has no copied evaluator.

V3 also documents both new constructors, branches on the explicit symbol and marker Boolean conditions, and supplies the exact original child-pattern list to Matches.node. Its public ProgramEncoding definition and structuralTemplate_matches statement are unchanged. The final change names the same actual private helper as the original structuralTemplate receipt.

V1 and V2 remain unchanged. V3 is immutable and UNTESTED until Root reports its actual check. No compiler was run by this worker. All earlier source-scope limitations remain.
