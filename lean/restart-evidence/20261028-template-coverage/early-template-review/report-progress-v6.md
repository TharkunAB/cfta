# Revision V6

Status: OPEN. Root strict check 3 failed on V5 with a 5782-byte log. The actual private-constant tactic macros now work. Only the local marker condition failed: Lean generalized the match over both second and the dependent converted receipt, while the actual source helper matches only second. The exact source and failed receipt are retained.

V6 changes only that local Boolean match to match (generalizing := false) second. It preserves the actual imported helper, both proof-local tactic macros, ProgramEncoding, and the public theorem statement. No additional premise or evaluator is introduced. Root will check the immutable V6. No compiler was run by this worker.
