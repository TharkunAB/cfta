The original frozen 25-line proposal remains unchanged and was not a clean linter result.
Actual strict2 elaborated the theorem and returned 0. It reported one unused-variable warning for the existential proof binder built.
The corrected proposal renames only that binder to _built. All types, binder order, let expressions, and the conclusion remain byte-identical.
The complete candidate uses exactly that one replacement. Its proof body is byte-identical to actual strict2.
Inverse replacement recovers the complete actual strict2 source and the original frozen proposal byte-for-byte.
This is a public binder alpha-renaming. It adds no premise, axiom, linter exception, or resource limit.
The corrected candidate has not been checked. Application, strict3, and FULL require separate root authorization.
