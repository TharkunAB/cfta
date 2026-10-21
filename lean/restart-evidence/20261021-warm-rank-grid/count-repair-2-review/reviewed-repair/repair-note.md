SOURCE-ONLY repair of actual root strict2. No retry has run here.
The first quotient equality mismatch is repaired, but the full strict2 raw shows a second mismatch at255 for paths.
positivePaths uses the existing native List.instBEq. The DecidableEq-polymorphic helper derives instBEqOfDecidableEq instead.
Replace only the LOCAL helper binders [DecidableEq Item] by [BEq Item] [LawfulBEq Item].
This gives each call site control of the exact existing Boolean equality instance.
SymbolicDriver.eraseDups_nodup and List.mem_eraseDups require exactly BEq and LawfulBEq. Nodup.length_le_of_subset has no instance requirement.
Native List BEq and LawfulBEq definitions are in installed Init/Data/List/Basic144–162.
No public premise/header, private candidate-length proof, original declaration, import or mathematical goal changes.
The reverse one-line replacement recovers the actual strict2 input; deleting the whole append recovers original195/7647.
Keep repair1 and all previous reports unchanged. Require root and independent source review and separate activation before any compiler command.
