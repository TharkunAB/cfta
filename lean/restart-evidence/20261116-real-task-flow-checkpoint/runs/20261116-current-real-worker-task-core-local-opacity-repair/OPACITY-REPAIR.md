UNCOMPILED. Original737/log51055 remain unchanged.
The six complete headers, public ORIGINAL5493 and every proof block are exact.
Only local reducibility attributes are added before the two timed-out declarations.
The captured startup now uses the original checked owner15142 context: nodeReserved
is opaque except at its explicit expansion. The prepared scan restores the checked
c831 context: eagerReserved/eagerFinal and actual resume/continue code remain opaque.
This prevents the simplifier and declaration elaborator from evaluating a full
recursive mathematical reservation or worker continuation while comparing its head.
No heartbeat increase, premise, fuel, runtime or result change is introduced.
