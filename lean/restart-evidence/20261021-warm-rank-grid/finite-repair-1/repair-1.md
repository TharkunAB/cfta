Clear the unused dependent bound after extracting the suffix length. The induction hypothesis then has the intended conjunction type.
Remove both later dsimp calls. The first public proof dsimp already reduces the nested let expressions.
The actual failed check reported two induction-hypothesis projections and the first redundant dsimp. The later redundant dsimp was removed by source inspection, not by a new compiler probe.
The three public headers, imports, numeric equations and resource conclusions remain unchanged.
The original input, complete raw log, receipt, limits and usage bytes are preserved.
No candidate was applied to the selected or official source, and no compiler or runtime job was run for this repair.
