# Definitional route only

The actual repaired nodeEdges has a direct Empty branch. It returns empty rows and the SAME heap before it examines fuel. Filtering those rows leaves an empty list. surviving and canonicalEdges leave that empty list empty. Actual makeNode then requests Work.pure Empty, and actual run returns Empty with the SAME heap. Actual narrowAt therefore returns done Empty before at every fuel, including zero.

This route needs only the existing theorem-scoped EdgeKey equality instance used by narrowAt. It does not require Ready, Available, closedness, Coherent, success, an output law, or a fuel lower bound. It does not use the OLD source reader. No proof body, local fact, or skeleton is included. Root owns all proof text and compiler checks.
