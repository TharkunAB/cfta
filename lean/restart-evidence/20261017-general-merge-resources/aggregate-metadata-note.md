# Aggregate metadata schema correction

The first aggregate metadata command assumed that every component manifest had an entry_count field.
The ResourceControl manifest records its entries without that redundant field.
The aggregate metadata now counts each entries list.
The final aggregate verifier passes all four manifests and 106 entries.
No production source or frozen component evidence changed for this correction.
