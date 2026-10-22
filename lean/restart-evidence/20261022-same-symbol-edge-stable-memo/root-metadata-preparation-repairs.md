# Metadata preparation repairs

prepare-linter-repair-1 failed before execution because a Python bytes literal contained Unicode characters.
Root changed that literal to a text string followed by encode. prepare-linter-repair-2 passed.
prepare-full-1 compared a bare theorem header with a frozen header that includes its doc comment and proof delimiter.
prepare-full-2 passed the corrected theorem check and then found the same extraction error for Stable.
Root included the leading doc comment in both exact declaration slices. prepare-full-3 passed.
The two failed FULL materializers wrote no printer or source snapshot. No FULL command had started at those failures.
All failed commands, original script snapshots and raw logs remain in the root support files.
These metadata failures add no Lean or Lake job. They do not change the selected clean proof source.
