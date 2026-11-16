UNCOMPILED minimal actual-hole normalization repair.
The strict77859 log for original2196 has exactly two proof errors: the hole
branch change pattern is not definitionally equal, and bare finishChecks is not
opened. Prior936c already qualifies finishChecks and is retained unchanged.

Replace only the guessed hole-body change block by `rw [expandPartial] at actual`.
Then invert the literal public operation's actual bind, as before. This uses the
actual source equation directly and avoids reconstructing its match closure.
All later branch proofs remain byte-exact. Complete8186 public headers/probes,
all premises, returned states and original fuels remain exact. No Source,
compiler, checking-budget or private-visibility change was made.
