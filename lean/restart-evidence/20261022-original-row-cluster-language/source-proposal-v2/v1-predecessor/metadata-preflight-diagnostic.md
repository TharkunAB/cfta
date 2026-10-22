# Metadata preflight correction
The first static assembly assertion counted the raw local-rows-binding bytes as a substring. It found three occurrences because the two header let-bindings contain that text at a larger indentation.
The corrected assertion compares complete source lines. It finds exactly one approved local binding. All actual header comparisons already passed.
This was one Python metadata assertion failure. The Lean source stayed unchanged. No compiler or prepared tool ran.
