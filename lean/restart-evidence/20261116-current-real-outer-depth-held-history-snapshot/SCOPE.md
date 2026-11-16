# Outer history assembly

Status: headers frozen. The proof is not checked.

The expand component keeps the original resource-case inputs. It adds the exact
smaller-depth structural IH and the original held isolation, native lookup, and
boundary. Its result covers every actual output from the original input core.

The full depth theorem has the byte-identical frozen `a2251c0a` header. It proves
the existing global depth predicate. It has no external IH or resource provider.
The proof obtains the resource IH from the already checked resource-depth theorem.

Parked and narrowed continuations use the same original work budget. Empty and
stopped runtime branches retain their actual emitted lists. The proof must not
remove outputs from a continuing branch that stops after an earlier emission.
