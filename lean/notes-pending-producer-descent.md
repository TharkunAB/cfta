# Missing observation in the shorter-producer descent

The proposed descent is not yet proved. The existing joint-key witness is
stronger than the ordinary-support fixture, but it does not contain the
paired producer executions needed by the current replay theorems. No
pending counterexample or counterexample to the full joint-key witness was
found in this review.

## What the witness retains

`InternedPendingJointKeyMismatch.Mismatch` retains three distinct source
observations. They must stay separate.

1. The pending site's two current callbacks return the active ancestor's
   exact original Depth and ordinary records. `Site` retains these calls
   and their actual chronological cuts.
2. The earlier completed representative of that same site has two actual
   callbacks and a completed request before the active missing cut. At
   least one component of this earlier pair differs from the active pair.
3. A shorter outer producer has one completed Depth callback. Its cached
   depth equals the changed later ordinary level. This callback finishes
   before the active ancestor's original start.

The two compared crossings have the same body. The outer producer's body
is a different existential variable. No equality between these bodies is
provided. Equality of their cached depths cannot supply that equality.

## Why the current descent does not follow

`Inputs` in `InternedPendingOrdinaryOrigins` stores the outer producer's
body, captures, source context, one completed Depth callback, computed
level, and growth to the current state. The strict length inequality is
preserved by each lexical crossing. The predicate does not retain a
lexical suffix relation between the producer captures and the active
ancestor's captures. It also does not retain a source path from that
producer body to the pending site.

More directly, the producer observation has no second execution of that
same body. It therefore supplies no pair of producer Depth callbacks with
different levels. It also supplies no producer ordinary callback, complete
producer request, or second joint-key pair. The mismatch's two earlier
callbacks belong to the pending site's body, not to the shorter producer.

`earlier_pair` requires a completed binder build and its completed request.
A completed Depth callback alone cannot discharge this premise. In source
order, the ordinary callback and request follow the Depth callback. A
descendant in the producer's ordinary callback can execute before that
producer has issued its own request. Existing growth relations record
this order but do not supply a completed request at the earlier cut.

## Next exact obligation

A valid descent must first construct another actual observation of the
shorter producer's same body. It must retain the capture relation, both
normalized callbacks, and chronological growth into the original cut.
Only then can it establish a changed producer pair or computed level and
use the strict capture-length decrease. This construction must use both
equal components of the current pending site's key; support membership
and the aliased ordinary level are insufficient.

The closed ordinary-capture fixture remains useful negative evidence for
those weaker premises. `closed_different_pairs` proves that both fixture
components differ from the ancestor pair. It cannot refute or discharge
the full joint-key case. No new Lean theorem or admitted draft was added
for the missing descent.
