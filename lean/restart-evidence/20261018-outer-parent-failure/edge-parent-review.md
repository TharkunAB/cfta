# Initial Parent-failure exclusion at an outer edge call

Date: 2026-10-18 07:57 CEST.

## Contract

SourceCurrentOuterEdgeParentFailure.lean has SHA256
`8debd2a70cee572f6e47f5d26b724403f8c8b15e75f1ae7bd193ab9238d28933`.
Its one public theorem is edge_no_parent_failure.

The theorem takes the initial semantic Context, Frame, profile Fits,
finite physical edge-guard carrier, inherited equality Ready, original
edge residency and pure UniformReserved. Each of the nine supplied lower
fuels must cover ParentUniformEnvelope.fuel at that initial alphabet and
profile. The outer fuel is arbitrary. The conclusion excludes every
Parent.Fault at the literal local edgeCall return, at every final caller.
There is no observed-success, notBusy, future graph, reached-state support
or future callback-result premise.

## Actual owner proof

The proof inspects the actual beginEdge result. A ready hit returns a done
value. Busy and absent demands return their edgeMemo diagnostic. These
three branches cannot return a parent diagnostic.

For evaluate, CallSteps.edge_start derives the captured original owner's
Context, inherited Ready and resident input. beginEdge_components proves
that this demand keeps the checked state. The initial Frame, Fits and
carrier therefore hold at the captured owner. UniformEnvelope.complete
constructs that owner's actual Parent return. Its nine-fuel replay gives
a done return at the supplied lower fuels. Literal edgeBody and edgeCall
then cannot return any parent diagnostic. No owner request equality is
assumed. The derived owner facts cover the captured request.

## Validation

edge-parent-direct-1 checks the immutable production snapshot with all
linters. Its raw log is zero bytes. edge-parent-canonical-1 completes the
single canonical target. edge-parent-public-1 checks and prints the complete
signature, proof and axioms of the one declaration. The source enables all
eight required print and linter settings. The verifier rejects omissions,
printer failures, sorry and diagnostics. Only the standard three axioms
are permitted.

Each selected run uses a five-minute cap. Effective memory.max and
memory.high are 4294967296. Effective memory.swap.max is zero. The owned
runner, worker, readbacks and unique peak log remain in this directory.
No attempt failed. No queue setting changed.

This component adds one public pair and no constructed pair. Root owns
the separate global phase and constructed execution checks. They are not
assumed here and are not counted or pinned by this component.

## Boundary

This theorem excludes local Parent faults with sufficient initial lower
resources. It does not exclude edgeMemo busy or absent observations,
prove an arbitrary outer call succeeds, exclude all active-owner key
collisions, bound fresh requests or establish general termination.
The initial semantic Context and resource reservations remain explicit.
A separate initial Room theorem can derive UniformReserved. No Haskell
source or runtime correspondence result changes here.
