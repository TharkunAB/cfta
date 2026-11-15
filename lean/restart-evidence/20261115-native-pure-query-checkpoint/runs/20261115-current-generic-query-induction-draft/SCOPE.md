# Generic actual query induction

Status: UNCOMPILED candidate. One public theorem. No compiler was run.
The source is extracted from the current public QueryGlobalLaws module.
Its verified strong fuel induction, BodyCode preservation, actual query
splits and finish handling are retained. No initial corollary is included.

## Fixed public interface

PUBLIC-HEADER.lean.txt was frozen first for consumers. Its SHA256 is
9294722a468fb4ac25c0f4619c3fb02125afe46914c864c412187d0b557533b8.
The raw module contains that header byte for byte.

The theorem accepts only the existing nodeLaw and edgeLaw functions, the two
inductive raw-body result rules, and the original supplied fuel. It retains
weak Physical validity, the actual InputsThrough plan and prior Returned laws
as ordinary query-preservation premises. It introduces no cache, model,
frame or profile type.

Each raw-body rule receives the literal original node or edge query, original
Physical and InputPlan, actual dispatch Steps1, exact first/middle states,
raw body Steps and the strict original parent-fuel bound. It receives actual
raw node and edge child callbacks from the SAME outer query. Every callback
retains the literal child request, continuation, state and positive outer
prefix, with used+count <= parentFuel. No child Returned law is requested
from the caller in either result rule.

## Prefix cache laws are derived inside the induction

For a callback whose child raw trace has count=0, the current query control
cannot equal a pure control. The two constructors differ. This eliminates
that case without a child result premise.

For count>0, used+count <= parentFuel gives used < parentFuel. Apply the
strong induction hypothesis at used to the SAME original parent query and
initial state, with its original physical validity and a weakened original
plan. Its memo-preservation projection yields both Returned laws at the
actual prefix endpoint. Rewrite with that actual prefix's Steps.execute.

Apply PrefixInputs to the SAME actual prefix. It derives the exact child
state's physical validity and raw remaining plan. Weaken that plan to count.
Since used>0, count < parentFuel. The strong induction hypothesis at count
then gives the actual child's raw result law. The result rules receive this
conclusion directly, without a future cache-history premise.

The proof uses a local past function in each parent query branch. Each such
function is defined by the strict induction hypothesis on that literal
parent query. It is not a public assumption or a state invariant provider.

## All endpoints and exact budgets

The generic BodyCodeReturned theorem still preserves both memo laws through
every compileNode branch. Its actual nodeChild and edgeChild hypotheses use
only strict original parent fuel and literal lifted outer prefixes.
The first row, union, reset or swap query may use the entire remaining body
budget. No raw-body decrease or fabricated dispatch step is inserted.

The checked edge-body theorem retains failed field loads, missing-field
blocks, rejected/sentinel branches, child walks and constructor endpoints.
Both actual query helpers retain direct node dispatch, absent, busy, ready,
evaluate and the exact finish continuation. Running cells are derived by
their existing Clean/Shape proof. RequiredCache.Ready is not introduced.

The public conclusion retains both Returned laws at every actual execute
endpoint and each raw pure result with count <= supplied fuel. The raw trace
does not spend an extra terminal observation step. Internal query-result
helpers may use execute(count+1) only to read the same observed raw result.
The public fuel and raw-count bound remain unchanged.

## Instantiation and limits

Root can instantiate nodeResults and edgeResults with the existing concrete
SelfResult and MismatchResult raw-body producers, using their SAME actual
branch equations. This packet adds no initial-cache corollary. Initial prior
Returned laws remain legitimate generic preservation premises; empty tables
can establish them separately with returned_empty.

The two body-result rules are inductive algorithm obligations, not a whole
query theorem or a completed semantic model. They must be proved for the
chosen nodeLaw and edgeLaw using the actual compiler and checked edge body.
The framework does not itself prove arbitrary semantic typing, denotational
intersection, termination, Haskell correspondence or the full accepted-source
compatible-completion goal. Auxiliary open results need no Profile premise.

The original full coupled target header is copied byte for byte. No live
source, Git, board, Haskell, compiler or temporary-directory action occurred.
