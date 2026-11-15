# Actual all-branch Returned induction

Status: UNCOMPILED candidate. No compiler was run. The whole initialized
mismatch-history theorem is not proved by this packet.

## One existing source predicate

Use `SourceRecursiveIntersectionCode.BodyCode`. It excludes explicit
`finishNode` and `finishEdge` instructions. The checked driver adds those
frames. `compileNode_bodyCode` covers every actual compiler branch.
The candidate adds no second code predicate or cache framework.

The generic theorem accepts existing node and edge `Returned` predicates.
It takes only genuine smaller query hypotheses. Each query must occur at a
positive actual prefix of the same outer control, initial state and original
parent budget. The prefix retains the literal request and lifted continuation.
The result preserves both predicates at the complete actual endpoint of every
supplied remaining budget. It requires no local body-result law.

## Exact recursive budget

Let N be the original outer query fuel. Let s be the actual outer prefix
length and r the remaining raw-body fuel. Require s > 0 and s + r <= N.
A query at the first raw-body instruction can use all r fuel. The candidate
therefore uses queryFuel < N. It does not require queryFuel < r.

At a query, `bind_endpoint_state_cases` gives two actual alternatives.

- Execution remains inside the query. Apply the smaller query hypothesis at
  the unchanged r budget and the same lifted outer prefix.
- Execution reaches the source continuation. If the raw query reaches pure
  after k yielded steps, use its actual execute(k+1) done equation to obtain
  both Returned laws at that same middle state. Append its k-step trace to
  the original outer prefix. Induct on the actual source continuation at
  fuel r-k and outer prefix s+k. The arithmetic bound is unchanged.

The source continuation may begin at zero further steps. No fake yielded
step or raw-body fuel decrement is inserted for reset, swap, rows or union.

## Source instructions

| BodyCode instruction | Actual transition | Cache reasoning |
| --- | --- | --- |
| pure | done with same complete state | Both prior laws remain. |
| fail | failed with same complete state | Both prior laws remain. |
| work | Actual run and actual advanced heap | Both memo tables stay fixed; induct on the actual continuation. |
| enter | Actual entered domain and advanced machine | Both memo tables stay fixed; induct on the actual continuation. |
| read | Actual SourcePreparedSharedRows.read result | The full state stays fixed; induct on that exact continuation. |
| optionalBinder done | Actual maybeMu result and heap | Both memo tables stay fixed; induct on that exact continuation. |
| optionalBinder pending | Actual blocked constructor and heap | Both memo tables stay fixed at the actual stopped endpoint. |
| node | Same actual request with lifted source continuation | Smaller actual node-query hypothesis plus endpoint split. |
| edge | Same actual request with lifted source continuation | Smaller actual edge-query hypothesis plus endpoint split. |
| finishNode / finishEdge | Excluded by BodyCode | No finish supplier is assumed. |

## Complete compileNode branch coverage

| Actual selector | Existing BodyCode route | First raw-body query offset |
| --- | --- | --- |
| empty | pure empty | No query. |
| self | pure original left operand | No query. |
| repeated key | pure repeatedValue key | No query. |
| unsupported | fail with literal operand references | No query. |
| reset | literal empty-domain node request | Zero; strict only against original outer fuel. |
| swap | literal reversed node request in same domain | Zero; strict only against original outer fuel. |
| bothMu / leftMu / rightMu | Actual enter, literal body query, actual optionalBinder | One for supported identity pairs; unsupported identity alternatives fail. |
| leftUnion / rightUnion | Ordered walk of literal members, then actual makeUnion work | Zero when nonempty; no synthetic distribution step. |
| leftReference / rightReference | Actual name test/read; exact found operand query | One after an actual read; missing cases fail. |
| ordinary | Actual ordered pairs walk, then actual makeNode work | Zero when a pair exists; no synthetic row step. |

`compileNode_bodyCode` also retains all defensive constructor alternatives
that compile to unsupported. No open/closed, original-only or Profile premise
is needed for this preservation statement. An auxiliary open repeated
reference or partially closed Mu result has the same trivial node result law.

## Instantiate the requested initialized law

Use the existing Returned predicate with these fixed laws:

    nodeLaw := fun _ _ => True
    edgeLaw := fun request row =>
      request.left.children.length != request.right.children.length ->
      row.children = [.empty]

The notation above is explanatory. The application file gives Lean syntax.

1. Initialize both memo tables with `returned_empty`.
2. Prove node and edge query preservation simultaneously by strong induction
   on the original query fuel. The smaller hypotheses are actual queries,
   not arbitrary source bodies or future completion providers.
3. For a node query, the generic query helper supplies its actual one-step
   body prefix and the prior Returned laws after lookup/demand. Instantiate
   this candidate using `compileNode_bodyCode`. Its parent result-law clause
   is True and requires no semantic result argument.
4. For an edge query, `edge_query_returned_of_body_induction` still needs the
   actual body preservation and local mismatch result. The existing actual
   edge-body preservation helper handles every endpoint. For equal arities,
   the conditional edge result law is vacuous. For unequal arities, use the
   actual canonical mismatch body and its same physical constructor facts.
   Do not assume a future sentinel result.
5. The existing query helpers derive exact running-cell retention from Clean
   code and physical Shape. They handle direct node dispatch, absent, busy,
   warm ready, evaluate and the actual finish. No running-cell provider is
   introduced by this packet.

The candidate's two child hypotheses remain generic so later full C/M/Aux
families can reuse it. They quantify only actual positive outer prefixes and
strictly smaller original fuel. They do not assume Profile for open results.

## Physical admission boundary

The generic source-body lemma does not assume Physical or InputsThrough.
It does not need those facts once the smaller actual query laws are supplied.
When the strong fuel induction instantiates those query laws, obtain physical
validity and the raw child InputsThrough plan from the SAME original plan and
actual prefix. Node key safety remains conditional on an actual encoded key;
edge key safety comes from its actual current input check.

Canonical's separate physical-plan projection supplies this transport.
No physical-plan file is added here. RequiredCache.Ready is unnecessary for
prefix physicality when step_valid suffices. Weak physical cache validity
alone does not imply word bounds, future InputsThrough, or the mismatch law
at arbitrary pre-existing warm cells. Starting from empty tables removes that
last initialization assumption. Original caller admission must still be
produced from the actual source context and bounds.

## What remains open

The candidate is not yet checked. The original all-fuel initialized node/edge
Returned induction still needs assembly and its actual mismatch-body result
producer. Whole accepted-source compatible completion and all original full
clauses remain open. The original coupled header is copied byte for byte.
No compiler, live source, Git, board, Haskell or temporary files were changed.
