# Empty library and size zero at the actual public boundary

Status: FROZEN READ-ONLY AUDIT. No compiler or Haskell execution was run.
This is a source reduction and an exact map to existing normal Lean theorems.
The expected observations in PUBLIC-API-UNEXECUTED.hs.txt are UNEXECUTED.
No reachable bug or new counterexample is claimed.

## Concrete original inputs

Haskell: library [] [] [], Query [] (TVar "a"), signed size 0.
This uses FirstOrder, no components, no argument-only rows, no avoid rules and
no query arguments. The goal is a rigid type variable. No finite Program has
zero components. The Lean counterparts are the public zeroLibrary, zeroQuery
and zeroExpression in SourceSynthesisCurrentZeroDepthProductivity.lean:99-108.

## Haskell construction rejects the empty candidate before public output

1. Synthesis.hs:801 defines buildTerms _0=[]. With no query arguments,
   buildRelevant _0[] uses termsOfSize _0 at828. permutations [] has the single
   empty selection. relevantOfSize0 at838 is therefore union[].
2. Interned/Operations.hs:715-722 defines union[]. Its ordinary fast path builds
   Node[]. Interned/Type.hs:575-585 defines that smart constructor as EmptyNode.
3. Synthesis.hs:655-656 constructs the original filter with children
   [typeNodeWith FirstOrder (TVar "a"), EmptyNode]. This does not replace the root.
   Interned/Type.hs:546-552 removes every edge with an EmptyNode child, and
   mkNode:583-585 maps the resulting empty row list to EmptyNode.
   Thus rawSearchSpace emptyLibrary emptyQuery 0 is already EmptyNode.
4. The public solutionsOfSize route at973-974 runs programsIn after
   orderedSearchSpace/reduceWithOrder. Reduction preserves EmptyNode:
   Equality/Operations.hs:84 returns EmptyNode; withoutRedundantEdges uses
   mapNodesStep, whose EmptyNode equation is Interned/Operations.hs:96.
   refoldEdges:214-215 keeps it because it has no recursive unfoldings.
5. programsIn:969-970 calls runsBy and only projects successful run results.
   runsBy delegates to runsFrom (Enumeration.hs:1253-1256,1285-1294).
   There is no call to toProgram unless a run was returned.

## Actual enumeration of that same empty root

initEnumerationState stores UVarUnenumerated (Just EmptyNode) [] in slot0
(Enumeration.hs:297-311). Crucially, EmptyNode IS expandable: recursiveBoundary
EmptyNode is false (Interned/Type.hs:608-611), so expandable at473 is true.
It is not treated as an unconstrained recursive boundary and is not marked done.
The initial waiting map is empty. findExpandableUVars:835-842 and
nextExpandableUVar:863-878 therefore select slot0.

No-stop enumerateFully uses enumerateUntil' Nothing with identity narrowing
(Enumeration.hs:913-927). The selected root is read at1001. EmptyNode takes the
ordinary expand route at1014, not the recursive parking route. The identity
narrowing leaves that SAME EmptyNode at990. The literal EmptyNode case at992
rejects the branch with mzero BEFORE the Right callback, enumerateOutUVarWith,
root expansion or readback. The call does not reach ExpansionDone.
The separate enumerateNode _EmptyNode=mzero equation at724 agrees, but is not
the first rejection reached by this actual public path.

Therefore the static expected public result is [] for runsInterned, programsIn
and solutionsOfSize on these exact inputs. Rejection occurs before root readback,
not through a placeholder and not through toProgram. Independently,
expandUVarWith:1076-1082 would reject a direct unexpanded EmptyNode root, since
it is not a recursive boundary; that fallback is not needed in the actual run.
The plain terms fast path also returns [] via plainTermLevels EmptyNode at1326.

## Existing exact formal boundary, with its qualifications retained

SourceSynthesisCurrentZeroProgramObstruction.size_zero_frontend_without_program:15
already proves frontend acceptance at size0 and absence of any zero-component
Program for arbitrary Library/Query. It does not claim that the worker emits.

SourceSynthesisCurrentZeroDepthProductivity provides the concrete chain:

- zero_source_accepted:112 retains this actual firstOrderRaw result.
- zero_source_native_empty:132 says EVERY successful actual native build of
  zeroExpression returns the empty value.
- zero_source_no_native_member:154 says that same built root has no finite
  native member, for any guard interpretation and ambient environment.
- zero_source_initializer_emitted_nil:181 takes that SAME actual native build
  and its actual encodeNode receipt, retains the original caller/startup and
  ALL supplied workFuel/depth, and concludes emitted(actual worker)=[] .

The last theorem's exact policy scope is Unit metadata with empty lists,
templates[], the stored nodeEdges getter, noStop, default order and identity
narrowing. It quantifies arbitrary graph/checkEmpty/cache/width. It is not a
new all-configuration theorem for arbitrary real narrowing. Do not silently
strengthen that specialization. Its proof uses the actual empty root and
handle0; it does not force a decision or read an arbitrary replacement state.

Formal smart construction agrees with the Haskell boundary:
InternedConstructorTemplates.surviving:234-235 removes the empty-child filter
edge; makeUnion:275-277 and makeNode:248-251 return empty. Nodes.encodeNode:18
and lookupNode:25 encode/read empty using handle0. Startup marks that original
nonrecursive root expandable. A low-depth stop produces no fresh emitted output.

## Consequence for the full target

This concrete accepted but uninhabited source is NOT evidence that an actual
public source output lacks a completion: its public output list is empty.
The full completion theorem must quantify an output of the SAME actual original
source worker. It must not quantify all initialized or diagnostic lower-worker
states merely because a partial observer can render them.
No new source filter, larger fuel, model premise or root replacement is needed
to exclude this particular size-zero case. Other source cases remain untouched.
