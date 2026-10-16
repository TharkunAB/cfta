# Source correspondence of the completed current recursive graph

Read-only review on 2026-10-16. No new Haskell defect or incorrect modeled
source branch was found. No source edit, build, test, or Git command was run.
This review addresses source correspondence and the next execution bridge.
It does not replace the independent semantic/kernel reviews.

## Literal reduction schedule and arguments

* Equality/Operations.hs:68–81 starts reducePartially with EmptyConstraints
  and uses a distinct process-global binary memo family for reducePartially'.
  The graph's NodeCall retains its inherited value and input node in a
  complete request, keyed by the inherited identity and tagged node reference
  (PartialState.lean:28–49,68–72). This is a logical physical-key adapter,
  not an implementation proof of Typeable selection, hashing, or machine IDs.
* Equality/Operations.hs:87–96 maps reduceChildren inherited AFTER
  reduceEdgeIntersection inherited. The argument of reduceChildren is the
  RETURNED edge. Graph.Rows.cons uses that exact narrowed edge as its
  Descendants input (PartialGraph.lean:87–104). Its raw field, symbol, children,
  and even sentinel arity are therefore taken from the returned edge, not
  from the initial row. The central proof preserves this at PartialActual
  lines 161–193. It derives the first call, returned-edge descendants, and
  remaining row effects in that order.
* Equality/Operations.hs:95–96 combines inherited FIRST with equalities of
  the returned edge's complete guard. InheritedPrefix.run:30–41 implements
  that order and retains the actual operation state. It short circuits an
  inherited contradiction before demanding the own accessor. This follows
  Equality/Constraint.hs:449–453, whose first contradiction equation returns
  before inspecting its second argument. Do not exchange this with the
  local precheck order: Equality/Operations.hs:209 combines own ecs FIRST,
  then inherited ecs. These are distinct operations and memo keys.
* Constraint.hs:129–136 reads the stored equalities plus positive guard Same
  atoms. The prefix uses the actual accessor, not merely the raw stored
  equalities field. Its exact receipt connects the combined payload to
  inherited satisfaction AND these sourceEqualities. The full raw guard
  remains on the returned/rebuilt edge.
* Equality/Operations.hs:143–145 maps EmptyNode over a contradiction and
  otherwise zipWiths actual descended inherited values at indices 0,1,... .
  Graph.Children/Walk and PartialActual:194–225 retain that offset, head,
  and tail. PartialDescent supplies actual completed allocation payloads.
  A contradiction erases each existing slot, so [] maps to []. There is
  no general zero-child rejection or empty-language theorem from erasure
  alone. The inherited-conditioned law correctly avoids that claim.

## Empty, union, Mu, and reconstruction

* EmptyNode and InternedUnion return unchanged in source lines 84 and 86.
  Graph.NodeBody and PartialActual:125–131 preserve these cases. Their
  NodeLaw is reflexivity, even when inherited is contradictory. This law
  claims narrowing and exactness for inherited-satisfying input terms; it
  does not assert that every output term satisfies inherited constraints.
* The source line 85 uses the BIDIRECTIONAL Mu pattern. Type.hs:674–676
  expands construction to createMu. It is not a plain identity return.
  Type.hs:771–783 reuses stored depth/ordinary probes on these construction
  arguments; createMuDontCleanup:735–753 applies its stored-body filter,
  interns, then createMu:691–698 removes redundant/self-only binders.
  Graph.NodeBody.binder records actual rebuild=.done at the actual heap.
  CallSteps.node_binder derives result=cleanup(original Mu) and same heap
  from resident filtered probes before using a reflexive physical post.
  The language law is cleanup_exact. Initial ProbeHeap is explicit and
  preserved along the actual schedule. It is not inferred from arbitrary
  generic readiness. No unsupported source identity shortcut is used.
* Type.hs:398–400 directly interns the complete original field and new
  children on the SAME-arity setChildren branch. It does not call mkEdge.
  Graph.Children.length supplies exactly this arity equality for the
  RETURNED edge. RawRebuild.edge/edge_same_arity:30–44 uses the direct
  constructor; PartialActual:190–193 derives its actual physical receipt.
  No universal original-edge arity or initial Top-field premise is added.
* Type.hs:620–627 compares the ordered new and old row lists. Edge Eq is
  edge identity equality (Type.hs:209–216). RawRebuild.modify:47–50 uses
  that literal ordered identity comparison. The unchanged branch retains
  the original node and whole checked state. Resident coherence derives
  complete row equality on this branch (RawRebuild:160–170). Changed rows
  use the real node constructor, which removes empty edges and deduplicates
  and orders the survivors (Type.hs:583–585). The proof derives its row-union
  language; it does not claim returned node rows equal the preprocessed list
  including empty/duplicate rows. Source row order and multiplicity remain
  in the traversal trace before this constructor preprocessing.
* Source line 91 reports the Rec error. The completed graph has no successful
  reference body and proves NodeBody.reference_error. This is not a proof
  that every source input avoids the error.

## Result memo publication and stored owners

Equality/Operations.hs:80–81 and160–161 use TWO distinct memo families.
Interned/Memo.hs:93,116–128 dispatches the appropriate typed table and pairs
the arguments. Interned/Cache.hs:149–155 first looks up, then installs a lazy
candidate with keep-first, then rereads the winner. A hit does not evaluate
its candidate body. The installed thunk captures its complete original
arguments. EqConstraints Eq/Hashable compares its interned identity or
contradiction tag (Equality/Constraint.hs:288–309). Node Eq is tag-sensitive
(Type.hs:289–295); edge Eq compares identity.

PartialState beginNode/beginEdge models publication and demand separately,
retains that complete original request, and exposes suspended/evaluating/
returned phases. The actual begin equation selects the stored owner, not a
new candidate. PartialActual:117–124 and141–148 derives this owner's input,
runs the smaller actual owner body, protects its exact evaluating handle
through Frames, and installs the derived owner law before transporting it
to the candidate physical key. A busy observation has no successful graph
constructor (Graph.NodeCall.not_busy/EdgeCall.not_busy). This is faithful to
the intended completed serial owner discipline. It is not a GHC blackhole,
exception, concurrency, or lazy-heap correspondence theorem. The logical
finish point projects a fully completed resident body; source publication
occurs earlier, when the thunk is installed. Lost concurrent candidates and
partial thunk evaluation are not equated with graph body execution.

## What the central theorem now proves

PartialActual.lean:227–277 proves eight claims by the supplied strict-read
mutual induction. It derives the smaller child laws, physical effects,
current inventory admission, semantic/cost/field/probe invariants, warm
result-cell laws, merge/fourth retention, and validity of the SUPPLIED final
three-family global bundle at the SUPPLIED actual return. The strict primary
reads tie each queried record to its actual endpoint. There is no implication
from older unanchored primary reads to this schedule refinement.

PartialChecks.Checks:141–164 ranges only over actual reached edge-body leaves
and asks their conditional live-load Scan word checks. It contains no desired
language, final readiness, successful future call, or recursive completion
premise. The central theorem consumes a finite completed graph with strict
reads. It does not produce such a graph for arbitrary requests.

PartialActual.root_exact:279–293 discharges inherited satisfaction using an
actually allocated ready empty payload. It derives full independent PCS
language equality for that supplied completed root call. Initial Context,
input residency, inherited readiness, and reached word checks remain
explicit. Source history can establish the physical/field/probe inputs;
empty tables can establish initial caller soundness. Admission and coherent
warm tables must remain tied to the actual current state. The theorem does
not silently reset them or derive an arbitrary warm cache from key presence.

## Smallest next operational bridge

1. Add an explicit outer-control worker for these eight raw graph families.
   Its instructions should perform real begin/demand, inspect node bodies,
   run the checked parent leaf, execute inherited-first combination and
   actual indexed descent, rebuild raw edges/nodes, and finish exact handles.
   Keep busy, missing field, checked errors, and raw Rec errors observable.
   Do not supply a completed recursive body as a callback premise.
2. Prove worker completed-run erasure to the SAME raw trace and strict Reads,
   with exactly the returned caller state and global bundle. Conversely,
   a supplied finite graph may justify enough worker fuel; that still does
   not prove all requests complete. Derive reached Checks from the worker's
   actual primitive word-range plan rather than from future final validity.
3. Compose erasure with PartialActual for the literal worker's partial
   correctness. Establish cold/warm initial Context causally from original
   allocation histories, loaded-field coverage, inventory admission, and
   previous actual receipts. Keep filtered ProbeHeap explicit in this chain.
4. Prove source demand adequacy separately. Haskell map/zipWith are lazy;
   modifyNode's list equality may demand only an initial row prefix before
   the constructor demands more. The graph chooses completed head→tail
   effects and already-resident inputs. It does not prove the source's exact
   WHNF demand, list-spine forcing, allocation order, thunk publication, or
   losing-writer behavior. The general Mu callback still has no operational
   global-unfold Runs adapter in the strict Reads definition. Native/query
   component event receipts do not supply that missing outer adapter.
5. Keep general outer termination separate. The source itself identifies
   two sufficient-case arguments and leaves the other inputs and repeated
   fixpoint passes unproved (Equality/Operations.hs:119–142). No global
   decreasing measure for generated constrained descendants follows merely
   from this completed-graph induction. Int/identity counter capacity and
   tagged encoding safety also remain runtime premises (Cache.hs:89–91).

No concrete source bug was found; no FINDINGS registry repair is needed.
