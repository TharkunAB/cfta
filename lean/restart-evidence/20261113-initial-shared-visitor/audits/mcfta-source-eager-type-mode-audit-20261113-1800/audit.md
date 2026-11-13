# Opaque Type modes and a joint child-tuple witness

Status: bounded read-only audit. No runtime probe, proof body or source counterexample is claimed.
The prior audit94/target10 and the checked size-zero obstruction remain unchanged.
Paths in this note refer to inspected current source. Exact hashes are in source-pins.json.

1. A new useful boundary: checkEmpty does not control literal-empty rejection.
   SourcePruningEnumerationSharedIncomingNode.run:67-88 sends the actual merged query
   through IncomingNode.finish even when checkEmpty=false leaves that query unchanged.
   IncomingNode.finish:30-35 always rejects replacement=.empty. Its existing
   finish_complete:95-110 returns the literal empty result list in that case.
   Haskell Enumeration.hs:514-530 writes the merged value, then always guards
   not(hasEmptyContents new). Both modes reject a literal empty created by a child merge.
   Thus the proposed g:Int, goal Bool, size1 candidate cannot escape ONLY because
   checkEmpty was disabled IF its actual terminal intersection is literal empty.
   No full source execution or surviving output for that candidate has been established.
   Earlier native reduction may already remove the candidate.

2. What the Boolean actually changes.
   With checkEmpty=false, SharedIncomingNode.run skips the enabled emptiness worker.
   With true, SharedEnabledEmpty.check:32 first runs the descendant gate; a false gate
   skips the worker. SharedEnabledEmptyActual.Outcome.completed:26 maps that skip
   to some false. Even true does not run a complete SAT test for every domain.
   Haskell Enumeration.hs:204-218 applies provablyEmpty only when BOTH checkEmpty
   and reachesConstrainedMu intersection hold. The extra test can replace a query
   by EmptyNode; it does not turn all surviving queries into certified inhabitants.
   provablyEmpty:576-601 documents its budget and undecidability boundary.
   A skipped, open, or unread conjunction may contribute a conservative false answer.
   No mode restriction of the form checkEmpty=true alone closes finite-witness existence.

3. Pin the actual default mode before comparing coverage.
   Haskell initEnumerationState:296-311 derives the flag from reachesConstrainedMu root.
   Synthesis.orderedSearchSpace:774-775 first uses reduceWithOrder; programsIn:970
   then calls runsBy on THAT spaceNode. The flag belongs to the reduced input.
   CurrentProgramEagerOutputs.accepted instead starts from its SAME raw source build
   and accepts checkEmpty as configuration. Its parameter is not the above derived flag.
   The exact preprocessing/flag correspondence is a separate unfinished boundary.
   Turning a Boolean on in the raw theorem is not proof that it covers the default route.
   Conversely, no reached-source counterexample currently establishes that the raw
   finite-root target MUST exclude false mode. Do not document a necessity without one.

4. The current source shape is useful, but is not an occurs certificate.
   CurrentSourceGuards.firstOrderRaw_guards_plainMu:320 derives PlainMu for the raw source.
   PlainMu (RecursiveOrigins:23) describes source binder guards. It is not a model,
   a proof of productivity for every reached domain, or a trace of the reduced root.
   Haskell enumerateNode:725-733 and formal ShallowChild.prepareChild:17-37 allocate
   Mu/union with an empty bucket when there is no terminal suspended constraint.
   That branch does not inspect checkEmpty. Terminal constraints instead enter the
   actual shared merge. Native shape and those SAME terminal results are decisive.
   EnumerationOrder.Stratified:18-22 controls enumerated Fragment dependencies.
   All pending slots can share the frontier. It does not rule out a finite-Type
   occurs obstruction hidden inside their native domains and shared path requirements.

5. Existing occurs lemmas are not an actual eager rejection observation.
   SymbolicNormalization.occurs_constructor_reject:454 proves that a finite assignment
   cannot equate a variable with a constructor term containing it, by term height.
   SymbolicUnification.lean uses that separate symbolic Problem/count engine.
   Neither API supplies a finite unifier for the actual native eager child tuple,
   nor states that its native/emptiness path rejects every such source obstruction.
   They can validate an extracted equation, but cannot replace the missing trace link.

6. Smallest useful next constructive interface, without a new provider premise.
   joint-source-row-child-witness.lean.txt states an UNPROVED added conclusion at the
   SAME actual completed source-row tuple: ONE assignment fills ALL ordered child
   fragments in their original source-child native languages AND satisfies the full
   source-row guard on their assembled parent. No separate child models are joined.
   This uses existing Fragment/fill/native meaning; it introduces no typing hierarchy.
   The assignment is a CONCLUSION. Current source RowCall/origin, guard projection,
   equality-class allocation and actual completed tuple receipts are its proof inputs.
   Source ancestry must be derived from the actual shared driver, never supplied as
   a desired original-row match or taken from the old nonshared Parent observer.
   Current source field-layout/ordinary typing observers can consume the resulting
   finite terms. They cannot construct this simultaneous assignment in advance.
   A proof must derive compatibility/no finite occurs obstruction for the same chosen
   Type classes, including ordinary constructor choices and untouched opaque domains.
   A different independent witness per child, allTypes' var1 witness, or a supplied
   future unifier leaves this exact step open. Old Type assignments may need revision;
   the target does not demand fresh-only extension of an unrelated assignment.

7. Status and scope.
   No actual emitted firstOrder-source counterexample was found by these read-only checks.
   The Bool/Int mechanism above is excluded conditionally by an unconditional empty
   rejection law, not by a newly proved execution of that input. No new defect is claimed.
   No Boolean-only mode restriction is presently justified as necessary or sufficient.
   The next semantic proof must either build the joint finite solution from the actual
   source-origin choices or retain a real source execution that contradicts it.
   This local row interface is not yet the full original-root/partial witness, and is
   not claimed for arbitrary native states. Ancestor pullback, actual partial sharing,
   source completeness and Haskell correspondence remain part of the full objective.
   No compiler, probe, live edit, Git, Haskell change, board or cleanup action was run.
