import hashlib,json
from pathlib import Path
h=Path(__file__).resolve().parent
r=Path('/home/tritlo/Code/mcfta')
def pin(base,path):
 data=(base/path).read_bytes();return {'path':path,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
heads=['MicroCFTA.SourceCurrentNativeOriginalRequestScope.RootedScope','MicroCFTA.SourceCurrentNativeOriginalRequestScope.optional']
paths=['lean/MicroCFTA/'+name+'.lean' for name in [
'SourceCurrentNativeRequestSourceScope','SourceCurrentCompletedBuildRootedWriters',
'SourceCurrentConstrainedCapSourceHistory','InternedProbeProvenance',
'SourceRecursiveIntersectionRequestScope','SourceRecursiveIntersectionInputInventory',
'SourceEqualityRequiredSemanticCache','SourceCurrentNativeOptionalChildOrigin',
'InternedFreshOrdinarySourceHistory','InternedFreshOrdinaryActiveOrigins',
'SourceCurrentSourceCaptureOriginalSlots','SourceCurrentNativeSelfCaptureSlots',
'SourceCurrentPublicationBodySourceRows','SourceCurrentRootedRowChildOrigins',
'SourceCurrentSourceRowTerminalSuffix','SourceCurrentSelectedBinderChildResume']]
(h/'original-scope-source-pins.json').write_text(json.dumps({'files':[pin(r,p) for p in paths]},indent=2)+'\n')
selection={'finalized':True,'strict':'original-scope-direct-2','canonical':None,'groups':[{'name':'original-scope-public-1','pairs':2,'kind':'prototype-public','full_proof':True}],'public_heads':heads,'lean_jobs':3,'failed_attempts':1,'constructed_pairs':0,'production_pairs':2,'canonical_jobs':0,'unselected':[{'name':'original-scope-direct-1','reason':'The proof used reserved prefix as a local name and had one unnecessary tactic focus. Renaming the local trace and simplifying focus fixed elaboration and the linter.'}]}
(h/'original-scope-selection.json').write_text(json.dumps(selection,indent=2)+'\n')
(h/'original-scope-peaks-final.txt').write_bytes((h/'original-scope-peaks.txt').read_bytes())
(h/'original-scope-review.md').write_text('''# Actual source execution writers for a recovered optional owner

Reviewed on 2026-10-20 at 20:19 CEST.

The two public heads are RootedScope and optional. RootedScope records original source execution Written for every full Mu equal to the same queried request's left or right operand. It also gives an exact complete Mu read and its same full-payload Written for each name in the queried domain. Written is the existing completed-source rooted writer contract. Its Reached field retains an actual source Path and callback crossings. It does not assert a unique lexical binder occurrence or that the current requester wrote the selected cell.

The actual source build is `build original [] empty = .done root before.native.machine.heap`. Its output heap is exactly the native query entry heap. Initial Good and native writer History remain explicit. The root request's operands remain Available and closed, and the existing numeric resource bounds remain explicit. Initial SemanticReady is derived from the source build. It is not a caller premise. No source Context, selected writer, desired ancestry invariant, later result, or supplied owner is an input.

The private available_writer proof gets the exact full resident Mu cell from Available.resident. CompletedBuildRootedWriters.build_writer then uses the actual same source build, empty_context and literal absence of every initial Mu in empty. This removes the prior-cell branch without a caller absence premise. scope_rooted applies that proof to the same full operands. Named bindings are read through the existing complete codec, with the same full available Mu payload and physical read_identity. It does not infer a payload from an identity bound alone.

The optional proof invokes RequestSourceScope.optional once on the same raw optional prefix. It retains that receipt's exact ChildOrigin tuple, including the actual query, enter step, completed child Trace, protected owner, site continuation and Forwarded result. A universal certificate handles every actual node-prefix Trace from that same root request. It derives NodeScope and inventory membership with node_prefix, then adds RootedScope. The certificate therefore applies to the exact earlier query Trace inside the returned Origin. It does not choose another owner by body or key equality. Its proof has no future enclosing completion premise or internal History conclusion.

The exact-heap condition is material. Source-build physical growth into a later native entry heap does not imply backward availability. A Mu created by a later native operation can be available there. This theorem does not attach such a generated entry-heap Mu to the earlier source build. Its source root is the actual original supplied Syntax, not a generated encode root chosen for convenience.

For a rooted original source execution with empty captures, SourceCaptureOriginalSlots.empty_initial excludes a row-bearing capture at any supplied original source Path. The callback prefix contains literal references, including Depth, ordinary and reserved-self names. A later generated encode root instead starts with a potentially nonempty leaves list. Its closed row-bearing captures are not eliminated by that empty-initial argument. NativeSelfCaptureSlots gives only the exact closed-leaf or stored-self substitution split. It does not supply an original source Path for arbitrary optional-generated captures.

Existing PublicationBodySourceRows can expose the same selected writer's historical raw callback, Context, Reached and SourceRow. RootedRowChildOrigins then gives an actual source child or an explicit capture/binder stop. A nested warm binder can use an earlier selected writer with different source syntax. SourceRowTerminalSuffix supplies the actual nonunion return's physical and issued suffix before whole-call selected-writer resumption. These interfaces retain actual operations. They do not imply a generated child bound, same-leaf membership through normalized unions, current-callback/writer identity, or general termination.

Strict direct2 personally exited zero with an empty raw log. Full public1 personally exited zero with two complete statement/proof/axiom groups. All eight printer settings are enabled. Mechanical verification rejects omitted output and nonstandard axioms. All three Lean attempts are retained under 4 GiB maximum/high, zero swap and five-minute limits with fresh usage checks. Direct1 had one reserved-name elaboration error and a tactic-focus warning; both are preserved. Counts are two generic public heads, zero constructed pairs and zero owned canonical jobs. Final source SHA256: cd8d2d2f79aa3edbdbcb7905cab0f900d50f43d81c05407811c9fc63ac501d96.
''')
s=Path('/tmp/mcfta-recursive-prefix-node-scope/node-scope-verify.py').read_text()
s=s.replace('node-scope','original-scope').replace('SourceCurrentAllocatedRecursivePrefixScope.lean','SourceCurrentNativeOriginalRequestScope.lean')
s=s.replace("HEAD = 'MicroCFTA.SourceCurrentAllocatedRecursivePrefixScope.node_scope'","HEADS = "+repr(heads))
s=s.replace("assert len(re.findall(pattern, printer, re.M)) == 1","assert len(re.findall(pattern, printer, re.M)) == 2")
s=s.replace("    assert '#check @' + HEAD in printer and '#print ' + HEAD in printer and '#print axioms ' + HEAD in printer","    for head in HEADS:\n        assert '#check @' + head in printer and '#print ' + head in printer and '#print axioms ' + head in printer")
s=s.replace("== 1\n    for report in reports:","== 2\n    for report in reports:")
s=s.replace("selection['public_heads'] == [HEAD]","selection['public_heads'] == HEADS")
s=s.replace("    assert 'theorem node_scope' in source.decode()\n    assert 'NodeScope source request ∧ request.domain.key ∈ inventory' in source.decode()","    assert 'theorem optional' in source.decode()\n    assert 'def RootedScope' in source.decode()\n    assert 'build original [] empty = .done root before.native.machine.heap' in source.decode()")
s=s.replace("'public_pairs': 1","'public_pairs': 2")
(h/'original-scope-verify.py').write_text(s)
files=['SourceCurrentNativeOriginalRequestScope.lean','original-scope-run-check.py','original-scope-capped-worker.py','original-scope-public.lean','original-scope-peaks-final.txt','original-scope-selection.json','original-scope-review.md','original-scope-source-pins.json','original-scope-verify.py','package.py']
for stem in ['original-scope-direct-1','original-scope-direct-2','original-scope-public-1']:
 files += [stem+x for x in ['.json','.limits.json','.usage.json','.source.lean','.log']]
(h/'original-scope-manifest.json').write_text(json.dumps({'schema':1,'files':[pin(h,p) for p in files],'sources':[pin(r,p) for p in paths]},indent=2)+'\n')
