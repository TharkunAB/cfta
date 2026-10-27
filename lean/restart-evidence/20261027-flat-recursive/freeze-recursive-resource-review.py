from pathlib import Path
import hashlib,json,datetime
repo=Path('/home/tritlo/Code/mcfta');out=Path('/tmp/mcfta-flat-recursive-20261027/recursive-resource-review')
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(p,b):p=out/p;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def js(p,x):put(p,(json.dumps(x,indent=2)+'\n').encode())
selections={
'SourcePruningEnumerationFiniteContract':[(28,49,'universal original Complete contract')],
'SourcePruningEnumerationFiniteResources':[(28,50,'depth induction discharges the smaller-depth contract')],
'SourcePruningEnumerationFiniteRunStep':[(28,78,'actual positive-depth driver and non-expansion routes')],
'SourcePruningEnumerationFiniteHeadResources':[(68,98,'exact head endpoint resources and hook outcome'),(134,162,'receipt admission and completed subtree endpoint')],
'SourcePruningEnumerationFiniteReceiptResources':[(70,90,'actual completed receipt derives current recursive Packet')],
'SourcePruningEnumerationFiniteCallbackResources':[(77,115,'callback rejection and same-mass accepted recursion')],
'SourcePruningEnumerationFiniteSiblingResources':[(130,162,'suffix uses actual hook caller and full memos'),(200,229,'stopped callback outputs and optional endpoint')],
'SourcePruningEnumerationFiniteExpansionResources':[(112,144,'actual narrowed prefix admission and original ordinary reservation')],
'SourcePruningEnumerationRecursivePacket':[(21,47,'Packet and captured Post transport'),(63,80,'receipt packet from actual context and histories')],
'SourcePruningEnumerationRecursiveCallback':[(29,60,'single original callback producer with exact generic equation')],
'SourcePruningEnumerationSubtreeEffects':[(30,43,'completed subtree full Post/memos/captured cache transport')],
'SourcePruningEnumerationSuspendedMass':[(89,95,'exact stored-values mass preservation')],
'SourceFlatPruningChildCompletion':[(142,164,'public actual stable old child observer without Ranges')],
'SourcePruningEnumerationChildResources':[(29,64,'original child resource admission and actual endpoint')],
'SourceFlatPruningTraversalCompletion':[(154,173,'existing ranged traversal tail induction to replace')],
'SourceFlatPruningCapturedCompletion':[(81,109,'current flat captured admission still uses old Ranges')],
'SourceFlatPruningCallbackCompletion':[(42,49,'semantic callback wrapper has extra Canonical premise')],
'SourceFlatPruningOracle':[(101,115,'full actual callback successful replay')],
'SourceFlatPruningContinuation':[(45,67,'generic actual flat continuation singleton equation')],
'EnumerationFlatNativeIndex':[(103,122,'index correctness from full related cache and old native invariants')]
}
sources=[];cuts=[]
for name,regions in selections.items():
 p=repo/'lean/MicroCFTA'/f'{name}.lean';b=p.read_bytes();ls=b.splitlines(keepends=True);dest=f'inputs/{name}.lean';put(dest,b);sources.append(dict(path=str(p),source=str(p),snapshot=dest,bytes=len(b),sha256=sha(b),lines=len(ls),read_scope='focused source cuts and surrounding producer proof reviewed; whole file pinned for identity'))
 for start,end,meaning in regions:
  end=min(end,len(ls));assert 1<=start<=end<=len(ls),(name,len(ls),end)
  data=b''.join(ls[start-1:end]);dest=f'cuts/{name}-{start}-{end}.lean';put(dest,data);cuts.append(dict(path=str(p),source=str(p),source_sha256=sha(b),start=start,end=end,inclusive=True,snapshot=dest,bytes=len(data),sha256=sha(data),meaning=meaning))
report='''FINAL SOURCE PLAN AND PROOF DRAFT. No build was run by this reviewer. The draft is an original-input admission helper, not a claim that full flat finite-depth completion is already proved.

The exact old induction is a suitable basis. FiniteContract.Complete quantifies inventory, current Caller, full Memos, cache, metadata, seed and an original mass ceiling. Its inputs are Packet, Fits, current guard carrier, selector membership/length laws, mass bound and the original finite reservation. FiniteResources.finite_complete discharges the smaller-depth Complete premise by depth induction. No future successful call or post-hook Ranges is an input to that public theorem. The flat extension should retain this old packet and append actual flat execution related to that SAME old outcome. Bounds should precede the related flat cache. Preserve the option to return an existential actual flat endpoint for each adequate run; do not assume one literal flat forest across all bounds.

The endpoint sequence is explicit. FiniteHeadResources.head_finite_complete_resources supplies an actual captured receipt, full head Post/Memos, Admitted, Pending, FragmentHistory, cache bounds and Fits/carrier at afterHead. FiniteReceiptResources.receipt_finite_complete_resources uses receipt_packet to derive the callback Packet at the receipt's own cache and caller. FiniteCallbackResources.callback_finite_complete_resources calls callback_complete once. Frame.values preserves suspendedBound, so the same ceiling and reservation admit the smaller-depth driver after the callback. The true callback result prunes the branch; it is not a successful-recursion hypothesis. The false result executes the actual recursive driver.

The first concrete proof draft is drafts/SourceFlatPruningRecursiveAdmission.lean. callback_entry calls callback_complete ONCE and retains its ENTIRE original output: returned Packet, RenderStable, Frame, metadata equations, all larger-fuel Success/exact raw singleton and generic original continueWith equation. It adds the preserved mass ceiling, current Fits/carrier, actual successful flat callback replay, framed cache Related, index correctness at the same native caller, restart equality and a generic exact flat continueWith equation. It needs no Canonical input. The existing semantic callback wrapper does require Canonical; that stronger wrapper is unnecessary for resource-only replay. No actual flat observation or desired final resource fact is an input to callback_entry. Its flat endpoint is existential for each actual larger callback fuel.

The second drafted theorem, completed_subtree, consumes the actual smaller-depth OutcomeResources for a completed subtree. completed_captured_packet gives its literal reached Caller, full final Memos and Post, the restored original captured Packet, Fits/carrier and all own-output certificates. Correct transfers to the SAME captured flat cache at that reached heap through full Cached.Related. The theorem preserves every output certificate. It does not exchange an output's own cache for the captured sibling cache. It does not infer memo equality from query equality or assert Safe for a rejection. This directly supplies the next-sibling resource gate after an actual subtree.

There is one lower-level completion lift to retain. Existing flat Captured/Selected/Traversal producers accept old Ranges. Original resource completion does not automatically export that universal future-state proposition. The public SourceFlatPruningChildCompletion.observed bypasses it: genuine current Safe/Roots/counts/realized/bucket bounds/InputsPending and a stable actual old child family in representative/index fuels give the actual flat child relation at fixed native/p/h. Lift ChildCompletion.complete_with_fragments_resources once through this observer. Then adapt the resource traversal induction, followed by existing pure own-prefix/residual/finalization replay. Do not assume post-hook Ranges. Root reported that the child resource lift and this admission draft passed first strict checks while this report was prepared; this bundle pins source inputs and the immutable draft, not those independently owned compiler reports.

For the full sibling induction, reuse FiniteSiblingResources: the suffix starts at hookCaller/hookMemos under hookPost, not the head endpoint. Its captured cache stays fixed. ScanReserved.tail pays that same planned seed. Receipt and output schedules remain distinct. Stops retain arbitrary output prefixes, nested reasons and absent endpoints. FiniteExpansionResources supplies actual narrowed-prefix admission; parked, Empty and fallback routes still require their exact operational relations. These lifts must be attached to the actual flat recursive worker before a global flat finite-depth theorem is claimed. Language soundness, coverage, initial histories and unbounded convergence remain separate. H6 is unchanged.
'''
put('report.txt',report.encode());js('source-pins.json',dict(version=1,status='FINAL SOURCE PLAN',sources=sources,cuts=cuts,draft='drafts/SourceFlatPruningRecursiveAdmission.lean',scope='No repo edits, Lean/native builds, Git or network by reviewer'))
for row in sources:
 assert Path(row['source']).read_bytes()==(out/row['snapshot']).read_bytes()
for row in cuts:
 b=Path(row['source']).read_bytes();assert sha(b)==row['source_sha256'];assert b''.join(b.splitlines(keepends=True)[row['start']-1:row['end']])==(out/row['snapshot']).read_bytes()
# Do not include the packaging helper in the immutable proof/source payload.
files=sorted(p for p in out.rglob('*') if p.is_file() and p.name!='freeze.py');payloads=[dict(path=str(p.relative_to(out)),bytes=len(p.read_bytes()),sha256=sha(p.read_bytes())) for p in files];js('pins.json',dict(version=1,files=payloads));b=(out/'pins.json').read_bytes();js('FROZEN.json',dict(version=1,status='FINAL SOURCE PLAN',payload_count=len(payloads),exact_payload_files=len(payloads)+2,source_count=len(sources),cut_count=len(cuts),cut_lines=sum(r['end']-r['start']+1 for r in cuts),pins_sha256=sha(b),report_sha256=sha((out/'report.txt').read_bytes()),draft_sha256=sha((out/'drafts/SourceFlatPruningRecursiveAdmission.lean').read_bytes())))
for p in out.rglob('*'):
 if p.is_file() and p.name!='freeze.py':p.chmod(0o444)
print(json.dumps(dict(path=str(out),report_sha256=sha((out/'report.txt').read_bytes()),source_pins_sha256=sha((out/'source-pins.json').read_bytes()),frozen_sha256=sha((out/'FROZEN.json').read_bytes()),controls=json.loads((out/'FROZEN.json').read_text())),indent=2))
