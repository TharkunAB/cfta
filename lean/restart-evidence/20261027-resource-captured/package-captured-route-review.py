from pathlib import Path
import hashlib,json,re,datetime
repo=Path('/home/tritlo/Code/mcfta');out=Path('/tmp/mcfta-resource-captured-20261027/captured-route-review')
def sha(b):return hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def dump(rel,o):put(rel,(json.dumps(o,indent=2,ensure_ascii=False)+'\n').encode())
selected={
'SourcePruningEnumerationSelectedEdgeStableNeutral':'stable_complete_neutral_semantics',
'SourcePruningEnumerationSelectedEdgeNeutralSoundness':'stable_complete_neutral_sound_current',
'SourcePruningEnumerationSelectedEdgeSoundness':'stable_complete_sound',
'SourcePruningEnumerationCapturedEdgeSoundness':'stable_complete_sound_current',
'SourcePruningEnumerationSelectedEdgeResources':'complete_with_fragments_resources',
'SourcePruningEnumerationCapturedEdgeResources':'complete_with_history_resources'}
sources=[];cuts=[];imports=[]
for name,decl in selected.items():
 p=repo/'lean/MicroCFTA'/(name+'.lean');b=p.read_bytes();rel='inputs/'+p.name;put(rel,b)
 sources.append(dict(path=str(p),source=str(p),snapshot=rel,sha256=sha(b),bytes=len(b),lines=len(b.splitlines()),read_scope='whole relevant declaration and proof; projection tails inspected'))
 lines=b.splitlines(keepends=True);start=next(i for i,x in enumerate(lines) if x.startswith(('theorem '+decl+'\n').encode()));end=start
 while b':=' not in lines[end]:end+=1
 part=b''.join(lines[start:end+1]);r=f'cuts/{name}--{decl}.lean';put(r,part)
 cuts.append(dict(path=str(p),source=str(p),snapshot=r,start=start+1,end=end+1,source_sha256=sha(b),bytes=len(part),sha256=sha(part)))
 for i,line in enumerate(lines,1):
  if line.startswith(b'import '):imports.append(dict(source=str(p),line=i,literal=line.decode().rstrip('\n'),target=line.decode().strip().split()[1]))
for name,start,end,label in [('SourcePruningEnumerationSelectedEdgeStableNeutral',87,103,'old-numeric-bridge-and-producer'),('SourcePruningEnumerationCapturedEdgeSoundness',90,116,'stored-bucket-and-selected-producer'),('SourcePruningEnumerationCapturedEdgeSoundness',137,165,'neutral-finalize-restoration')]:
 p=repo/'lean/MicroCFTA'/(name+'.lean');b=p.read_bytes();part=b''.join(b.splitlines(keepends=True)[start-1:end]);rel=f'cuts/{name}--{label}.lean';put(rel,part)
 cuts.append(dict(path=str(p),source=str(p),snapshot=rel,start=start,end=end,source_sha256=sha(b),bytes=len(part),sha256=sha(part)))
def conclusion(text,marker):return text[text.index(marker):text.index(' := by',text.index(marker))]
oldStable=(repo/'lean/MicroCFTA/SourcePruningEnumerationSelectedEdgeStableNeutral.lean').read_text();newStable=(out/'drafts/SourcePruningEnumerationSelectedEdgeStableResourceNeutral.lean').read_text()
oldSound=(repo/'lean/MicroCFTA/SourcePruningEnumerationSelectedEdgeNeutralSoundness.lean').read_text();newSound=(out/'drafts/SourcePruningEnumerationSelectedEdgeNeutralResourceSoundness.lean').read_text()
retention=dict(stable_conclusion_exact=conclusion(oldStable,'    ∃ childFragments : List Fragment,')==conclusion(newStable,'    ∃ childFragments : List Fragment,'),sound_conclusion_exact=conclusion(oldSound,'    ∀ (held : Nat), held < before.core.counter')==conclusion(newSound,'    ∀ (held : Nat), held < before.core.counter'),no_ranges_bridge='ranges' not in newStable and 'numeric' not in newStable and 'ranges' not in newSound,semantic_gates_retained=all(x in newSound for x in ['(inheritedValid : EnumerationSemantics.ValidSuspended scs)','(nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)','(freshArity : arityAllows edge.children.length (suspendedVars before.core.counter tries) = true)','(retained : ∀ incoming bucket,']),own_producer_calls=newStable.count('SourcePruningEnumerationEdgeInputs.complete '),traversal_resource_producer_calls=newStable.count('SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources_semantics\n'),neutral_resource_observer_calls=newStable.count('SourcePruningEnumerationTraversalCompletion.stable_complete_neutral_semantics_resources\n'))
assert all(retention[x] for x in ['stable_conclusion_exact','sound_conclusion_exact','no_ranges_bridge','semantic_gates_retained'])
assert retention['own_producer_calls']==retention['traversal_resource_producer_calls']==retention['neutral_resource_observer_calls']==1
dump('retention.json',retention)
report='''[2026-10-27 10:14 CET] SOURCE-ONLY PROPOSAL. Root owns compilation and adoption.

The smallest exact route is resource-neutral traversal, resource-neutral selected edge, unchanged pure selected-edge acceptance, then actual captured finalization. Ordinary selected-edge semantics alone is insufficient: the held captured slot still contains its original pending payload until finalization. Applying nonneutral completion would require this stale payload at the wrong phase. The existing neutral route removes only that held slot and restores it with the actual written fragment equation.

Two full theorem drafts are included. SelectedEdgeStableResourceNeutral.stable_complete_neutral_semantics_resources retains the entire old stable neutral conclusion. It specializes width to bits+2, adds seed first, and replaces the old Ranges input with current Fits, Reserved bits seed (SelectedEdge.cost edge scs before.counter tries), and the original heap guard carrier. The own producer supplies the actual ordered child inputs and Protected/childAvoids. It changes no native Caller, so the original Fits and guard carrier are still at the actual traversal entry. The reservation cost is definitionally TraversalCompletion.cost of those exact inputs. Duplicate occurrences and recorded order remain intact.

The draft invokes the full traversal resource/semantics producer once. Its output order is the entire old packet, returned Fits, returned carrier, then childMeaning. Common representative/native sums and maxima for p/h align the actual completed selected-edge family with that producer. The full cache, actual Caller, Queries and fragment are identified by the literal Result constructor. It does not infer full Memos equality from Queries. Own suspension neutral semantics and residual finish neutral semantics then compose the exact iff. The old universal numeric bridge is removed. The new traversal neutral resource observer uses the actual same completed traversal receipt; it is not an initial promise of future success.

SelectedEdgeNeutralResourceSoundness.stable_complete_neutral_sound_current_resources keeps the entire old backward acceptance conclusion. The pure projection, child evidence and restriction proof is unchanged. Current Context derives the annotation heap; no extra annotation premise is introduced. inheritedValid, nonterminal, freshArity and retained remain explicit semantic gates. The resource premises supply numeric admission, not these semantic gates. The observed stable complete family is an actual execution receipt. Its final Satisfies premise is under the returned implication, not an admission premise of the resource producer.

The next CapturedEdge.stable_complete_sound_current_resources can copy the reviewed old captured proof. Replace its Ranges input with the same seed/Fits/reservation/carrier. Use SelectedEdge.complete_with_fragments_resources once, destruct its two final resource fields, and call the new resource-neutral soundness consumer. Keep actual Finalize.complete once and the common-fuel constructor alignment. Protected supplies the same captured pending slot in the actual middle cache. Finalize.written_semantics gives neutral-middle Satisfies plus fill(fragment)=assignment uv. Neutral selected soundness and handles_lookup restore the original pending native restriction and all its suspended constraints. Neutralize_restore then gives the exact original before-state Satisfies, edge/parent acceptance, suspended Holds and final fragment equation. No universal Ranges or second existential captured producer is needed.

Canonical before.core remains necessary in that captured consumer: the actual stored pending bucket derives inheritedValid by canonical applied to the stored slot. Ready supplies Safe, allocation, rootness and Avoids, but not Canonical. nonterminal must be supplied or derived from an actual ordinary-route classifier. Fresh own arity is not a consequence of Fits, current cache realization or normalized guard annotations. Retention requires each actual child to be ordinary, its bucket to contain a terminal trie, or its bucket to be empty; otherwise existing child execution intentionally drops that nonterminal bucket. These are exact existing gates, not newly derived histories. Checked-constructor arity histories and global canonical-history transport are outside this six-file review.

Rejection remains separate. The resource producers can return valid raw[] stopping receipts with their actual cache and native effects. The stable complete observer excludes that branch by constructor equality at common adequate bounds. It neither promotes raw[] to an accepted fragment nor exports Safe on arbitrary rejection.

The six reviewed sources are copied whole with literal declaration and proof cuts. The drafts have no runtime definitions, new datatype, helper predicate, Graph relation, future semantic fact, sorry or native_decide. They have not been compiled by this reviewer. Planned new traversal modules and imported pure lemmas are listed as unreviewed dependencies. All earlier checkpoint areas remain untouched. No repository edit, build, Git command or network call was made.
'''
put('report.txt',report.encode())
planned=[dict(module='MicroCFTA.SourcePruningEnumerationTraversalResourceLanguage',api='TraversalCompletion.complete_with_fragments_resources_semantics seed, old arguments, fits reserved known; old packet then returnedFits returnedKnown childMeaning',status='Required confirmed draft API; source not reviewed in this bounded bundle'),dict(module='MicroCFTA.SourcePruningEnumerationTraversalStableResourceNeutral',api='TraversalCompletion.stable_complete_neutral_semantics_resources seed, old arguments, fits reserved known, actual stable family',status='Root announced API; source not reviewed in this bounded bundle')]
input_names={'MicroCFTA.'+x for x in selected}
unreviewed=sorted(set(x['target'] for x in imports if x['target'] not in input_names))
drafts=[]
for p in sorted((out/'drafts').glob('*.lean')):
 b=p.read_bytes();drafts.append(dict(path=str(p),snapshot=str(p.relative_to(out)),bytes=len(b),lines=len(b.splitlines()),sha256=sha(b)))
dump('source-pins.json',dict(version=1,status='IMMUTABLE SOURCE-ONLY PROPOSAL; ROOT CHECK REQUIRED',sources=sources,cuts=cuts,drafts=drafts,literal_imports=imports,unreviewed_imported_dependencies=unreviewed,planned_unreviewed_dependencies=planned,retention='retention.json'))
entries=[]
for p in sorted(out.rglob('*')):
 if p.is_file():entries.append(dict(path=str(p.relative_to(out)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())))
dump('pins.json',dict(version=1,count=len(entries),pins=entries))
b=(out/'pins.json').read_bytes();dump('FROZEN.json',dict(status='IMMUTABLE SOURCE-ONLY PROPOSAL',payload_count=len(entries),file_count=len(entries)+2,pins_sha256=sha(b),pins_bytes=len(b),report_sha256=sha((out/'report.txt').read_bytes()),source_pins_sha256=sha((out/'source-pins.json').read_bytes()),sources=len(sources),cuts=len(cuts),cut_lines=sum(x['end']-x['start']+1 for x in cuts),drafts=len(drafts),draft_lines=sum(x['lines'] for x in drafts)))
print((out/'FROZEN.json').read_text());print('FROZEN_SHA256',sha((out/'FROZEN.json').read_bytes()))
