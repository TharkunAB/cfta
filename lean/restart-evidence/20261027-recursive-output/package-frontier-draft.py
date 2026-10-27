from pathlib import Path
import hashlib,json
repo=Path('/home/tritlo/Code/mcfta');out=Path('/tmp/mcfta-recursive-output-20261027/frontier-draft')
def sha(b):return hashlib.sha256(b).hexdigest()
def write(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def dump(rel,o):write(rel,(json.dumps(o,ensure_ascii=False,indent=2)+'\n').encode())
selected={
'SourceFlatPruningRestart':[(19,44)],
'EnumerationFlatNativeIndex':[(88,98)],
'SourcePruningEnumerationNativeIndex':[(17,27)],
'SourcePruningEnumerationNodes':[(24,33)],
'EnumerationState':[(31,35),(244,248),(264,277)],
'MergedOrdinaryHeight':[(89,92)],
'SourcePruningEnumerationRendering':[(23,25),(142,155)],
'SourcePruningEnumerationObservation':[(20,26)],
'EnumerationFlatCached':[(14,32)],
'EnumerationFlatState':[(31,60)],
'EnumerationWaitingIndex':[(31,39),(55,57)],
'EnumerationCanonicalWaiting':[(17,21),(35,37)]}
sources=[];cuts=[]
for name,spans in selected.items():
 p=repo/'lean/MicroCFTA'/(name+'.lean');b=p.read_bytes();rel='inputs/'+p.name;write(rel,b)
 sources.append(dict(path=str(p),source=str(p),snapshot=rel,bytes=len(b),sha256=sha(b),role='actual defining source',read_scope='focused definitions/proofs as described in cuts'))
 for start,end in spans:
  lines=b.splitlines(keepends=True);assert 0<start<=end<=len(lines);part=b''.join(lines[start-1:end]);r=f'cuts/{name}-{start}-{end}.lean';write(r,part)
  cuts.append(dict(path=str(p),source=str(p),snapshot=r,start=start,end=end,bytes=len(part),sha256=sha(part),source_sha256=sha(b)))
report='''[2026-10-27 09:14 CET] SOURCE-ONLY DRAFT. Root owns compilation and adoption.

The new SourceFlatPruningOutputFrontier module separates three exact observations. A None decision requires an explicit rule, a nonempty complete native candidate list, and acceptance of every candidate. This list includes blocked candidates. A some.done decision is equivalent to an empty complete candidate list, for every stop rule and every ordering preference. A some.stuck decision requires a nonempty complete candidate list and an empty unblocked list, provided the stop rule did not accept. Invalid preferences still fall back to the first offered candidate.

The native frontier theorem uses the actual EnumerationFlatNativeIndex.Correct, including counter/list alignment and decoded expandable flags, plus Related and actual PendingRealized. Empty candidates are equivalent to every graph-bearing pending slot decoding to an available closed recursive-boundary value with an empty suspended bucket. No graph model is substituted for the native lookup. Correct.waiting is preserved in the premise but is not needed to classify candidate exhaustion: waiting removes candidates from offered work and never from the complete candidate list.

Pure equality slots with node=None are always noncandidates. They can retain nonempty suspended buckets even when no candidates remain. Thus the exact rendering Discharged predicate requires two additional slot conditions: there are no graph-bearing pending slots, and every pure equality pending bucket is empty. discharged_iff states this condition at the same related old/flat slot array. It does not assume or infer Safe, semantic acceptance, a global assignment, or successful rendering.

recursive_initial_counterexample constructs the literal initial single pending slot, false expandable function and empty waiting function. From an actual decoded available closed recursive boundary, it proves Related, genuine native Correct, PendingRealized and a done decision, while refuting Discharged. This is a conditional concrete family at any such actual native boundary. It does not certify an entire source allocation history or add a native execution claim. No native_decide, axiom or sorry is used.

The existing render_assignment theorem still needs Safe, Stratified, Discharged, actual successful rendering and checked rendered residuals. The new frontier classification supplies none of these independently. It identifies precisely which pending restrictions must be removed or treated by a separately proved recursive-marker semantics before that theorem applies. A marker produced for a retained recursive boundary is not evidence that the finite native language contains that marker.

The draft has complete proposed proofs but has not been compiled by this reviewer. It changes only this temporary bundle. All source inputs are copied whole and pinned. Cuts retain literal inclusive line ranges and parent hashes. The draft is separate from the previous frozen recursive-completion review. No repository edit, build, Git command or network call was made.
'''
write('report.txt',report.encode())
draft=out/'SourceFlatPruningOutputFrontier.lean'
dump('source-pins.json',dict(version=1,status='SOURCE-ONLY DRAFT; ROOT CHECK REQUIRED',draft=dict(path=str(draft),bytes=draft.stat().st_size,sha256=sha(draft.read_bytes())),sources=sources,cuts=cuts))
files=[]
for p in sorted(out.rglob('*')):
 if p.is_file():files.append(dict(path=str(p.relative_to(out)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())))
dump('pins.json',dict(version=1,pins=files,count=len(files)))
pp=(out/'pins.json').read_bytes();dump('FROZEN.json',dict(status='IMMUTABLE SOURCE-ONLY PROPOSAL',payload_count=len(files),file_count=len(files)+2,pins_sha256=sha(pp),pins_bytes=len(pp),source_count=len(sources),cut_count=len(cuts),cut_lines=sum(x['end']-x['start']+1 for x in cuts),draft_sha256=sha(draft.read_bytes()),report_sha256=sha((out/'report.txt').read_bytes())))
print((out/'FROZEN.json').read_text());print('FROZEN_SHA256',sha((out/'FROZEN.json').read_bytes()))
