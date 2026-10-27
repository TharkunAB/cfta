from pathlib import Path
import json,hashlib,datetime
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');base=Path('/tmp/mcfta-recursive-admission-20261027/recursive-history-next-proof')
assert not (base/'FROZEN.json').exists();(base/'cuts').mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest();now=datetime.datetime.now().astimezone().isoformat(timespec='seconds')
specs=[
 ('SourcePruningEnumerationFiniteContract.lean',[(28,48)]),
 ('SourcePruningEnumerationOutputHistory.lean',[(27,70)]),
 ('SourcePruningEnumerationFiniteCallbackResources.lean',[(94,116)]),
 ('SourcePruningEnumerationFiniteCallbackReceiptLanguage.lean',[(41,71)]),
 ('SourcePruningEnumerationHeadAdmission.lean',[(71,102)]),
 ('SourcePruningEnumerationFiniteHeadResources.lean',[(100,162)]),
 ('SourcePruningEnumerationFiniteReceiptResources.lean',[(76,90)]),
 ('SourcePruningEnumerationInvocationReceipts.lean',[(93,125),(138,173)]),
 ('SourcePruningEnumerationFiniteSiblingResources.lean',[(100,179)]),
 ('SourcePruningEnumerationFiniteReservation.lean',[(179,208)]),
 ('SourcePruningEnumerationFiniteParkedResources.lean',[(90,115)]),
 ('SourcePruningEnumerationFiniteExpansionResources.lean',[(117,152)]),
 ('SourcePruningEnumerationRecursivePacket.lean',[(21,60)]),
]
records=[]
for name,cuts in specs:
 p=repo/name;b=p.read_bytes();rec={'source':str(p),'scope':'whole source identity only; snapshots are literal cuts','bytes':len(b),'sha256':sha(b),'reviewed_scope':'listed literal cuts','cuts':[]}
 for f,l in cuts:
  cut=b''.join(b.splitlines(keepends=True)[f-1:l]);q=base/'cuts'/f'{name}.{f}-{l}.txt';q.write_bytes(cut)
  rec['cuts'].append({'scope':'literal cut','first_line':f,'last_line':l,'snapshot':str(q),'bytes':len(cut),'sha256':sha(cut)})
 records.append(rec)
(base/'source-index.json').write_text(json.dumps({'created':now,'cut_convention':'One-based inclusive lines, splitlines(keepends=True), trailing LF preserved. No whole-source snapshot is claimed by a cut record.','sources':records},indent=2)+'\n')
report=f'''[{now}] Source-grounded next-proof plan. No completion or semantic closure is claimed.

Result. The missing resource information is local and available during the existing finite proof. It is not recoverable from a bare OutputHistory, CompletedHeadReceipt or FalseCallbackReceipt alone. The smallest first step is to retain the actual smaller-depth restart admission before the finite callback drops it, then pass a stronger uniform induction contract through callback, head and sibling completion. The separate callback-admission-draft now proposes this first data export. It is uncompiled at this report's creation.

1. Exact required restart input.
For each actual false callback, retain inventory, actual Caller, FULL Memos, updated metadata, actual framed cache, recursive depth, the original callback seed s and mass ceiling C. The data are:
Packet formulas solver inventory caller memos updated framedCache;
Fits s.2 caller.checked;
Heap (membership in s.1) caller.nativeHeap;
suspendedBound framedCache.core ≤ C;
FiniteReservation.Reserved bits depth s C.
The global selector membership and length policies remain the fixed outer Complete inputs. They need not be duplicated in every receipt. The callback input also requires its actual target/fragment and FragmentBound before.counter fragment. Frame.counter transports that same fragment bound; the recursive run itself does not consume fragment or target as extra admission.
The full Memos must be the witness of the actual head Post. Equality of its query field with returned queries does not determine the remaining memo fields.

2. What current exports retain and omit.
FiniteContract.Complete (28–48) has exactly the required initial resource data, but concludes only a stable actual outcome and OutcomeResources. RecursivePacket (21–35) supplies native Context/full Memos, Safe, PendingReferences, CacheValid, dependency order and allocated metadata pending IDs. It does not imply arbitrary numeric Fits, alphabet membership, a mass ceiling or a finite reservation.
OutputHistory (27–70) records literal selected-prefix, ordinary invocation and callback singleton equations. Its tags carry no Inventory, full Memos, Packet, seed, ceiling or reservation. Its zero tags are operational paths; they do not establish discharge or semantic truth.
FalseCallbackReceipt (41–71) already fixes the actual updated metadata/core/framed cache, original and returned Packets, exact callback singleton and concrete same-fuel continuation/restart. It does not retain seed, ceiling, Fits/Heap, mass or reservation.
CompletedHeadReceipt (71–102) retains actual head input/return full Memos, Post, input and completed Packets, afterHead Fits/Heap, actual projection/arity and stable captured completion. It omits capturedMass, HeadCacheBounds and the callback half of HeadReserved. Its local edge reservation does not imply that callback half.
InvocationReceipts (93–101) discards _cacheBounds/_headFits/_headKnown and later returns only CompletedHeadReceipt. Thus an existing rich invocation certificate alone does not recover the omitted callback reservation or mass ceiling.

3. All required callback data already exist at the genuine producer.
FiniteHeadResources (100–143) derives edge width/projection bounds from the original Packet, Fits and guard Heap, then bounds actual edgeCost and takes the original reserved.edge prefix. Its actual head producer returns Admitted/Pending/FragmentHistory/HeadCacheBounds/full Post/Memos and head Fits/Heap. head_mass_le derives the actual completed cache mass from HeadCacheBounds and original capturedMass/inherited bounds.
At the actual completed head, choose callbackSeed = RecursiveReservation.afterHead localSeed inherited, callbackCeiling = RecursiveReservation.massCeil localSeed capturedMass inherited. FiniteReservation.HeadReserved (191–194) already contains Reserved bits depth callbackSeed callbackCeiling as its second component. No post-run reservation construction is needed.
FiniteReceiptResources (76–89) derives the input Packet at the SAME completed cache and reached native Caller from Admitted/history/pending and the original ordered metadata packet, then calls the callback producer with its actual full final Memos. These are the correct restart witnesses.
FiniteCallbackResources (94–100) derives massAfter by exact Frame.values and calls the smaller-depth IH with the SAME original seed/ceiling/Fits/Heap/reservation, plus the actual updated returned Packet. The new admission export should retain exactly this call data.

4. Preserve full sibling context.
After a completed recursive hook, use its actual OutcomeResources plus the original captured Packet to recover full Post, actual post-hook Caller/Memos and Packet for the SAME captured sibling cache. The next sibling uses that Caller/full Memos, not the head completion Caller or an output's own cache. FiniteSiblingResources (133–141) already does this and advances to FiniteReservation.step depth seed B L with reserved.tail. Individual recursive outputs retain their own caches and native heaps. Aggregate scan Post composes original scan Caller to each local head input; it does not equate earlier output caches with the captured sibling cache.

5. The quantifier/bound blocker.
An old Complete witness b only controls run(b+extra). A separately derived richer witness r need not satisfy r≤b. It is invalid to enrich EVERY old-adequate execution merely by invoking a theorem that starts at r. No such inequality follows from Complete.
The stronger contract must choose its common work bound BEFORE the universal larger-fuel execution and output membership. Preserve the old stable outcome/resource fields, then append:
∀ extra, ∀ output ∈ hookOutputs outcome, ∃actualHistory, OutputHistory at workFuel(bound+extra) ... output ∧ a resource decoration for its actual operation tags.
A resource decoration supplies the original operation admission and exact full endpoints; it contains no desired Satisfies statement or future successful action as initial input. Existence of one admitted actual path per emitted output is sufficient. There is no need to claim admission for every arbitrary proof of the unrestricted raw OutputHistory predicate.

6. Smallest next interfaces and implementation order.
A. CallbackAdmission: the present temp proposal introduces RecursiveCallbackAdmission and transports it through an actual FalseCallbackReceipt using returned Packet plus Frame.counter/values. A new head wrapper retains the entire prior head-with-receipt packet and appends actual-complete→that admission. The final old universal field requires parentheses before the new conjunction; its field body remains exact.
B. FiniteHistoryContract: copy the original Complete universal inputs unchanged, keep its stable run and full OutcomeResources, and append the actual resource-decorated output history family at the SAME chosen bound. A forget theorem returns old Complete with that SAME bound/outcome, not an independently chosen one.
C. FiniteCallbackHistory: consume this stronger smaller-depth contract. Retain the entire callback packet and its actual false restart admission. Choose the callback stable state first, invoke the richer IH at that actual framed state, and enlarge the common callback bound to cover both recording and richer resume. Return actual output paths using the richer IH family at the resulting work fuel. The true callback emits no outputs and requires no fabricated tail certificate.
D. FiniteHead/InvocationHistory: retain the actual head packet and callback admission, use the stronger callback result, then induct the sibling list at the actual post-hook Caller/full Memos and same captured cache. Carry head/callback/tail bounds explicitly. Preserve unsupported and rejected paths and stopped-hook outputs.
E. Positive selected/parked route, then depth induction: retain actual PrefixValid/full prefix Post/metadata and resource admission at the narrowed input. Reuse the exact original narrowing and mass argument. Apply the strengthened ordinary/sibling producer or the genuine parked smaller-depth admission. Assemble the original run contract and rich paths at a common bound, then perform the existing finite depth induction.

7. Concrete bound alignment method.
If wrapping an unchanged old producer, choose b for the retained packet and r for the richer local route; set W=b+r (or max b r). At every extra, specialize oldRunning with W+extra-b and richerRunning with W+extra-r, prove both equalities arithmetically, and compare the SAME deterministic actual runtime at W+extra. This identifies the old and rich outcomes without a future-observation input. Rebase every exported stable head/callback family to W. Do not keep a field indexed by W while silently using a proof only indexed by b. Existing FiniteCallbackResources (101–115), FiniteSiblingResources (142–179), and InvocationReceipts (126 onward) show the explicit common-bound pattern. A producer proof can instead be structurally strengthened to call the richer IH once and reconstruct all original fields, avoiding a duplicate IH instantiation. Either route must retain full old contracts.

8. The parked route is separate.
FiniteParkedResources (90–114) pads the original seed through narrowSeed then afterHead, bounds the checked cache mass by the original ceiling and massCeil, and consumes reserved.first.2. It has no executed captured edge. Retain these exact planned seed/ceiling witnesses and same original Caller/full Memos with the checked Packet. Do not pretend the synthetic padding denotes an actual edge execution. A .stuck restart emits no outputs. For a nonblocked parked restart, apply the richer IH at its actual decision and checked cache.

9. Semantic closure is not supplied by this resource step.
After resource histories exist, an interpreter can consume the current explicit Canonical/fresh-arity/retention gates and local prefix/captured/callback assignment laws. These gates are not added to the resource producer's initial admission. Parked clearing still requires its exact lost suspended Holds obligation or a genuine discharge condition. Ancestry alone does not restore it. Canonical storage does not imply acceptance, Frame does not imply Safe, and a stopped output path is not a whole discharged-output language theorem.

No builds, repository edits, Git/network actions or prior frozen bundle changes were made. This plan pins focused cuts only; it does not duplicate the old module archive or claim whole-source review for the cut records.
'''
(base/'report.txt').write_text(report)
(base/'interfaces.txt').write_text('''DESIGN ONLY — no Lean declaration in this file has been compiled.

Stronger finite contract shape, with ALL original Complete inputs:
  originalAdmission → ∃ bound outcome,
    (∀extra, oldRun(bound+extra,depth,actualInput)=outcome) ∧
    OutcomeResources originalCaller(final depth seed ceiling) outcome ∧
    (∀extra output, output∈hookOutputs outcome →
      ∃ history, OutputHistory(workFuel=bound+extra, actual original input, output) ∧
        operation-by-operation resource evidence for that SAME history).

Resource evidence for each false callback tail input:
  ∃inventory fullMemos callbackSeed callbackCeiling,
    fullMemos.query=actualSavedQueries ∧
    Packet inventory actualReachedCaller fullMemos actualUpdatedMetadata actualFramedCache ∧
    Fits callbackSeed.profile actualReachedCaller ∧ Heap callbackSeed.alpha actualReachedHeap ∧
    suspendedBound actualFramedCache≤callbackCeiling ∧
    FiniteReservation.Reserved bits smallerDepth callbackSeed callbackCeiling.
  PLUS exact actual callback singleton, local recording/frame receipt,
  and the smaller-depth history at the SAME parent workFuel.

Actual head provenance:
  callbackSeed = afterHead localHeadSeed inherited;
  callbackCeiling = massCeil localHeadSeed capturedMass inherited;
  callbackReserved = original local HeadReserved second component;
  fullMemos = actual head Post's complete returned Memos witness.

No Satisfies, desired history, future Success or final resource premise is an
initial producer input. Global selector policies remain unchanged outer inputs.
''')
for rec in records:
 b=Path(rec['source']).read_bytes();assert sha(b)==rec['sha256']
 for c in rec['cuts']:
  cut=b''.join(b.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert cut==Path(c['snapshot']).read_bytes() and sha(cut)==c['sha256']
files=sorted(p for p in base.rglob('*') if p.is_file() and p.name not in ['pins.json','FROZEN.json'])
pins={'created':now,'files':{str(p.relative_to(base)):{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in files}}
(base/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
frozen={'created':now,'status':'FROZEN / source-grounded plan only','payload_count':len(files),'exact_file_count':len(files)+2,'pins_sha256':sha((base/'pins.json').read_bytes()),'report_sha256':sha((base/'report.txt').read_bytes()),'source_index_sha256':sha((base/'source-index.json').read_bytes())}
(base/'FROZEN.json').write_text(json.dumps(frozen,indent=2)+'\n')
for rel,r in pins['files'].items():b=(base/rel).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
print(json.dumps({'area':str(base),'payload_count':len(files),'exact_file_count':len(files)+2,'FROZEN_sha256':sha((base/'FROZEN.json').read_bytes()),**{k:frozen[k] for k in ['pins_sha256','report_sha256','source_index_sha256']}},indent=2))
