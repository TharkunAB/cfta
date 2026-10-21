from pathlib import Path
import hashlib,json,shutil
p=Path(__file__).resolve().parent
root=Path('/home/tritlo/Code/mcfta')
prefix='positive-quotient-count'
sha=lambda b:hashlib.sha256(b).hexdigest()
plan=Path('/tmp/mcfta-older-owner-lineage-next-plan')
shutil.copytree(plan,p/'inputs'/'plan')
shutil.copyfile('/home/tritlo/Code/heavy-management/README.md',p/'inputs'/'heavy-management-README.md')
source=(p/'SourceCurrentPositiveQuotientCount.lean').read_bytes()
proposal=(p/'inputs/plan/proposed-geometry-signatures.lean.txt').read_text()
text=source.decode()
header=proposal[proposal.index('theorem child_count\n'):proposal.index('\n\nend MicroCFTA')]
assert header==text[text.index('theorem child_count\n'):text.index(' := by\n',text.index('theorem child_count\n'))]
shutil.copyfile(p/'source-proposal.json',p/'source-proposal-prelaunch.json')
comparison=json.loads((p/'source-proposal-prelaunch.json').read_text())
comparison.update(source_sha256=sha(source),source_lines=len(text.splitlines()),selected_source=True)
(p/'source-proposal.json').write_text(json.dumps(comparison,indent=2)+'\n')
readback=json.loads((p/'full-public-readback.json').read_text())
assert readback['source_sha256']==sha(source)
ledger=[]
for stem,kind in [(prefix+'-direct-1','strict'),(prefix+'-direct-2','strict'),(prefix+'-public-1','FULL')]:
 r=json.loads((p/(stem+'.json')).read_text())
 ledger.append({'name':stem,'kind':kind,'exit_code':r['exit_code'],'source_sha256':r['sha256'],'receipt':stem+'.json','raw_log':stem+'.log','usage':stem+'.usage.json','limits':stem+'.limits.json','actually_launched':True})
(p/'attempt-ledger.json').write_text(json.dumps({'actual_lean_jobs':3,'failed_jobs':1,'warning_jobs':0,'infrastructure_nonlaunches':0,'canonical_jobs':0,'runtime_jobs':0,'constructed_pairs':0,'attempts':ledger},indent=2)+'\n')
(p/(prefix+'-selection.json')).write_text(json.dumps({'finalized':True,'source':'SourceCurrentPositiveQuotientCount.lean','source_sha256':sha(source),'source_lines':195,'official_path':'lean/MicroCFTA/SourceCurrentPositiveQuotientCount.lean','selected_strict':prefix+'-direct-2','selected_public':prefix+'-public-1','groups':[{'name':h['head'],'pairs':1,'kind':'production','full_proof':True,'declaration_kind':h['kind']}for h in readback['heads']],'actual_axioms_by_head':{h['head']:h['actual_axioms']for h in readback['heads']},'actual_lean_jobs':3,'failed_jobs':1,'warning_jobs':0,'canonical_jobs':0,'constructed_pairs':0,'runtime_jobs':0,'all_eight_settings':True,'actual_type_identity':True,'no_new_runtime_back_or_rank_claim':True,'source_header_byte_exact_frozen_proposal':True},indent=2)+'\n')
(p/(prefix+'-report.md')).write_text('''# Positive quotient counts

Final source: SourceCurrentPositiveQuotientCount.lean,195lines. The public count identifies finite PositiveAt natural child paths under the inherited Rel classes. It deduplicates paths before it deduplicates quotient classes. Row choices and union alternatives do not add path indices. Mu bodies and references stay opaque.

The public child_count proves a weak bound for an arbitrary child with the explicit backwards relation. It proves a strict bound when the same selected source row is nonplain. The combined physical records must be coherent and fixed. They must cover the inherited classes. The inherited records need not be fixed, coherent, nonempty, or closed under positive paths. The caller supplies no enumeration or reflection law.

The source and target quotient types differ. One total injective relation maps positive child classes into positive parent classes with the parent root class erased. The actual public child_reflect theorem gives injectivity after coverage lifts the parent relation into the combined relation. A nonplain source row makes the parent root path positive, so erasure gives the strict bound. A functional representative map is not assumed.

The exact52-line enumeration/specification is copied from unchanged PositiveOwnerPair23–74. Both earlier enumerations are private. Local elementary symmetry, coverage, consistency, root-separation and setoid helpers follow the checked geometry proof. The source imports that geometry for child_reflect. It changes no existing declaration or source. source-proposal.json records exact public header comparison. The original prelaunch comparison remains source-proposal-prelaunch.json.

Root and guard read all195lines and both headers before the first check. Strict1 failed with one real elaboration error and no warnings: counted.trans attempted the unavailable Nat.le.trans field. The sole repair uses Nat.le_trans counted List.length_erase_le. Root and guard read the complete raw log and exact one-line patch before strict2. The original294ffba5 source remains the first immutable check input. The final7647bb4b source has the same public types and mathematical proof.

Selected strict2 passed with a literally empty raw log. The sole FULLpublic1 passed. check-full-public.py verified both complete check/print type pairs, unique actual lambda body delimiters, all eight settings, no omissions, and no private public TYPE identifiers. It read each actual axiom report separately. Both count(definition) and child_count(theorem) depend on propext, Classical.choice and Quot.sound. This was measured after the checks, not assumed for the definition.

The complete public output is232882bytes with SHA22b0afbb4b7ad65a21ad3341fa2114c08786e6e88ca0dd8f6efc6be45ce42aea. The printer SHA is a6d05223540a0f718f37e09f6da75632e01b28329da0b45cf5a2ab3317ab4144. Normalized public TYPE lengths are232 and6063characters. The complete bodies contain2608 and211226characters. No metadata parser retry was needed.

There are three actual Lean commands: strict1failed, strict2passed, FULL1passed. There are no warned checks, infrastructure nonlaunches, canonical jobs, runtime tests or constructed examples. Each job has its own immutable input, raw log, receipt, effective-limit record, and fresh usage record. All three usage records have age0seconds and46percent remaining. Each actual worker verified MemoryMax=MemoryHigh=4294967296bytes and memory.swap.max=0. The capped wrapper imposed five minutes. Peak records are132/139/158MiB in job order.

This component proves pure geometry. It does not produce the backwards relation from Parent work, transport that relation across an older-owner lineage, or prove outer completion. The separate source-only lineage plan remains frozen in inputs/plan. Its actual Back producer and later lexicographic rank contract remain open there. No actual native prefix, arbitrary ancestor exclusion, end-to-end runtime rank, or Haskell correspondence is claimed.

The author previously wrote PositiveOwnerPair and PositiveInheritedChildSeparation, plus the resource and positive-chronology foundations named in the plan. This component does not claim an independent review of those authored foundations. Guard independently reviewed the new source and one-line repair. Root separately owns installation, independent strict checking and Audit. None of those root jobs are included in this component's three author jobs.
''')
excluded={prefix+'-manifest.json',prefix+'-verification.json',prefix+'-live-verification.json'}
files=[]
for f in sorted(p.rglob('*')):
 if f.is_file() and f.name not in excluded:
  b=f.read_bytes();files.append({'path':str(f.relative_to(p)),'bytes':len(b),'sha256':sha(b)})
(p/(prefix+'-manifest.json')).write_text(json.dumps({'finalized':True,'source_sha256':sha(source),'actual_lean_jobs':3,'failed_jobs':1,'files':files},indent=2)+'\n')
print(json.dumps({'manifest_sha256':sha((p/(prefix+'-manifest.json')).read_bytes()),'selection_sha256':sha((p/(prefix+'-selection.json')).read_bytes()),'local_pins':len(files)}))
