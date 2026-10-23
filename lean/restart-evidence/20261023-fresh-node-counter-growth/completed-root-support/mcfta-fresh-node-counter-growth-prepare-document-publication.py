exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import datetime,difflib
previous=ROOT/'lean/restart-evidence/20261023-pair-inventory-rebase'
actual=load(HERE/'actual-proof-cut.json')
assert actual['metrics']==dict(actual_jobs=5,source_jobs=4,focused_build_jobs=0,audit_jobs=1,failed_jobs=1,warned_source_exit_zero_jobs=1,rejected_public_type_jobs=0)
assert actual['audit']['build_jobs']==3652 and actual['audit']['dependencies']==75541
assert actual['audit']['log_sha256']==sha(HERE/'audit1.log')=='f5d1bbe1ff0b0e8bafc4c54678f17c0bc1ab259d7541b86d273353a6ef735bb3'
def replace_one(text,before,after):
    assert text.count(before)==1,before
    return text.replace(before,after,1)
def retain(owner,name,basis,selected):
    (owner/name).write_text(selected)
    (owner/(name+'.basis.txt')).write_text(basis)
    (owner/(name+'.patch')).write_text(''.join(difflib.unified_diff(basis.splitlines(True),selected.splitlines(True),fromfile='H32/'+name,tofile='H33/'+name)))
    (owner/(name+'.inverse.patch')).write_text(''.join(difflib.unified_diff(selected.splitlines(True),basis.splitlines(True),fromfile='H33/'+name,tofile='H32/'+name)))
def freeze(owner,names):
    pins=[dict(path=p.name,bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(owner.iterdir()) if p.is_file()]
    (owner/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
    (owner/'FROZEN.json').write_text(json.dumps(dict(status='FINAL_FROZEN_REVIEW_REQUIRED',
        observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),pins_count=len(pins),pins_sha256=sha(owner/'pins.json'),
        selected_lines={name:len((owner/name).read_bytes().splitlines()) for name in names}),indent=2)+'\n')
    print(json.dumps(dict(owner=str(owner),pins_sha256=sha(owner/'pins.json'),frozen_sha256=sha(owner/'FROZEN.json'))))
owner=Path('/tmp/mcfta-fresh-node-counter-growth-document-preparation')
owner.mkdir()
basis=previous/'update-documents.py'
assert sha(basis)=='e79ad06516c2724e062db5d664fa6fbf3d04fa66460a70b89db6296a85962c87'
original=basis.read_text()
selected=original
for before,after in [('fb1949b3cf44911f25ac105403879a259fc8056a',START),
    ('actual_jobs=3, source_jobs=2','actual_jobs=5, source_jobs=4'),
    ('failed_jobs=0, warned_source_exit_zero_jobs=0','failed_jobs=1, warned_source_exit_zero_jobs=1'),
    ('public_theorems=1, audit_build_jobs=3651, audit_dependencies=75528','public_theorems=3, audit_build_jobs=3652, audit_dependencies=75541'),
    ('26624ac69192ddd76665e9da66031d6d6b3637ecdae938fd34493d890a5e786f',actual['audit']['log_sha256']),
    ('assert len(type_summary) == 3','assert len(type_summary) == 9'),
    ('lean/notes-current-pair-inventory-rebase.md','lean/notes-current-fresh-node-counter-growth.md')]:
    selected=replace_one(selected,before,after)
assert selected.count('public-readback/pair-inventory-rebase-')==3
selected=selected.replace('public-readback/pair-inventory-rebase-','public-readback/fresh-node-counter-growth-')
retain(owner,'update-documents.py',original,selected)
for source,target in [('current-update.proposal.md','current-update.template.md'),('focused-note.proposal.md','focused-note.template.md')]:
    data=Path('/tmp/mcfta-fresh-node-counter-growth-'+source).read_bytes()
    assert data.endswith(b'\n') and b'\r' not in data
    (owner/target).write_bytes(data)
(owner/'scope.md').write_text('Root adapted the complete H32 writer88 and conditional templates. Actual ledger5/4/1 failed/1 warned source, Audit3652/75541 and exact raw hash are bound. All nine LF inverses and FINDINGS-first repair index guards remain before writes. Three public heads require nine TYPE summary lines. Both actual saved modes and the exact two-file proof commit must precede documents. No selected program ran. This proves only repaired constructor node counter lower bounds, including pending; H6 remains strongest combined and the whole goal remains ACTIVE/incomplete. No new Haskell repair is indicated.\n')
freeze(owner,['update-documents.py'])
owner=Path('/tmp/mcfta-fresh-node-counter-growth-publication-preparation')
owner.mkdir()
expected={'proof-commit.py':'12db8e862a24e39e1137704312f6537086635cb86ce8034dd2ce12361e4daa40',
    'final-publication.py':'2b88a0456f0cbea288ea71fbed3d05f35a1b8bf2ca21bc01b874e06af35298da',
    'run-standalone-proof-evidence.py':'39b9d639157ed69b323ca1b7b743dd6e5bd5b64aa28bcaf60fed50eaa7489b17'}
for name,digest in expected.items():
    assert sha(previous/name)==digest
    original=(previous/name).read_text()
    selected=original.replace('mcfta-pair-inventory-rebase','mcfta-fresh-node-counter-growth')
    if name in ['proof-commit.py','run-standalone-proof-evidence.py']:
        selected=replace_one(selected,"report['actual_jobs'] == 3","report['actual_jobs'] == 5")
        selected=replace_one(selected,"report['public_theorems'] == 1 and report['failed_jobs'] == 0","report['public_theorems'] == 3 and report['failed_jobs'] == 1")
    if name=='proof-commit.py':
        selected=replace_one(selected,"report['audit_dependencies'] == 75528","report['audit_dependencies'] == 75541")
        selected=replace_one(selected,'Preserve cached pair meaning in the enlarged inventory','Prove node counter growth in repaired construction')
    elif name=='final-publication.py':
        for before,after in [('20261023-pair-inventory-rebase','20261023-fresh-node-counter-growth'),
            ('fb1949b3cf44911f25ac105403879a259fc8056a',START),
            ('codex/backup-pair-inventory-rebase-20261023-1112','codex/backup-fresh-node-counter-growth-20261023-1209'),
            ('lean/notes-current-pair-inventory-rebase.md','lean/notes-current-fresh-node-counter-growth.md'),
            ('Preserve pair inventory rebase proof evidence','Preserve repaired constructor counter proof evidence')]:
            selected=replace_one(selected,before,after)
    retain(owner,name,original,selected)
(owner/'scope.md').write_text('Root adapted the complete H32 proof committer28, local publisher47 and standalone launcher26. Exact generic guards remain. Accepted source/history and normal/live PASS from cwd / precede the exact two-file proof commit. Actual ledger5 jobs/3 public/1 retained failure and Audit75541 are bound. The local publisher checks formalize, backup/main refs, full sealed paths, all filesystem/index/HEAD blobs and modes, clean tree and seal. It has no network command. User-authorized Root push follows local verification. No selected program ran.\n')
freeze(owner,list(expected))
