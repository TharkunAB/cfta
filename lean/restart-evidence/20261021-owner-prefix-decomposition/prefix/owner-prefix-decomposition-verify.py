#!/usr/bin/env python3
"""Verify frozen owner prefix evidence without running Lean."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import runpy
from pathlib import Path

HERE=Path(__file__).resolve().parent
PREFIX='owner-prefix-decomposition-'
HEAD='MicroCFTA.SourceCurrentOuterOwnerPrefix.first_child'
FINAL='e790cbbaab2d2dd73a45738d950f45463102c2a7048f8bd59b5a95d6f3e965c6'

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path: Path) -> dict:
    return json.loads(path.read_text())

def relative(value: str) -> Path:
    path=Path(value)
    assert not path.is_absolute() and '..' not in path.parts,value
    return path

def check(path: Path,pin: dict) -> None:
    assert path.is_file() and path.stat().st_size==pin['bytes'] and sha(path)==pin['sha256'],str(path)

def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    manifest=read(HERE/(PREFIX+'manifest.json'))
    assert manifest['finalized']
    for pin in manifest['files']:
        check(HERE/relative(pin['path']),pin)
    pins=read(HERE/(PREFIX+'source-pins.json'))['sources']
    assert pins==manifest['sources'] and len(pins)==8
    for pin in pins:
        snapshot=HERE/relative(pin['snapshot'])
        check(snapshot,pin)
        lines=snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines)==pin['lines']
        for span in pin['reviewed_ranges']:
            lo,hi=span['start'],span['end']
            assert 1<=lo<=hi<=len(lines)
            assert hashlib.sha256(b''.join(lines[lo-1:hi])).hexdigest()==span['sha256']
        if args.live:
            check(args.root/relative(pin['path']),pin)
    selected=read(HERE/(PREFIX+'selection.json'))
    assert selected['finalized'] and selected['public_heads']==[HEAD]
    assert selected['lean_jobs']==4 and selected['failed_checks']==2
    assert selected['warning_checks']==selected['infrastructure_attempts']==selected['canonical_jobs']==selected['constructed_pairs']==0
    assert selected['new_public_pairs']==1 and selected['official_edits_by_author'] is False
    source=HERE/selected['source'];text=source.read_text()
    assert sha(source)==selected['source_sha256']==FINAL
    assert len(text.splitlines())==selected['source_lines']==203
    assert re.findall(r'^theorem (\w+)',text,re.M)==['first_child']
    assert re.findall(r'^private theorem (\w+)',text,re.M)==['head_cases','node_tail','walk_first','descendants_first','rows_first']
    assert re.findall(r'^private def (\w+)',text,re.M)==['NodeTail','WalkFirst','RowsFirst']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private',text)
    proposal=(HERE/'inputs/plan/proposed-signature.lean.txt').read_text()
    assert text.split('theorem first_child\n',1)[1].split(' := by',1)[0]==proposal.split('theorem first_child\n',1)[1].split('\nend MicroCFTA.',1)[0]
    assert selected['public_header_byte_exact_frozen_proposal'] and selected['proposal_elaborated_before_draft'] is False
    prelaunch=(HERE/'owner-prefix-decomposition-prelaunch-1.source.lean').read_text()
    assert sha(HERE/'owner-prefix-decomposition-prelaunch-1.source.lean')=='5a9dfbc537c552431d0d159d398e1f8feb80ee675c71b88be9f79ca25d5c638a'
    first=(HERE/(PREFIX+'direct-1.source.lean')).read_text()
    assert first==prelaunch.replace('private theorem head_cases','variable {g s r e p h m c n budget : Nat}\n\nprivate theorem head_cases',1)
    second=(HERE/(PREFIX+'direct-2.source.lean')).read_text()
    assert second==first.replace('refine ⟨0,next,value,[],before','refine ⟨0,fuel,value,[],before').replace('have sameFuel : next + 1 =','have sameFuel : fuel + 1 =').replace('(.rows (next + 1) inherited','(.rows (fuel + 1) inherited').replace('(congrArg nodeEdges ordinary)','(congrArg InternedEdgeResidency.nodeEdges ordinary)')
    assert text==second.replace('        have entered := Reached.snoc (Reached.refl _) (SourceCurrentOuterExecutionAncestry.Step.body_rows ordinary)\n','').replace('earlier,child,ownerSplit,entered.trans cut,parent','earlier,child,ownerSplit,(Reached.snoc (.refl _) (.body_rows ordinary)).trans cut,parent')
    expected={PREFIX+'direct-1':1,PREFIX+'direct-2':1,PREFIX+'direct-3':0,PREFIX+'public-1':0}
    ledger=read(HERE/(PREFIX+'attempt-ledger.json'))
    attempts=ledger['attempts']
    assert ledger['actual_lean_jobs']==4 and ledger['failed_checks']==2 and ledger['copies_add_lean_jobs']==ledger['canonical_jobs']==0
    assert ledger['infrastructure_attempts']==[]
    assert len(attempts)==4 and {item['name']:item['exit_code'] for item in attempts}==expected
    assert {path.stem for path in HERE.glob(PREFIX+'*.json') if re.fullmatch(PREFIX+r'(?:direct|public)-\d+',path.stem)}==set(expected)
    for item in attempts:
        stem=item['name'];receipt=read(HERE/(stem+'.json'));log=(HERE/(stem+'.log')).read_text()
        assert item['lean_launched'] and receipt['exit_code']==item['exit_code']
        assert sha(HERE/(stem+'.json'))==item['receipt_sha256']
        assert sha(HERE/(stem+'.log'))==item['log_sha256']
        assert sha(HERE/receipt['source'])==receipt['sha256']==item['source_sha256']
        assert read(HERE/(stem+'.limits.json'))=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=read(HERE/(stem+'.usage.json'))
        assert 0<=usage['age_seconds']<120 and usage['remaining_percent']>1
        assert usage['remaining_percent']==item['usage_remaining_percent']
        assert receipt['wrapper'][1:5]==['--mem','4G','--time','5m']
        assert receipt['command'][0].endswith('lean4---v4.34.1/bin/lean') and receipt['command'][1]=='-Dlinter.all=true'
        assert not re.search(r'\bwarning(?:\([^)]*\))?:',log)
        assert len(re.findall(r': error',log))==item['error_diagnostics']
    assert [item['error_diagnostics'] for item in attempts]==[4,40,0,0]
    strict,public=selected['selected_strict'],selected['selected_public']
    assert strict==PREFIX+'direct-3' and public==PREFIX+'public-1'
    assert not (HERE/(strict+'.log')).read_bytes()
    assert (HERE/(strict+'.source.lean')).read_bytes()==source.read_bytes()
    result=runpy.run_path(str(HERE/(PREFIX+'readback.py')))['check'](source,HERE/(public+'.source.lean'),HERE/(public+'.log'))
    assert result==read(HERE/(PREFIX+'readback.json'))
    assert result['public_log_bytes']==selected['public_log_bytes']==3520979
    assert result['public_log_sha256']==selected['public_log_sha256']=='bfe3af9863750dc5ef47ea3e407da6ed7dfab7e588918acef2ec319b2fbfdff4'
    assert result['axioms_by_head']==selected['axioms_by_head']
    print(json.dumps(dict(status='PASS',live=args.live,local_pins=len(manifest['files']),root_pins=len(pins),lean_jobs=4,failed_checks=2,warning_checks=0,canonical_jobs=0,infrastructure_attempts=0,constructed_pairs=0,new_public_pairs=1,public_heads=[HEAD],all_eight_settings=True,public_type_identity=True,standard_axioms_only=True,manifest_sha256=sha(HERE/(PREFIX+'manifest.json'))),indent=2))

if __name__=='__main__':
    main()
