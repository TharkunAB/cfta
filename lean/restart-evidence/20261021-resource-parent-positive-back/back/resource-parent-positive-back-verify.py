#!/usr/bin/env python3
"""Verify the frozen all-child positive-source evidence without running Lean."""
from __future__ import annotations
import argparse
import difflib
import hashlib
import json
import re
import runpy
from pathlib import Path

HERE=Path(__file__).resolve().parent
PREFIX='resource-parent-positive-back-'
HEAD='MicroCFTA.SourceCurrentResourceParentPositiveBack.children'


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
    assert pins==manifest['sources'] and len(pins)==11
    for pin in pins:
        snapshot=HERE/relative(pin['snapshot']);check(snapshot,pin)
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
    assert selected['failed_checks']==selected['warning_checks']==selected['infrastructure_attempts']==selected['canonical_jobs']==selected['constructed_pairs']==0
    assert selected['new_public_pairs']==1 and selected['official_edits_by_author'] is False
    source=HERE/selected['source'];text=source.read_text()
    assert sha(source)==selected['source_sha256']=='fa63f2d89d8494b24e5563bff710f4d9eab9b887a951ee16a1ab28660c04fc7e'
    assert len(text.splitlines())==selected['source_lines']==208
    assert re.findall(r'^theorem (\w+)',text,re.M)==['children']
    assert re.findall(r'^private theorem (\w+)',text,re.M)==['rel_covers','prefix_data']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private',text)
    proposal=(HERE/'inputs/plan/proposed-signature.lean.txt').read_text()
    assert text.split('theorem children\n',1)[1].split('\n := by',1)[0]==proposal.split('theorem children\n',1)[1].split('\n\nend MicroCFTA.',1)[0]
    assert selected['public_header_byte_exact_frozen_proposal'] and selected['proposal_elaborated_before_draft'] is False
    first=(HERE/'positive-back-prelaunch-1.source.lean').read_text()
    second=(HERE/'positive-back-prelaunch-2.source.lean').read_text()
    third=(HERE/'positive-back-prelaunch-3.source.lean').read_text()
    assert len(first.splitlines())==223 and len(second.splitlines())==224 and third==text
    assert second==first.replace('local notation "Edge" => EdgeValue Symbol Guard\n','local notation "Edge" => EdgeValue Symbol Guard\nlocal notation "Record" => SourceEqualityClassOrder.Record\n')
    expected=''.join(difflib.unified_diff(second.splitlines(keepends=True),third.splitlines(keepends=True),fromfile='positive-back-prelaunch-2.source.lean',tofile='SourceCurrentResourceParentPositiveBack.lean'))
    assert expected==(HERE/'prelaunch-covers-only.patch').read_text()
    delta=read(HERE/'prelaunch-covers-only.json')
    assert delta['before_sha256']==sha(HERE/'positive-back-prelaunch-2.source.lean') and delta['after_sha256']==sha(source)
    assert delta['proof_jobs']==0 and delta['public_header_changed'] is False
    for needle in ['SourceCurrentActualParentBranchCases.edge_cases','SourceCurrentActualParentSelectedCertificates.selected_certificates','SourceCurrentSelectedPrimaryOrigins.selected_class','SourceCurrentRequiredPositiveChronology.pass']:
        assert text.count(needle)==1,needle
    assert text.count(':= written')==1
    assert 'ResourceOwnerInheritedProgress.key_ne_inherited' not in text
    assert 'foundOwner' not in text
    ledger=read(HERE/(PREFIX+'attempt-ledger.json'));attempts=ledger['attempts']
    assert ledger['actual_lean_jobs']==selected['lean_jobs']==len(attempts)==2
    assert ledger['failed_checks']==selected['failed_checks']==sum(item['exit_code']!=0 for item in attempts)==0
    assert ledger['copies_add_lean_jobs']==ledger['canonical_jobs']==0 and ledger['infrastructure_attempts']==[]
    assert {path.stem for path in HERE.glob(PREFIX+'*.json') if re.fullmatch(PREFIX+r'(?:direct|public)-\d+',path.stem)}=={item['name'] for item in attempts}
    for item in attempts:
        stem=item['name'];receipt=read(HERE/(stem+'.json'));log=(HERE/(stem+'.log')).read_text()
        assert item['lean_launched'] and receipt['exit_code']==item['exit_code']
        assert sha(HERE/(stem+'.json'))==item['receipt_sha256']
        assert sha(HERE/(stem+'.log'))==item['log_sha256']
        assert sha(HERE/receipt['source'])==receipt['sha256']==item['source_sha256']
        assert read(HERE/(stem+'.limits.json'))=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=read(HERE/(stem+'.usage.json'))
        assert 0<=usage['age_seconds']<120 and usage['remaining_percent']>1
        assert usage['remaining_percent']==item['usage_remaining_percent']==46
        assert receipt['wrapper'][1:5]==['--mem','4G','--time','5m']
        assert receipt['command'][0].endswith('lean4---v4.34.1/bin/lean') and receipt['command'][1]=='-Dlinter.all=true'
        assert not re.search(r'\bwarning(?:\([^)]*\))?:',log)
    assert [line.split()[-2] for line in (HERE/(PREFIX+'peaks.txt')).read_text().splitlines()]==['179M','320M']
    strict,public=selected['selected_strict'],selected['selected_public']
    assert read(HERE/(strict+'.json'))['exit_code']==read(HERE/(public+'.json'))['exit_code']==0
    assert not (HERE/(strict+'.log')).read_bytes()
    assert (HERE/(strict+'.source.lean')).read_bytes()==source.read_bytes()
    result=runpy.run_path(str(HERE/(PREFIX+'readback.py')))['check'](source,HERE/(public+'.source.lean'),HERE/(public+'.log'))
    assert result==read(HERE/(PREFIX+'readback.json'))
    assert result['public_log_bytes']==selected['public_log_bytes'] and result['public_log_sha256']==selected['public_log_sha256']
    assert result['axioms_by_head']==selected['axioms_by_head']
    print(json.dumps(dict(status='PASS',live=args.live,local_pins=len(manifest['files']),root_pins=len(pins),lean_jobs=selected['lean_jobs'],failed_checks=0,warning_checks=0,canonical_jobs=0,infrastructure_attempts=0,constructed_pairs=0,new_public_pairs=1,public_heads=[HEAD],all_eight_settings=True,public_type_identity=True,standard_axioms_only=True,manifest_sha256=sha(HERE/(PREFIX+'manifest.json'))),indent=2))


if __name__=='__main__':
    main()
