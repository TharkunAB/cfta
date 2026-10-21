#!/usr/bin/env python3
"""Verify the source-only outer writer plan without running Lean."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()

def read(p: Path) -> dict:
    return json.loads(p.read_text())

def rel(value: str) -> Path:
    p=Path(value)
    assert not p.is_absolute() and '..' not in p.parts
    return p

def check(p: Path,pin: dict) -> None:
    assert p.is_file() and p.stat().st_size==pin['bytes'] and sha(p)==pin['sha256'],str(p)

def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',required=True,type=Path)
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args();here=Path(__file__).resolve().parent
    manifest=read(here/'plan-manifest.json');assert manifest['finalized']
    for pin in manifest['files']:check(here/rel(pin['path']),pin)
    pins=read(here/'plan-source-pins.json')['files'];assert pins==manifest['sources']
    for pin in pins:
        p=here/'inputs/root'/rel(pin['path']);check(p,pin)
        if args.live:check(args.root/rel(pin['path']),pin)
        lines=p.read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            assert 1<=span['start']<=span['end']<=len(lines)
            assert hashlib.sha256(b''.join(lines[span['start']-1:span['end']])).hexdigest()==span['sha256']
    selected=read(here/'plan-selection.json')
    assert selected['status']=='APPROVED SOURCE-ONLY PLAN; UNPROVED'
    assert selected['new_lean_commands']==selected['new_lake_commands']==selected['new_canonical_commands']==0
    assert selected['new_public_pairs']==selected['constructed_pairs']==0 and not selected['official_edits']
    assert selected['implementation_requires_complete_source_review'] and selected['maximum_lines_before_review']==650
    assert selected['public_head']=='MicroCFTA.SourceCurrentOuterResourceWriters.reached' and selected['public_heads']==1
    proposal=here/'proposed-signature.lean.txt';assert sha(proposal)==selected['public_signature_sha256']
    text=proposal.read_text();assert re.findall(r'^theorem (\w+)',text,re.M)==['reached']
    assert not re.search(r'^(?:def|structure|inductive)\s',text,re.M)
    header=text.split('theorem reached',1)[1].split('\nend ',1)[0]
    assert header.rstrip().endswith(selected['public_output'])
    for name in ['actual','initial','frame','fits','known','inputs','room','normal','supported','causal','merged','positiveMemo','origins']:
        assert re.search(r'\('+name+r'\s*:',header),name
    assert '(origins : SourceCurrentResourceParentWriters.Origins formulas solver (caller first))' in header
    assert ' := by' not in text and 'sorry' not in text
    authority=here/'inputs/authority'
    expected={'writer':'writer-owner-manifest.json','completed_stores':'completed-store-owner-manifest.json','prefix_stores':'prefix-owner-manifest.json'}
    source_names={'writer':'SourceCurrentResourceParentWriters','completed_stores':'SourceCurrentOuterNativeStores','prefix_stores':'SourceCurrentOuterPrefixNativeStores'}
    for key,name in expected.items():
        dep=selected['dependencies'][key]
        assert sha(authority/name)==dep['owner_manifest_sha256']
        p=here/'inputs/root/lean/MicroCFTA'/f'{source_names[key]}.lean'
        assert sha(p)==dep['source_sha256']
    dep=selected['dependencies']['prefix_stores']
    assert dep['status']=='FINAL FROZEN CHECKED; OFFICIAL ROOT STRICT AND AUDIT PASSED'
    assert sha(authority/'prefix-owner-selection.json')==dep['owner_selection_sha256']
    owner=read(authority/'prefix-owner-selection.json')
    assert owner['source_sha256']==dep['source_sha256'] and owner['source_lines']==198
    checks=here/'inputs/prefix-checks'
    for field in ['selected_strict','selected_public']:
        stem=dep[field];assert owner[field]==stem
        receipt=read(checks/(stem+'.json'));assert receipt['exit_code']==0
        assert sha(checks/rel(receipt['source']))==receipt['sha256']
    assert (checks/(dep['selected_strict']+'.log')).read_bytes()==b''
    source=(here/'inputs/root/lean/MicroCFTA/SourceCurrentOuterPrefixNativeStores.lean').read_text()
    printer=(checks/'prefix-native-stores-public.lean').read_text();assert printer.startswith(source)
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert printer.count('set_option '+option)==1
    log=checks/(dep['selected_public']+'.log');assert log.stat().st_size==owner['public_log_bytes'] and sha(log)==owner['public_log_sha256']
    rendered=log.read_text();head='MicroCFTA.SourceCurrentOuterPrefixNativeStores.reached'
    checked,printed=rendered.split('@'+head+' :',1)[1].split('\ntheorem '+head+' :',1)
    declared,proof=printed.split(' :=',1);assert ''.join(checked.split())==''.join(declared.split()) and '_private' not in checked+declared
    ax=re.search(re.escape("'"+head+"' depends on axioms:")+r'\s*\[([^\]]*)\]',proof);assert ax
    names=sorted(x.strip() for x in re.sub(r'\.\{[^}]*\}','',ax.group(1)).split(','));assert names==['Classical.choice','Quot.sound','propext']
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|⋯|…|\.\.\.',rendered)
    for name in ['root-prefix-strict-1.json','root-prefix-audit-1.json']:assert read(authority/name)['exit_code']==0
    assert read(authority/'root-prefix-strict-1.json')['sha256']==dep['source_sha256']
    plan=(here/'plan.md').read_text()
    for phrase in ['six private','ONE old','eight literal','one call','only public head','No missing mathematical','same Written','not yet add a selected historical consumer']:
        assert phrase.lower() in plan.lower(),phrase
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),'root_pins':len(pins),'new_lean_commands':0,'new_lake_commands':0,'new_canonical_commands':0,'new_public_pairs':0,'proposed_public_heads':1,'dependency_prefix_status':dep['status'],'manifest_sha256':sha(here/'plan-manifest.json')},indent=2))

if __name__=='__main__':main()
