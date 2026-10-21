#!/usr/bin/env python3
"""Check the complete public printer log without running Lean."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

HEAD = 'MicroCFTA.SourceCurrentResourceOwnerInheritedDispatch.key_ne_inherited'
SETTINGS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
            'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']

def check(source: Path, printer: Path, log_path: Path) -> dict:
    text, full, log = source.read_text(), printer.read_text(), log_path.read_text()
    assert full.startswith(text + '\n')
    for setting in SETTINGS:
        assert full.count('set_option ' + setting + '\n') == 1, setting
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert full.count(directive + HEAD + '\n') == 1
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    checked, printed = log.split('@' + HEAD + ' :', 1)[1].split('\ntheorem ' + HEAD + ' :', 1)
    delimiters = list(re.finditer(r' :=\n(?=fun\b)', printed))
    assert len(delimiters) == 1, len(delimiters)
    delimiter = delimiters[0]
    declared, proof = printed[:delimiter.start()], printed[delimiter.end():]
    assert ''.join(checked.split()) == ''.join(declared.split())
    assert '_private' not in checked + declared
    match = re.search(re.escape("'" + HEAD + "' depends on axioms:") + r'\s*\[([^\]]*)\]', proof)
    assert match and len(proof[:match.start()]) > 1000
    names = sorted(item.strip() for item in re.sub(r'\.\{[^}]*\}', '', match.group(1)).split(','))
    assert names == ['Classical.choice', 'Quot.sound', 'propext'], names
    return dict(status='PASS', public_heads=[HEAD], public_log_bytes=log_path.stat().st_size,
                public_log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest(),
                public_type_identity=True, public_type_characters=len(checked),
                all_eight_settings=True, no_omissions=True, no_private_public_type_names=True,
                axioms_by_head={HEAD: names})

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('source', type=Path)
    parser.add_argument('printer', type=Path)
    parser.add_argument('log', type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.source, args.printer, args.log), indent=2))
