#!/usr/bin/env python3
"""Verify the frozen local nonhereditary rank and numeric-pair evidence."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = Path(__file__).resolve().parent
MODULES = [
    ('SourceCurrentConstrainedCapNonplainRank.lean', 'nonplain-rank', 3, 'b153be1c11384c52b335ff244b4981411d28fa9bba341ea4a26e0c11e6d3ad2d'),
    ('SourceCurrentConstrainedCapNativePairRank.lean', 'pair-rank', 2, 'f24eafbe1bf4661f8d0e7a75c59d3f038a61034b2b2e61a5bbb82a7c208f9ffd'),
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def probes(prefix: str, kind: str, attempt: int, names: list[str]) -> None:
    source = (EVIDENCE / f'{prefix}-{kind}.lean').read_text()
    log = (EVIDENCE / f'{prefix}-{kind}-{attempt}.log').read_text()
    assert source == (EVIDENCE / f'{prefix}-{kind}-{attempt}.source.lean').read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true',
                   'pp.deepTerms true', 'pp.maxSteps 1000000', 'pp.fullNames true']:
        assert f'set_option {option}' in source
    assert source.count('#print axioms ') == len(names)
    assert source.count('#check @') == len(names)
    assert not re.search(r'error:|error\(|warning:|sorryAx|declaration uses|truncated', log)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log, re.S)
    assert [name for name, _ in reports] == names
    for name, axioms in reports:
        used = {re.sub(r'\.\{[^}]*\}', '', atom.strip()) for atom in axioms.split(',') if atom.strip()}
        assert used <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert re.search(r'^@?' + re.escape(name) + r'(?:\.\{[^}]*\})?\s*:', log, re.M), name
        assert f'#check @{name}' in source


def main() -> None:
    for module, prefix, attempt, expected in MODULES:
        path = ROOT / 'lean/MicroCFTA' / module
        assert digest(path) == expected
        assert path.read_bytes() == (EVIDENCE / f'{prefix}-final.source.lean').read_bytes()
        assert path.read_bytes() == (EVIDENCE / f'{prefix}-direct-{attempt}.source.lean').read_bytes()
        assert not (EVIDENCE / f'{prefix}-direct-{attempt}.log').read_bytes()
    names = json.loads((EVIDENCE / 'nonplain-rank-public-names.json').read_text())
    assert len(names) == 26
    probes('nonplain-rank', 'public', 1, names)
    probes('pair-rank', 'public', 1, ['MicroCFTA.SourceCurrentConstrainedCapNativePairRank.' + name
        for name in ['sorted_pair_eq', 'same_identity_rank', 'same_pair_rank', 'strict_pair_ne']])
    probes('nonplain-rank', 'kernels', 3, ['MicroCFTA.NonplainRankChecks.mixed_shell', 'MicroCFTA.NonplainRankChecks.source_reference'])
    probes('pair-rank', 'kernels', 2, ['MicroCFTA.PairRankChecks.ordinary_children_excluded'])
    for log, jobs in [('nonplain-rank-build.log', 1005), ('native-pair-rank-build.log', 1007)]:
        assert f'Build completed successfully ({jobs} jobs).' in (EVIDENCE / log).read_text()
    for prefix, attempt in [('nonplain-rank', 1), ('pair-rank', 1)]:
        assert 'error' in (EVIDENCE / f'{prefix}-direct-{attempt}.log').read_text()
        assert (EVIDENCE / f'{prefix}-direct-{attempt}.source.lean').is_file()
    manifest_path = EVIDENCE / 'nonplain-pair-manifest.json'
    if manifest_path.is_file() and '--no-manifest' not in sys.argv:
        for entry in json.loads(manifest_path.read_text())['files']:
            path = ROOT / entry['path']
            assert path.is_file() and digest(path) == entry['sha256'], str(path)
    print('PASS: two exact frozen modules; strict direct/canonical checks; 30 public + 3 integration pairs; complete signatures; standard axioms; preserved attempts; manifest hashes.')


if __name__ == '__main__':
    main()
