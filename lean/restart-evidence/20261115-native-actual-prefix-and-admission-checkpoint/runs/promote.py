from pathlib import Path
import hashlib
import json
import shutil

work = Path(__file__).parent
base = Path('lean/restart-evidence')
specs = [
    ('20261115-current-actual-prefix-returned-induction-draft',
     'SourceCurrentAllocatedNativeActualPrefixReturnedInduction',
     '12318c748fc83735732bae5e2e1447c1b1563b7d64918dbe6f04857c7c123b77',
     ['returned_at_every_actual_prefix'], '20261115-native-actual-prefix-returned-induction-check'),
    ('20261115-source-mixed-ordinary-native-child-qualification-draft',
     'SourceCurrentAllocatedNativeSourceMixedOrdinaryChildQualification',
     '35ddfd3321ca360fb3baa7def28d281af0865451e3b234c2d2df8f90ccec9202',
     ['current_stored_universe_mixed_ordinary_child_qualification'],
     '20261115-native-source-mixed-ordinary-child-qualification-check'),
    ('20261115-general-closed-native-union-typed-prefix-repair',
     'SourceCurrentAllocatedNativeClosedUnionProfile',
     '18708cbc162aa4d8f0290302207e86c76501a78dbf4c217e98a5df0517167624',
     ['closed_union_body_profile_of_fuel_induction'],
     '20261115-native-general-closed-union-typed-repair-check'),
    ('20261115-current-same-prefix-keyed-child-result-index-repair',
     'SourceCurrentAllocatedNativeSamePrefixKeyedChildResult',
     '568ea29287bef52f0743ebe52b327201b80608240d38f72876074cdf48107a71',
     ['keyed_child_law_at_node_finish', 'keyed_child_law_at_edge_finish'],
     '20261115-native-same-prefix-keyed-child-index-repair-check'),
]


def declaration(text: str, name: str) -> str:
    start = text.index('theorem ' + name + '\n')
    end = text.index(' := by', start)
    return text[start:end]


promotion = []
for folder, module, digest, statements, checked_run in specs:
    raw = base / folder / (module + '.lean')
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    check = json.loads((base / checked_run / 'checked.json').read_text())
    assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in check['checks'])
    if module == 'SourceCurrentAllocatedNativeClosedUnionProfile':
        original = base / '20261115-general-closed-native-union-profile-draft' / raw.name
        assert declaration(raw.read_text(), statements[0]) == declaration(original.read_text(), statements[0])
    if module == 'SourceCurrentAllocatedNativeSamePrefixKeyedChildResult':
        original = base / '20261115-current-same-prefix-keyed-child-result-draft' / raw.name
        for name in statements:
            assert declaration(raw.read_text(), name) == declaration(original.read_text(), name)
        first = raw.read_text().index('theorem ' + statements[0] + '\n')
        old_first = original.read_text().index('theorem ' + statements[0] + '\n')
        assert raw.read_text()[first:] == original.read_text()[old_first:]
    public = Path('lean/MicroCFTA') / raw.name
    if public.exists():
        assert public.read_bytes() == raw.read_bytes()
    else:
        shutil.copyfile(raw, public)
    promotion.append({'module': module, 'raw': str(raw), 'sha256': digest, 'public_statements': statements})
(work / 'promotion.json').write_text(json.dumps(promotion, indent=2) + '\n')
print(json.dumps({'exact_modules': len(promotion), 'public_statements': 5, 'all_private_checks_passed': True}))
