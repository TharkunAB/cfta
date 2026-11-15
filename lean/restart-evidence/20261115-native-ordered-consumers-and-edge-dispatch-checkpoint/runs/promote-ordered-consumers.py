from pathlib import Path
import hashlib
import json
import shutil

work = Path(__file__).parent
base = Path('lean/restart-evidence')
checked = json.loads((base / '20261115-native-ordered-source-consumers-check/checked.json').read_text())
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in checked['checks'])
specs = [
    ('20261115-source-ordered-mixed-ordinary-child-qualification-draft',
     'SourceCurrentAllocatedNativeSourceOrderedMixedOrdinaryChildQualification',
     '058b0dca590fa5d859a5f1ce91d094052cbf1097dcfe5a5f9ee96c565e958459',
     'current_stored_universe_mixed_ordinary_child_qualification_ordered_entry'),
    ('20261115-current-ordered-finite-prefix-reference-control-draft',
     'SourceCurrentAllocatedNativeOrderedFinitePrefixReferenceControl',
     '812d6ac8d1f23fc16860b84d3893216d7bcf30fca691a013bf83dba3e458682d',
     'current_stored_universe_ref_control_at_finite_prefix_ordered_entry'),
]
promotion = []
for folder, module, digest, statement in specs:
    raw = base / folder / (module + '.lean')
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    text = raw.read_text()
    start = text.index('theorem ' + statement + '\n')
    end = text.index(' := by', start) + len(' := by')
    assert text[start:end] + '\n' == (raw.parent / 'PUBLIC-HEADER.lean.txt').read_text()
    public = Path('lean/MicroCFTA') / raw.name
    assert not public.exists()
    shutil.copyfile(raw, public)
    promotion.append({'module': module, 'raw': str(raw), 'sha256': digest, 'public_statements': [statement]})
(work / 'promotion.json').write_text(json.dumps(promotion, indent=2) + '\n')
print(json.dumps({'exact_promoted_modules': 2, 'private19451_exit': 0}))
