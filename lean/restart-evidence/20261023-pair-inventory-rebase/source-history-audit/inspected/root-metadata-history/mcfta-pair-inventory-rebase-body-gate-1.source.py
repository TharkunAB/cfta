exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
import re
import sys
owner = Path('/tmp/mcfta-pair-inventory-rebase-source-v1')
review = Path('/tmp/mcfta-pair-inventory-rebase-body-v1-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
checked_package(owner, 'cdffa553d6358cc13d86024a391ddd29c2bcaab4472802c8c5ef557f54728575', 'ff5fd589cb93257c8625418477678e3d3070ae2b12f21d774996733c36be61db')
checked_package(review, expected_pins, expected_freeze)
assert sha(review / 'review.json') == expected_review
assert load(review / 'review.json')['status'] == 'CLEAR'
source = (owner / (NAME + '.lean')).read_bytes()
assert sha(owner / (NAME + '.lean')) == 'b7351e92c6981f5caa5d7a18a05676912b9ee741c94cc2a39f1ba3ef74b03840'
assert len(source.splitlines()) == 77 <= 180
positions = []
for fragment in load(HERE / 'declaration-plan/insertion-map.json')['compiled_fragments']:
    data = (HERE / 'declaration-plan' / fragment['file']).read_bytes()
    if 'future_body_attachment' in fragment:
        data = data.rstrip(b'\n') + fragment['future_body_attachment'].encode()
    assert source.count(data) == 1, fragment['file']
    positions.append(source.index(data))
assert positions == sorted(positions)
body = (owner / 'body.txt').read_bytes()
assert re.findall(rb'\blet\s+(\w+)', body) == [b'next']
assert re.findall(rb'\bhave\s+(\w+)', body) == [b'included', b'agreement']
assert len(re.findall(rb'\bobtain\b', body)) == 1
assert not re.search(rb'\b(?:sorry|admit|axiom|private|induction|show|suffices|haveI|letI)\b|set_option', source)
archive(owner, 'source-v1')
archive(review, 'body-v1-audit')
assert not (HERE / 'strict-selected-source.lean').exists()
(HERE / 'strict-selected-source.lean').write_bytes(source)
save('root-v1-body-gate.json', dict(status='ACCEPTED_COMPLETE_BODY_FOR_STRICT_CHECK',
    module=NAME, source_sha256=sha(owner / (NAME + '.lean')), source_lines=77,
    root_complete_source_lines_read=77, whole_source_hard_stop=180,
    exact_declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
    independent_body_review_sha256=expected_review, all_six_fragments_exact=True,
    public_let_occurrences=3, local_haves=2, local_lets=1, local_obtains=1, obtained_fields=5,
    all_lambda_types_reviewed=True, helper_count=0, induction=False,
    agreement_derived_not_assumed=True, same_full_wrapper=True,
    shorter_than_soft_estimate_disclosed=True, default_declaration_limits=True,
    all_linters=True, goal_status='ACTIVE_INCOMPLETE'))
print('ACCEPTED complete77-line body with all six exact contracts before strict compilation.')
