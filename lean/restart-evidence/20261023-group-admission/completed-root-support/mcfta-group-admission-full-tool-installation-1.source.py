exec(compile(open('/tmp/mcfta-group-admission-root-common.py').read(), '/tmp/mcfta-group-admission-root-common.py', 'exec'))
import sys
owner = Path('/tmp/mcfta-group-admission-full-preparation')
checked_package(owner,'b179bd7ea0aac267c89397ae039dc9dabff9e36b98ba7af7f049222cb72b9dc3','edcd5443053f6fa9eb45c065ad0c302e83abc4e0d9ec0cee4f94c4d32019b4eb')
audit = Path('/tmp/mcfta-group-admission-full-tools-audit')
expected_pins, expected_freeze, expected_review = sys.argv[1:]
assert all(len(value) == 64 and set(value) <= set('0123456789abcdef') for value in sys.argv[1:])
checked_package(audit,expected_pins,expected_freeze)
assert sha(audit / 'review.json') == expected_review and load(audit / 'review.json')['status'] == 'CLEAR'
assert load(HERE / 'root-full-tool-scope-gate.json')['selected_source_authoring_accepted']
selected = load(HERE / 'selected-source-gate.json')
assert selected['status'] == 'ACCEPTED_STRICT_SOURCE' and selected['strict_log_bytes'] == 0
assert (HERE / 'strict1.log').read_bytes() == b''
assert not (HERE / (NAME + '.lean')).exists() and not (HERE / 'FULL1.json').exists()
assert sha(HERE / 'strict-selected-source.lean') == selected['source_sha256']
tools = {'check-full-public.py':owner / 'selected/check-full-public.py', 'prepare-full.py':owner / 'selected/prepare-selected-full.py'}
assert sum(len(path.read_bytes().splitlines()) for path in tools.values()) == 203
assert all(not (HERE / name).exists() for name in tools)
archive(owner,'full-preparation')
archive(audit,'full-tools-audit')
for name,path in tools.items():
    (HERE / name).write_bytes(path.read_bytes())
save('root-full-tools-gate.json',dict(status='ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE',
    module=NAME,source_sha256=selected['source_sha256'],source_lines=100,public_heads=['groups_admitted'],
    independent_review_sha256=expected_review,root_complete_selected_tool_lines_read=203,
    root_complete_predecessor_lines_read=201,whole_tool_hard_stop=210,
    installed_tools={name:sha(path) for name,path in tools.items()},diagnostic_tail_lines=14,
    materializer_activation=True,sole_FULL_activation=True,reader_activation_after_actual_FULL=True,
    unchanged_source_FULL_jobs_so_far=0,compiler_outcome_not_claimed=True))
print('ACCEPTED reviewed FULL tools and ordered materializer/FULL/reader activation.')
