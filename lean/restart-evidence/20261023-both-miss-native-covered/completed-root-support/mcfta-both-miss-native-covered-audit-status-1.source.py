import datetime
import re
import runpy
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

stem = 'both-miss-native-covered-audit-1'
receipt = load(HERE / (stem + '.json'))
assert receipt['exit_code'] == 0 and receipt['command'][-2:] == ['build', 'MicroCFTA.Audit']
raw = HERE / (stem + '.log')
text = raw.read_text()
assert 'Build completed successfully (3643 jobs).' in text
assert 'Checked axiom dependencies of 75504 MicroCFTA theorems.' in text
assert sha(raw) == '8f408f71d6d34a931a73666491b71fe7ba54f53384dd99b75a37027312315c95'
assert not re.search(r'\berror(?:\([^)]*\))?:', text)
assert len(re.findall(r'^warning:', text, re.M)) == 1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in text
assert (HERE / 'both-miss-native-covered-strict-1.log').read_bytes() == b''
report = dict(status='PASS', observed_at=datetime.datetime.now().astimezone().isoformat(),
    actual_lean_lake_jobs=3, source_jobs=2, audit_jobs=1, failed_jobs=0,
    warned_source_exit_zero_jobs=0, rejected_public_type_jobs=0,
    audit_build_jobs=3643, audit_dependencies=75504, audit_log_sha256=sha(raw),
    old_replay_warning_only=True, new_source_clean=True, whole_goal_complete=False)
save('root-audit-review.json', report)
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Aggregate Audit passed\n\nAll three actual Lean/Lake commands pass. Strict1 has an empty log.\nThe sole FULL1 and Audit1 pass. Audit has3643 jobs and75504 dependencies.\nOnly the old unused inputs warning is replayed. New source is clean.\nThere are no failed source jobs or rejected public TYPEs.\nThe sole152-line source variant remains; no source repair was needed.\nActual tool binding, standalone checks, proof commit, documents, seal and push remain pending.\nThe whole goal remains ACTIVE.\n')
print(json.dumps(report))
