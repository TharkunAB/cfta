from pathlib import Path
import hashlib, json, os, resource, selectors, stat, subprocess, sys, time

R = Path('/tmp/mcfta-runtime-packet-producer-normal-20261104-1205')
JOB = R / 'R79-B418-CAPPED-JOB-BEFORE.json'
PREFIX = R / 'R79-B418-CAPPED'
CAPS = {'stdout': 4096, 'stderr': 8192}

def pin(path):
    p = Path(path)
    a = p.lstat()
    assert p.resolve() == p and stat.S_ISREG(a.st_mode)
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(65536), b''):
            h.update(b)
    z = p.lstat()
    ident = lambda s: [s.st_dev, s.st_ino, s.st_size, stat.S_IMODE(s.st_mode), s.st_mtime_ns, s.st_ctime_ns]
    assert ident(a) == ident(z)
    return {'path': str(p), 'bytes': a.st_size, 'sha256': h.hexdigest(), 'mode': oct(stat.S_IMODE(a.st_mode)), 'identity': ident(a)}

def logical_match(e):
    p=Path(e['logical']);z=p.lstat()
    actual={'logical':e['logical'],'canonical':str(p.resolve()),'is_symlink':p.is_symlink(),'lstat_identity_decimal':list(map(str,[z.st_dev,z.st_ino,z.st_size,z.st_mode,z.st_mtime_ns,z.st_ctime_ns]))}
    return actual==e

def write_json(suffix, value):
    p = Path(str(PREFIX) + suffix)
    assert not p.exists()
    b = (json.dumps(value, separators=(',', ':')) + '\n').encode()
    assert len(b) <= 196608
    p.write_bytes(b)

expected = []
job = {}
result = {'status': 'STOP_BEFORE_HELPER', 'helper_executed': False}
child = None
try:
    assert hashlib.sha256(JOB.read_bytes()).hexdigest() == sys.argv[1]
    job = json.loads(JOB.read_bytes())
    expected = job['controls'] + [pin(JOB)]
    before_observed = {}
    for old in expected:
        if old['path'] not in before_observed:
            before_observed[old['path']] = pin(old['path'])
        assert before_observed[old['path']] == old
    for logical in job['logical_controls']:
        assert logical_match(logical)
    cg = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip().split('::', 1)[1].lstrip('/')
    actual = {n: (cg / n).read_text().strip() for n in ['memory.max', 'memory.high', 'memory.swap.max']}
    assert actual == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    resource.setrlimit(resource.RLIMIT_CPU, (30, 30))
    resource.setrlimit(resource.RLIMIT_FSIZE, (4194304, 4194304))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    write_json('-ACTUAL-CGROUP-BEFORE.json', {'controls': actual, 'cgroup': str(cg), 'inherited_RLIMIT_AS': list(resource.getrlimit(resource.RLIMIT_AS)), 'expected_table_pin': expected[-1], 'expected_layout': 'job.controls followed by own job pin', 'physical_before_count': len(expected), 'all_external_before_PASS': True, 'actual_before_reference': 'Every actual pin equals its indexed expected record', 'SourceProcessFAIL_Root_upperUNKNOWN': 'PERMANENT', 'source_history_before_all_guards': job['history']})
    started = time.monotonic()
    child = subprocess.Popen([sys.executable, job['helper'], *job['helper_args']], stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    result['helper_executed'] = True
    selected = selectors.DefaultSelector()
    buffers = {'stdout': bytearray(), 'stderr': bytearray()}
    for label, pipe in [('stdout', child.stdout), ('stderr', child.stderr)]:
        selected.register(pipe, selectors.EVENT_READ, label)
    while selected.get_map():
        remaining = 30 - (time.monotonic() - started)
        assert remaining > 0, 'WALL_CAP'
        for key, event in selected.select(min(remaining, 0.5)):
            label = key.data
            chunk = os.read(key.fileobj.fileno(), min(4096, CAPS[label] - len(buffers[label]) + 1))
            if not chunk:
                selected.unregister(key.fileobj)
                continue
            assert len(buffers[label]) + len(chunk) <= CAPS[label], 'OUTPUT_CAP_' + label
            buffers[label].extend(chunk)
    code = child.wait(timeout=max(0.1, 30 - (time.monotonic() - started)))
    outputs = {}
    for label, buf in buffers.items():
        p = Path(str(PREFIX) + '.' + label + '.txt')
        assert not p.exists()
        p.write_bytes(buf)
        outputs[label] = pin(p)
    result.update({'status': 'PROCESS_PASS_METADATA_ONLY' if code == 0 else 'STOP_HELPER_EXIT', 'exit': code, 'outputs': outputs})
except BaseException as exc:
    if child is not None and child.poll() is None:
        child.kill()
        child.wait()
    result.update({'status': 'STOP_NO_AUTOFOLLOW', 'exception': type(exc).__name__})
finally:
    def phase():
        observed = {}
        physical = []
        for index, old in enumerate(expected):
            try:
                if old['path'] not in observed:
                    observed[old['path']] = pin(old['path'])
                current = observed[old['path']]
                physical.append(current == old)
            except BaseException:
                physical.append(False)
        logical = []
        for index, old in enumerate(job.get('logical_controls', [])):
            try:
                logical.append(logical_match(old))
            except BaseException:
                logical.append(False)
        return {'physical': physical, 'logical': logical,
                'all_PASS': bool(expected) and all(physical + logical)}
    after = phase()
    final = phase()
    all_pass = after['all_PASS'] and final['all_PASS']
    result['all_external_after_final'] = all_pass
    result['after_and_final_are_distinct_full_passes'] = True
    result['role_link'] = 'UNKNOWN_EVEN_ON_SCHEMA_PASS'
    result['SourceProcessFAIL_Root_upperUNKNOWN'] = 'PERMANENT'
    write_json('-EXTERNAL-FINAL-METADATA-ONLY.json', {
        'all_PASS': all_pass, 'expected_table_pin': expected[-1] if expected else None,
        'expected_layout': 'job.controls followed by own job pin',
        'reference_rule': 'Flag array position is the expected role index; PASS compares actual full tuple; failed actual tuple UNKNOWN',
        'after': after, 'final': final, 'no_payload_retry': True})
    write_json('-RESULT.json', result)
    print(json.dumps({'status': result['status'], 'exit': result.get('exit'),
                     'external_fences_PASS': all_pass, 'external_count': len(expected),
                     'distinct_after_final': True,
                     'stdout_bytes': result.get('outputs', {}).get('stdout', {}).get('bytes'),
                     'role_link': 'UNKNOWN'}))
