"""Stage a candidate annotation. Do not run a compiler or change Original."""
import hashlib
import json
import os
import stat

CACHE = '/tmp/mcfta-haskell-activation-carrier-20261104/source-inputs-stage1/cfta/src/Data/CFTA/Enumeration.hs'
SHA = '83e394d6b9283a607ef1e31346d58e32bf1bc147e67291da0b51ec9de521da91'
IDENTITY = [2096, 1393586, 71748, 33204, 1793303702081610140, 1793781489945486190]
ALIAS = b'CFTAProbePrimitiveInt515'
IMPORT = b'import qualified GHC.Types as ' + ALIAS + b'\n'
CALLS = [(43282, 43300), (69043, 69064)]
OUT = '/tmp/mcfta-runtime-packet-producer-normal-20261104-1205/R84-INT515-CANDIDATE'


def identity(s):
    return [s.st_dev, s.st_ino, s.st_size, s.st_mode, s.st_mtime_ns, s.st_ctime_ns]


def read_cache():
    s = os.lstat(CACHE)
    assert stat.S_ISREG(s.st_mode) and identity(s) == IDENTITY
    assert os.path.realpath(CACHE) == CACHE
    chunks, remaining = [], s.st_size
    with open(CACHE, 'rb') as handle:
        assert identity(os.fstat(handle.fileno())) == IDENTITY
        while remaining:
            block = handle.read(min(131072, remaining))
            assert block
            chunks.append(block)
            remaining -= len(block)
        assert identity(os.fstat(handle.fileno())) == IDENTITY
    assert identity(os.lstat(CACHE)) == IDENTITY
    raw = b''.join(chunks)
    assert hashlib.sha256(raw).hexdigest() == SHA
    return raw


def transform(raw, choice):
    assert len(raw) == 71748 and hashlib.sha256(raw).hexdigest() == SHA
    assert ALIAS not in raw
    assert choice in ('int', 'unit')
    annotation = ALIAS + b'.Int' if choice == 'int' else b'()'
    inserts = [(3510, IMPORT), (11587, b'('), (11601, b' :: ' + annotation + b')')]
    pieces, edits, original_cursor, shift = [], [], 0, 0
    for position, insertion in inserts:
        assert original_cursor <= position <= len(raw)
        pieces.extend((raw[original_cursor:position], insertion))
        edits.append({'original_offset': position, 'staged_halfopen': [position + shift, position + shift + len(insertion)]})
        original_cursor, shift = position, shift + len(insertion)
    staged = b''.join(pieces) + raw[original_cursor:]
    recovered = staged
    for edit in reversed(edits):
        start, end = edit['staged_halfopen']
        recovered = recovered[:start] + recovered[end:]
    assert recovered == raw
    calls = []
    for start, end in CALLS:
        mapped = [start + sum(len(x) for p, x in inserts if p <= start),
                  end + sum(len(x) for p, x in inserts if p < end)]
        assert staged[mapped[0]:mapped[1]] == raw[start:end]
        calls.append({'original_halfopen': [start, end], 'staged_halfopen': mapped, 'bytes_equal': True})
    return staged, {'insertion_edits': edits, 'all_original_bytes_recovered': True,
                    'key_calls': calls, 'fresh_qualification_absent_in_original': True}


def main():
    result = {'status': 'STOP', 'Source_API_TYPE_compiler_accepted': False}
    payloads = {}
    try:
        raw = read_cache()
        result.update(status='STAGED_CANDIDATE_ONLY', source_sha256=SHA,
                      clones={})
        for choice in ('int', 'unit'):
            staged, proof = transform(raw, choice)
            result['clones'][choice] = {'bytes': len(staged),
                'sha256': hashlib.sha256(staged).hexdigest(), 'mapping': proof}
            payloads['.' + choice + '.PRIVATE-Enumeration.hs'] = staged
    except Exception as exc:
        payloads = {}
        result['status'] = 'STOP'
        result['exception_kind'] = type(exc).__name__
    finally:
        try:
            assert identity(os.lstat(CACHE)) == IDENTITY
            result['cache_final_identity_equal'] = True
        except Exception as exc:
            result['cache_final_identity_equal'] = False
            result['exception_kind'] = type(exc).__name__
            result['status'] = 'STOP'
            payloads = {}
    payloads['.metadata.json'] = (json.dumps(result, separators=(',', ':')) + '\n').encode()
    assert all(len(data) <= 131072 for suffix, data in payloads.items() if suffix.endswith('.hs'))
    assert len(payloads['.metadata.json']) <= 4096
    assert all(not os.path.lexists(OUT + suffix) for suffix in payloads)
    for suffix, data in payloads.items():
        with open(OUT + suffix, 'xb') as handle:
            handle.write(data)
    print(json.dumps({'status': result['status'], 'compiler_runs': 0}))
    return 0 if result['status'] == 'STAGED_CANDIDATE_ONLY' else 1


if __name__ == '__main__':
    raise SystemExit(main())
