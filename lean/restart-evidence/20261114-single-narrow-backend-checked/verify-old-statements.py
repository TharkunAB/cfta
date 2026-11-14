from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
runtime = Path(__file__).parent


def headers(text):
    starts = list(re.finditer(r'^(?:(?:private|protected)\s+)?theorem\s+(\S+)\b', text, re.M))
    result = []
    for number, match in enumerate(starts):
        end = starts[number + 1].start() if number + 1 < len(starts) else len(text)
        segment = text[match.start():end]
        stack = []
        block = 0
        quoted = False
        escaped = False
        line_comment = False
        pairs = {'(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄'}
        index = 0
        while index < len(segment) - 1:
            char, two = segment[index], segment[index:index + 2]
            if line_comment:
                line_comment = char != '\n'
            elif block:
                if two == '/-':
                    block += 1
                    index += 1
                elif two == '-/':
                    block -= 1
                    index += 1
            elif quoted:
                if escaped:
                    escaped = False
                elif char == '\\':
                    escaped = True
                elif char == '"':
                    quoted = False
            elif two == '--':
                line_comment = True
                index += 1
            elif two == '/-':
                block = 1
                index += 1
            elif char == '"':
                quoted = True
            elif char in pairs:
                stack.append(pairs[char])
            elif stack and char == stack[-1]:
                stack.pop()
            elif two == ':=' and not stack:
                result.append((match.group(1), segment[:index + 2]))
                break
            index += 1
        else:
            raise AssertionError(('header boundary not found', match.group(1)))
    assert len(starts) == len(result)
    return result


names = subprocess.check_output(
    ['git', 'diff', '--name-only', 'HEAD', '--', 'lean/MicroCFTA'], cwd=root, text=True).splitlines()
results = []
for name in names:
    before = subprocess.check_output(['git', 'show', 'HEAD:' + name], cwd=root, text=True)
    after = (root / name).read_text()
    old, new = headers(before), headers(after)
    remaining = iter(new)
    assert all(any(candidate == header for candidate in remaining) for header in old), name
    results.append({'file': name, 'source_sha256': hashlib.sha256(after.encode()).hexdigest(),
                    'old_theorem_headers': len(old), 'new_theorem_headers': [header[0] for header in new if header not in old]})
report = {'baseline': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
          'method': 'Each declaration ends at its first top-level assignment; nested assignments and comments are skipped.',
          'headers_preserved': sum(item['old_theorem_headers'] for item in results), 'files': results}
(runtime / 'all-old-theorem-headers-check.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'changed_modules': len(names), 'old_headers_preserved': report['headers_preserved'],
                  'new_laws': [item for item in results if item['new_theorem_headers']]}))
