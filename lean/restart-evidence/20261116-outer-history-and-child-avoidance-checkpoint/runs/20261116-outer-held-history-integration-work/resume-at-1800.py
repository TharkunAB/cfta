from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
target = datetime(2026, 11, 16, 18, 0, tzinfo=ZoneInfo('Europe/Stockholm'))
now = datetime.now(ZoneInfo('Europe/Stockholm'))
if now < target:
    raise SystemExit('The requested pause has not expired.')

marker = work / 'SCHEDULED-RESUME-STARTED.json'
with marker.open('x') as output:
    json.dump({'at': now.isoformat(), 'requested_at': target.isoformat()}, output)

prompt = '''Matti explicitly requested: "I need to run some benchmarks. Pause the work for now and resume at 2026-11-16 18:00. If it's already past that, ignore this message."
This is the scheduled resumption at or after 18:00 Europe/Stockholm on 2026-11-16.
Continue the SAME existing cfta formalization goal in /home/tritlo/Code/mcfta. Do not create a new goal or reduce its full scope. Read the pause prefix in NEXT-PROMPT.md, HANDOFF.md and FINDINGS.md and the Work21 pause record first. The timed pause has expired. Verify current host time, worktree, upstream and actual process state before work.
Latest verified/pushed checkpoint is2411688c with Source df642fe. New normal Prefix module and Audit edit remain UNCOMMITTED, with publication gates pending. Prefix, row/scan and opaque381 modules individually pass. Repaired full-chain check7985 is TERMINAL exit1 with ONE remaining expand-case error. A NEW final outer-only repair bc7f93a5 is frozen but UNCOMPILED. Test that at original budgets before any proof claim. Preserve all frozen attempts, headers and source pins. The original906/full outer statement and one joint finite historical model remain OPEN until proper checks pass. See PAUSE-UNTIL-1800.json for exact paths/hashes.
Keep all builds/checks serial under /home/tritlo/Code/heavy-management, 8GiB and zero swap, original proof/runtime limits. No benchmark work before the requested time. Keep /tmp bounded; preserve all source/logs/live outputs/public caches/unknown entries. Record EVERY Haskell fix in FINDINGS.md. Pushing origin/formalize remains explicitly authorized; fork/Liquid-Haskell changes were cancelled. Pause and notify Matti if primary usage exceeds80%. Timestamp every human-facing message. Respect any later human instruction that changes or cancels this scheduled resumption.
'''
with (work / 'scheduled-resume.log').open('w') as log:
    result = subprocess.run(
        ['/home/tritlo/.npm-global/bin/codex', 'exec', 'resume',
         '01a13eab-04a5-7d13-9f8c-5287118602cc', '-'],
        input=prompt, text=True, cwd=root, stdout=log, stderr=subprocess.STDOUT)
(work / 'SCHEDULED-RESUME-RESULT.json').write_text(
    json.dumps({'exit': result.returncode, 'at': datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()}, indent=2) + '\n')
raise SystemExit(result.returncode)
