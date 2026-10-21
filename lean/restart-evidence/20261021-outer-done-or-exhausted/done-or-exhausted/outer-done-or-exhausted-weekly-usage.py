import json,datetime
from pathlib import Path
now=datetime.datetime.now(datetime.timezone.utc)
latest=None
candidates={Path('/home/tritlo/.codex/sessions/2026/10/15/rollout-2026-10-15T10-25-57-01a13eab-04a5-7d13-9f8c-5287118602cc.jsonl')}
for offset in [1,0,-1]:
 root=Path('/home/tritlo/.codex/sessions')/(now+datetime.timedelta(days=offset)).strftime('%Y/%m/%d')
 candidates.update(sorted(root.glob('*.jsonl'),key=lambda p:p.stat().st_mtime,reverse=True)[:8])
for p in sorted(candidates,key=lambda p:p.stat().st_mtime,reverse=True):
 if p.is_file():
  with p.open('rb') as f:
   f.seek(max(0,p.stat().st_size-524288))
   lines=f.read().decode(errors='replace').splitlines()
  for line in reversed(lines):
   try:x=json.loads(line)
   except ValueError:continue
   data=x.get('payload',{})
   if x.get('type')!='event_msg' or data.get('type')!='token_count':continue
   rates=data.get('rate_limits') or {}
   windows=[rates.get(key) for key in ['primary','secondary']]
   weekly=[w for w in windows if w and w.get('window_minutes')==10080]
   if not weekly:continue
   stamp=x.get('timestamp')
   when=datetime.datetime.fromisoformat(stamp.replace('Z','+00:00'))
   result={'observed_at':stamp,'age_seconds':int((now-when).total_seconds()),'remaining_percent':100-weekly[0]['used_percent'],'resets_at':weekly[0]['resets_at']}
   if latest is None or stamp>latest['observed_at']:latest=result
   break
print(json.dumps(latest))
raise SystemExit(0 if latest and latest['age_seconds']<=600 and latest['remaining_percent']>1 else 2)
