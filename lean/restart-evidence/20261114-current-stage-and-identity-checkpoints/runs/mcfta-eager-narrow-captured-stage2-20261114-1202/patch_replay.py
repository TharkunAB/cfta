import re
def replay(source,patch,reverse=False):
 original=source.splitlines(keepends=True);out=[];cursor=0;rows=patch.splitlines(keepends=True);i=0
 while i<len(rows):
  m=re.match(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',rows[i])
  if not m:i+=1;continue
  olda,oldn,newa,newn=int(m[1]),int(m[2] or 1),int(m[3]),int(m[4] or 1)
  start=(newa if reverse else olda)-1;assert cursor<=start
  out.extend(original[cursor:start]);cursor=start;i+=1;consumed=0;produced=0
  while i<len(rows) and not rows[i].startswith(('@@ ','--- ','+++ ')):
   row=rows[i];kind=row[:1];body=row[1:]
   assert kind in [' ','-','+']
   consume=kind==' ' or (kind=='+' if reverse else kind=='-')
   emit=kind==' ' or (kind=='-' if reverse else kind=='+')
   if consume:assert original[cursor]==body;cursor+=1;consumed+=1
   if emit:out.append(body);produced+=1
   i+=1
  assert consumed==(newn if reverse else oldn)
  assert produced==(oldn if reverse else newn)
 out.extend(original[cursor:]);return ''.join(out)
