# Small independent static model of Rewriting.hs:1095-1114 and Term's lexicographic Ord.
# This does not load or execute any Haskell package or compile a candidate.
from dataclasses import dataclass
from functools import lru_cache
import json
@dataclass(frozen=True,order=True)
class T:
    sym:str
    children:tuple=()
def leaf(s):return T(s)
def arr(a,b):return T('->',(leaf('(->)'),a,b))
def atom(s,ty):return T(s,(ty,))
def app(f,x):
    ty=f.children[0];assert ty.sym=='->' and ty.children[1]==x.children[0]
    return T('app',(ty.children[2],f,x))
def spine(t):
    if t.sym=='app' and len(t.children)==3:
        h,args=spine(t.children[1]);return h,args+(t.children[2],)
    return t,()
precedence=['e','c','f']
def key(s,n):return (precedence.index(s),'',n) if s in precedence else (-1,s,n)
@lru_cache(None)
def greater(a,b):
    f,aa=spine(a);g,bb=spine(b)
    if len(f.children)!=1 or len(g.children)!=1:return False
    def lex(xs,ys):
        for x,y in zip(xs,ys):
            if x==y:continue
            return greater(x,y)
        return False
    return any(x==b or greater(x,b) for x in aa) or (key(f.sym,len(aa))>key(g.sym,len(bb)) and all(greater(a,x) for x in bb)) or (f.sym==g.sym and len(aa)==len(bb) and lex(aa,bb) and all(greater(a,x) for x in bb))
def cmp(a,b):return 0 if a==b else 1 if greater(a,b) else -1 if greater(b,a) else (a>b)-(a<b)
A,B,Bo,Ch,I=map(leaf,['A','B','Bool','Char','Int'])
li=lambda x:T('[]',(x,))
def full(first,second,name):
    f=atom('f',arr(li(first),arr(second,I)))
    return app(app(f,atom('[]',li(first))),atom(name,second))
s=full(A,Bo,'c');t=full(B,Ch,'d');u=full(A,I,'e')
assert all(x.children[0]==I for x in [s,t,u])
assert (cmp(s,t),cmp(t,u),cmp(u,s))==(-1,-1,-1)
result={'model':'Exact small static translation of upstream ground lpoCompare and Data.CFTA.Term Ord; no Haskell execution.','precedence':precedence,'s':'f ([] :: [A]) (c :: Bool)','t':'f ([] :: [B]) (d :: Char)','u':'f ([] :: [A]) (e :: Int)','common_result_type':'Int','signature':'f :: A -> B -> Int; [] :: [A]; c :: Bool; d :: Char; e :: Int','s_lt_t':cmp(s,t)==-1,'t_lt_u':cmp(t,u)==-1,'u_lt_s':cmp(u,s)==-1,'proper_lpo_s_greater_u':greater(s,u),'raw_fallback_s_lt_t':s<t,'raw_fallback_t_lt_u':t<u,'all_application_annotations_checked_by_builder':True}
print(json.dumps(result,indent=2))
