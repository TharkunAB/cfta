"""Compare #10's search (states) with the automaton path (automaton) on the timing runs."""
import sys, re, os
S = sys.argv[1]
def ghc(path):
    rows, figs = {}, {}
    for line in open(path):
        f = line.rstrip('\n').split(',')
        if f[0] == 'result' and f[1] != 'query': rows[f[1]] = f
        elif f[0] == 'figures': figs[f[1]] = {k: int(v) for k, v in re.findall(r'(\w+) = (-?\d+)', line)}
    return rows, figs
def lean(path):
    rows, figs = {}, {}
    for line in open(path):
        f = line.rstrip('\n').split(',')
        if f[0] == 'result' and f[1] != 'query': rows[f[1]] = f
        elif f[0] == 'figures': figs[f[1]] = {k: int(v) for k, v in re.findall(r'(\w+) = (-?\d+)', line)}
    return rows, figs
def report(name, a, b, cols):
    (ra, fa), (rb, fb) = a, b
    sa = {q for q, f in ra.items() if f[3] == 'solved'}; sb = {q for q, f in rb.items() if f[3] == 'solved'}
    both = sorted(sa & sb)
    t = lambda r, q: float(r[q][cols['seconds']])
    print(f"== {name}: solved states {len(sa)}, automaton {len(sb)}; only states {sorted(sa - sb)}, only automaton {sorted(sb - sa)}")
    print(f"   seconds on the {len(both)} both solve: states {sum(t(ra, q) for q in both):.1f}, automaton {sum(t(rb, q) for q in both):.1f} ({100 * sum(t(rb, q) for q in both) / max(sum(t(ra, q) for q in both), 1e-9) - 100:+.1f}%)")
    same_first = [q for q in ra if q in rb and ra[q][cols['first']] == rb[q][cols['first']] and ra[q][cols['firstFit']] == rb[q][cols['firstFit']]]
    same_rank = [q for q in both if cols.get('rank') is None or ra[q][cols['rank']] == rb[q][cols['rank']]]
    print(f"   same first fit on {len(same_first)} of {len(ra)}; same rank on {len(same_rank)} of {len(both)}")
    for key in ('figuresRefinements', 'figuresStates'):
        print(f"   {key}: states {sum(f.get(key, 0) for f in fa.values())}, automaton {sum(f.get(key, 0) for f in fb.values())}")
    if 'calls' in cols:
        c = lambda r, q: int(r[q][cols['calls']]) if r[q][cols['calls']] not in ('-', '') else 0
        print(f"   solver calls on both solved: states {sum(c(ra, q) for q in both)}, automaton {sum(c(rb, q) for q in both)}")
    p = lambda r, q: int(r[q][cols['programs']]) if r[q][cols['programs']] not in ('-', '') else 0
    print(f"   programs checked on both solved: states {sum(p(ra, q) for q in both)}, automaton {sum(p(rb, q) for q in both)}; automaton count {sum(f.get('figuresCount', 0) for f in fb.values())}")
    worst = sorted(both, key=lambda q: t(rb, q) - t(ra, q))[-5:]
    print("   largest slowdowns:", [(q, round(t(ra, q), 2), round(t(rb, q), 2)) for q in worst])
ghc_cols = {'seconds': 11, 'first': 5, 'firstFit': 18, 'rank': 7, 'calls': 10, 'programs': 9}
lean_cols = {'seconds': 13, 'first': 5, 'firstFit': 19, 'programs': 7}
for rung in ('prelude', 'base'):
    a, b = f'{S}/ghc-states-{rung}.csv', f'{S}/ghc-automaton-{rung}.csv'
    if os.path.exists(a) and os.path.exists(b): report(f'GHC {rung}', ghc(a), ghc(b), ghc_cols)
for rung in ('core', 'sweep'):
    a, b = f'{S}/lean-states-{rung}.out', f'{S}/lean-automaton-{rung}.out'
    if os.path.exists(a) and os.path.exists(b): report(f'Lean {rung}', lean(a), lean(b), lean_cols)
