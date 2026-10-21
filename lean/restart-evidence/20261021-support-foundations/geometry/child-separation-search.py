"""Search finite actual-normalization fixed points and prefix replacements."""
import itertools
import json


def prefix(first, second):
    return second[:len(first)] == first


def complete(classes):
    parts = []
    for paths in classes:
        current = set(paths)
        changed = True
        while changed:
            changed = False
            rest = []
            for old in parts:
                if current & old:
                    current |= old
                    changed = True
                else:
                    rest.append(old)
            parts = rest
        if len(current) > 1:
            parts.append(current)
    return tuple(sorted(tuple(sorted(paths)) for paths in parts))


def contradicts(classes):
    return any(a != b and prefix(a, b) for paths in classes for a in paths for b in paths)


def step(classes):
    members = set(itertools.chain.from_iterable(classes))
    added = list(classes)
    for paths in classes:
        suffixes = {extension[len(base):] for base in paths for extension in members
                    if base != extension and prefix(base, extension)}
        added.extend(tuple(base + suffix for base in paths) for suffix in suffixes)
    closed = complete(added)
    return None if contradicts(closed) else closed


def normalize(classes):
    current = complete(classes)
    for _ in range(32):
        if sum(map(len, current)) > 256 or any(len(p) > 12 for c in current for p in c):
            return 'skipped'
        changed = step(current)
        if changed is None:
            return None
        if changed == current:
            return current
        current = changed
    return 'skipped'


def partitions(values):
    if not values:
        yield []
        return
    for rest in partitions(values[1:]):
        yield [[values[0]]] + rest
        for i in range(len(rest)):
            yield rest[:i] + [[values[0]] + rest[i]] + rest[i + 1:]


def words(bound):
    return [p for length in range(bound + 1) for p in itertools.product(range(2), repeat=length)]


def investigate(classes):
    assert step(classes) == classes
    assert not contradicts(classes)
    assert all(len(c) > 1 and all(p for p in c) for c in classes)
    maximum = min(8, max((len(p) for c in classes for p in c), default=0) + 3)
    universe = words(maximum)
    parents = {p: p for p in universe}
    direct = {p: {p} for p in universe}

    def find(p):
        while parents[p] != p:
            parents[p] = parents[parents[p]]
            p = parents[p]
        return p

    for paths in classes:
        for a, b in itertools.combinations(paths, 2):
            for suffix in words(maximum - max(len(a), len(b))):
                left, right = a + suffix, b + suffix
                parents[find(left)] = find(right)
                direct[left].add(right)
                direct[right].add(left)
    components = {}
    for p in universe:
        components.setdefault(find(p), []).append(p)
    for paths in components.values():
        for p in paths:
            if not set(paths).issubset(direct[p]):
                q = next(q for q in paths if q not in direct[p])
                return {'kind': 'one_replacement_not_transitive', 'classes': classes,
                        'left': p, 'right': q, 'maximum_intermediate_length': maximum}
    checked_children = 0
    for child in range(2):
        if not all(sum(p[0] == child for p in paths) <= 1 for paths in classes):
            continue
        checked_children += 1
        for paths in components.values():
            local = [p for p in paths if p and p[0] == child]
            if len(local) > 1:
                return {'kind': 'child_separation_counterexample', 'classes': classes,
                        'child': child, 'left': local[0], 'right': local[1],
                        'maximum_intermediate_length': maximum}
    return checked_children


def main():
    small = words(2)[1:]
    pairs = list(itertools.combinations(words(3)[1:], 2))
    cases = itertools.chain((p for p in partitions(small)), ((p,) for p in pairs),
                            itertools.combinations(pairs, 2))
    fixed = set()
    counts = {'raw_inputs': 0, 'contradictory': 0, 'normalization_skipped': 0,
              'unique_fixed_points': 0, 'all_drop_child_checks': 0}
    for case in cases:
        counts['raw_inputs'] += 1
        result = normalize(case)
        if result is None:
            counts['contradictory'] += 1
        elif result == 'skipped':
            counts['normalization_skipped'] += 1
        else:
            fixed.add(result)
    for classes in sorted(fixed):
        outcome = investigate(classes)
        counts['unique_fixed_points'] += 1
        if isinstance(outcome, dict):
            print(json.dumps({'result': 'COUNTEREXAMPLE', 'counts': counts,
                              'witness': outcome}, sort_keys=True))
            return
        counts['all_drop_child_checks'] += outcome
    print(json.dumps({'result': 'NO_COUNTEREXAMPLE_IN_ENUMERATED_DOMAIN', 'counts': counts,
                      'alphabet': [0, 1], 'raw_domains': ['all partitions of proper paths of length <=2',
                      'one or two pair equations over proper paths of length <=3'],
                      'relation_path_bound': 'min(8, max_recorded_path_length + 3)',
                      'proof_status': 'independent Python finite search; no Lean theorem'}, sort_keys=True))


if __name__ == '__main__':
    main()
