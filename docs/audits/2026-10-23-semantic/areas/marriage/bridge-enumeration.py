#!/usr/bin/env python3
"""Exact finite semantic checks for the classical-marriage contracts bridge.

Independent integer/set model; does not call or interpret Lean. Every strict
ranking over partners and the outside option (-1) is enumerated for each
population size 0 <= men,women <= 2. No general theorem is inferred.
"""

from itertools import permutations, product
import json


def powerset(xs):
    return [frozenset(x for i, x in enumerate(xs) if mask >> i & 1)
            for mask in range(1 << len(xs))]


def assignments(A, nm, nw):
    return ([next((w for m1, w in A if m1 == m), -1) for m in range(nm)],
            [next((m for m, w1 in A if w1 == w), -1) for w in range(nw)])


def partial(A):
    return (len({m for m, _ in A}) == len(A)
            and len({w for _, w in A}) == len(A))


def run_size(nm, nw):
    X = [(m, w) for m in range(nm) for w in range(nw)]
    sets = powerset(X)
    matchings = [A for A in sets if partial(A)]
    partners = {A: assignments(A, nm, nw) for A in matchings}
    ranks_m = [dict(zip(p, range(nw + 1)))
               for p in permutations(range(-1, nw))]
    ranks_w = [dict(zip(p, range(nm + 1)))
               for p in permutations(range(-1, nm))]
    counts = dict(markets=0, outcomes=0, matching_pairs=0,
                  stable_pairs=0, stable_triples=0)
    for rm in product(ranks_m, repeat=nm):
        for rw in product(ranks_w, repeat=nw):
            counts['markets'] += 1

            # Literal set comprehension in mem_inducedChoiceM/W_iff.
            cm = {(m, Y): frozenset((m, w) for m1, w in Y
                    if m1 == m and rm[m][-1] <= rm[m][w]
                    and all(rm[m][w1] <= rm[m][w]
                            for m2, w1 in Y if m2 == m))
                  for m in range(nm) for Y in sets}
            cw = {(w, Y): frozenset((m, w) for m, w1 in Y
                    if w1 == w and rw[w][-1] <= rw[w][m]
                    and all(rw[w][m1] <= rw[w][m]
                            for m1, w2 in Y if w2 == w))
                  for w in range(nw) for Y in sets}

            def irm(A):
                a, _ = partners[A]
                return all(rm[m][-1] <= rm[m][a[m]] for m in range(nm))

            def irw(A):
                _, a = partners[A]
                return all(rw[w][-1] <= rw[w][a[w]] for w in range(nw))

            def classical_stable(A):
                a, b = partners[A]
                return irm(A) and irw(A) and not any(
                    rm[m][a[m]] < rm[m][w]
                    and rw[w][b[w]] < rw[w][m] for m, w in X)

            def contracts_ir(A):
                return (all(cm[m, A] == frozenset(x for x in A if x[0] == m)
                            for m in range(nm))
                        and all(cw[w, A] == frozenset(x for x in A if x[1] == w)
                                for w in range(nw)))

            def blocks(A, Z):
                return bool(Z) and not A & Z and all(
                    (m, w) in cm[m, A | Z] and (m, w) in cw[w, A | Z]
                    for m, w in Z)

            def contracts_stable(A):
                return contracts_ir(A) and not any(blocks(A, Z) for Z in sets)

            def men(A, B):
                a, _ = partners[A]
                b, _ = partners[B]
                return all(rm[m][b[m]] <= rm[m][a[m]] for m in range(nm))

            def women(A, B):
                _, a = partners[A]
                _, b = partners[B]
                return all(rw[w][b[w]] <= rw[w][a[w]] for w in range(nw))

            def seller(A, B):
                return all(cm[m, A | B] == frozenset(x for x in A if x[0] == m)
                           for m in range(nm))

            def buyer(A, B):
                return all(cw[w, A | B] == frozenset(x for x in A if x[1] == w)
                           for w in range(nw))

            for A in sets:
                counts['outcomes'] += 1
                if contracts_ir(A):
                    # Includes off-matching sets, testing exact carrier recovery.
                    assert partial(A), (nm, nw, rm, rw, A, 'IR not partial')
                if A in partners:
                    assert contracts_ir(A) == (irm(A) and irw(A))
                    assert contracts_stable(A) == classical_stable(A)
                    if irm(A) and irw(A):
                        a, b = partners[A]
                        for m, w in X:
                            assert blocks(A, frozenset({(m, w)})) == (
                                rm[m][a[m]] < rm[m][w]
                                and rw[w][b[w]] < rw[w][m])

            stable = [A for A in matchings if classical_stable(A)]
            assert stable, (nm, nw, rm, rw, 'no stable matching')
            for A, B in product(matchings, repeat=2):
                counts['matching_pairs'] += 1
                assert seller(A, B) == (irm(A) and men(A, B))
                assert buyer(A, B) == (irw(A) and women(A, B))
            for A, B in product(stable, repeat=2):
                counts['stable_pairs'] += 1
                assert men(A, B) == women(B, A)
                # Invariance of unmatched agents on both sides.
                a, b = partners[A]
                aa, bb = partners[B]
                assert [x == -1 for x in a] == [x == -1 for x in aa]
                assert [x == -1 for x in b] == [x == -1 for x in bb]
            max_m = [A for A in stable if all(men(A, B) for B in stable)]
            min_m = [A for A in stable if all(men(B, A) for B in stable)]
            max_w = [A for A in stable if all(women(A, B) for B in stable)]
            min_w = [A for A in stable if all(women(B, A) for B in stable)]
            assert len(max_m) == len(min_m) == len(max_w) == len(min_w) == 1
            assert max_m == min_w and min_m == max_w
            for A, B in product(stable, repeat=2):
                # Join/meet under A <= B iff men weakly prefer B to A.
                uppers = [C for C in stable if men(C, A) and men(C, B)]
                lowers = [C for C in stable if men(A, C) and men(B, C)]
                joins = [C for C in uppers if all(men(D, C) for D in uppers)]
                meets = [C for C in lowers if all(men(C, D) for D in lowers)]
                assert len(joins) == len(meets) == 1
                for C in stable:
                    counts['stable_triples'] += 1
                    assert men(C, joins[0]) == (men(C, A) and men(C, B))
                    assert women(C, meets[0]) == (women(C, A) and women(C, B))
    return counts


if __name__ == '__main__':
    result = {f'{nm}x{nw}': run_size(nm, nw)
              for nm in range(3) for nw in range(3)}
    result['scope'] = ('All strict preferences including outside-option positions; '
                       'all populations 0 through 2 on each side; exact finite '
                       'enumeration only, not proof of the Lean definitions.')
    print(json.dumps(result, indent=2, sort_keys=True))
