#!/usr/bin/env python3
"""Explicit checks of rejected alarms, not library defect counterexamples.

No Lean source is executed. None is represented by -1; larger rank is better.
Each assertion is for one fully enumerated finite instance only.
"""
import json


def proposal(pm, pairs, rejected):
    return {(m, max([-1] + [w for mm, w in pairs
                            if mm == m and (m, w) not in rejected], key=p.get))
            for m, p in enumerate(pm)} - {(m, -1) for m in range(len(pm))}


def held(pw, offers):
    return {(max([-1] + [m for m, ww in offers if ww == w], key=p.get), w)
            for w, p in enumerate(pw)} - {(-1, w) for w in range(len(pw))}


def step(pm, pw, pairs, rejected):
    offers = proposal(pm, pairs, rejected)
    return rejected | (offers - held(pw, offers))


def main():
    records = []
    pairs = {(0, 0)}
    pm, pw = [{-1: 0, 0: 1}], [{-1: 0, 0: 1}]
    assert step(pm, pw, pairs, pairs) == pairs
    assert held(pw, proposal(pm, pairs, pairs)) == set()
    assert pm[0][0] > pm[0][-1] and pw[0][0] > pw[0][-1]
    assert step(pm, pw, pairs, set()) == set()
    assert held(pw, proposal(pm, pairs, set())) == pairs
    records.append({"alarm": "arbitrary terminal history need not be stable",
                    "verified": True, "library_defect": False,
                    "reason": "stable_gsMatchingAt requires reachable gsRejected n"})

    pairs = {(0, 0), (0, 1)}
    pm, pw = [{-1: 0, 1: 1, 0: 2}], [{0: 0, -1: 1}, {-1: 0, 0: 1}]
    assert proposal(pm, pairs, set()) == {(0, 0)}
    assert held(pw, proposal(pm, pairs, set())) == set()
    assert pm[0][1] > pm[0][-1] and pw[1][0] > pw[1][-1]
    r1 = step(pm, pw, pairs, set())
    assert r1 == {(0, 0)} and held(pw, proposal(pm, pairs, r1)) == {(0, 1)}
    records.append({"alarm": "zero fuel may return an unstable holding",
                    "verified": True, "library_defect": False,
                    "reason": "WithFuel explicitly permits stopping before stabilization"})

    pairs = {(0, 0), (1, 0)}
    pm, pw = [{-1: 0, 0: 1}, {-1: 0, 0: 1}], [{-1: 0, 0: 1, 1: 2}]
    r, s = set(), {(1, 0)}
    assert r <= s
    assert step(pm, pw, pairs, r) == {(0, 0)}
    assert step(pm, pw, pairs, s) == {(1, 0)}
    assert not step(pm, pw, pairs, r) <= step(pm, pw, pairs, s)
    records.append({"alarm": "gsStep need not be monotone in arbitrary histories",
                    "verified": True, "library_defect": False,
                    "reason": "termination uses inflationarity, not monotonicity"})

    # Generalized operator from Contracts.StableFixedPoints: a contract is
    # accepted by its agent from the current coordinate with itself inserted.
    # In this example both men have only one acceptable woman, so every pair
    # is always in toBuyers(A). Women initially see only an inserted singleton.
    a1 = {(m, w) for m, w in pairs
          if pw[w][m] > pw[w][-1]}
    b1 = {(m, w) for m, w in pairs
          if pm[m][w] > pm[m][-1]}
    assert a1 & b1 == pairs
    assert len({m for m, w in a1 & b1 if w == 0}) == 2
    records.append({"alarm": "intermediate generalized outcome may not be a matching",
                    "verified": True, "library_defect": False,
                    "reason": "outcomes are Set contracts; only terminal outputs are asserted stable"})
    print(json.dumps({"result": "PASS", "source_execution": False,
                      "records": records}, indent=2))


if __name__ == "__main__":
    main()
