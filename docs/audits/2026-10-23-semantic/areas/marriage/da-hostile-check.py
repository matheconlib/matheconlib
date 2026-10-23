#!/usr/bin/env python3
"""Bounded independent check of the classical rejection-set DA recurrence.

Ranks increase with desirability; -1 is the outside option.  This is exact
finite enumeration, not a Lean execution or evidence for unenumerated sizes.
The literal set recurrence is compared with an independent queue/list
implementation, a partial-matching stability oracle, and all stable partial
matchings for proposer optimality.  No claim is inferred from arbitrary
rejection histories: only states reached from the empty rejection history
are tested as algorithm outputs.
"""

import itertools
import json
from pathlib import Path


def rankings(n):
    return [dict(zip(p, range(n + 1)))
            for p in itertools.permutations(range(-1, n))]


def rejection_set_da(pm, pw):
    """Literal gsProposals/gsHeld/gsStep recurrence; return final holdings."""
    nm, nw = len(pm), len(pw)
    rejected = set()
    for step in range(nm * nw + 1):
        proposals = {
            (m, max([-1] + [w for w in range(nw)
                           if (m, w) not in rejected], key=pm[m].get))
            for m in range(nm)
        }
        proposals = {p for p in proposals if p[1] != -1}
        held = {
            (max([-1] + [m for m, v in proposals if v == w], key=pw[w].get), w)
            for w in range(nw)
        }
        held = {p for p in held if p[0] != -1}
        assert held <= proposals
        next_rejected = rejected | (proposals - held)
        if next_rejected == rejected:
            return held, step
        rejected = next_rejected
    raise AssertionError("card(M x W) rejection-update bound failed")


def queue_da(pm, pw):
    """Independent classical algorithm: free-proposer queue and consumed lists."""
    nm, nw = len(pm), len(pw)
    lists = [
        [w for w in sorted(range(nw), key=pm[m].get, reverse=True)
         if pm[m][w] > pm[m][-1]]
        for m in range(nm)
    ]
    held = {}
    free = list(range(nm))
    while free:
        m = free.pop(0)
        if not lists[m]:
            continue
        w = lists[m].pop(0)
        old = held.get(w, -1)
        if pw[w][m] > pw[w][old]:
            held[w] = m
            if old != -1:
                free.append(old)
        else:
            free.append(m)
    return {(m, w) for w, m in held.items()}


def partial_matchings(nm, nw):
    return [
        {(m, w) for m, w in enumerate(a) if w != -1}
        for a in itertools.product(range(-1, nw), repeat=nm)
        if len([w for w in a if w != -1]) == len({w for w in a if w != -1})
    ]


def stable(held, pm, pw):
    mu = dict(held)
    inv = {w: m for m, w in held}
    if len(mu) != len(held) or len(inv) != len(held):
        return False
    if any(pm[m][w] < pm[m][-1] or pw[w][m] < pw[w][-1] for m, w in held):
        return False
    return not any(
        pm[m][w] > pm[m][mu.get(m, -1)] and
        pw[w][m] > pw[w][inv.get(w, -1)]
        for m in range(len(pm)) for w in range(len(pw))
    )


def proposer_dominates(held, alternative, pm):
    mu, nu = dict(held), dict(alternative)
    return all(pm[m][mu.get(m, -1)] >= pm[m][nu.get(m, -1)]
               for m in range(len(pm)))


def positive_controls():
    # A mutually acceptable pair blocks the empty matching.
    acceptable = [{-1: 0, 0: 1}]
    assert not stable(set(), acceptable, acceptable)
    assert stable({(0, 0)}, acceptable, acceptable)
    assert queue_da(acceptable, acceptable) == {(0, 0)}
    # An unacceptable assignment fails IR even though no unmatched pair exists.
    unacceptable = [{0: 0, -1: 1}]
    assert not stable({(0, 0)}, acceptable, unacceptable)
    assert queue_da(acceptable, unacceptable) == set()
    assert rejection_set_da(acceptable, unacceptable) == (set(), 1)
    # Two stable matchings: stability alone cannot distinguish proposer optimality.
    pm = [{-1: 0, 1: 1, 0: 2}, {-1: 0, 0: 1, 1: 2}]
    pw = [{-1: 0, 0: 1, 1: 2}, {-1: 0, 1: 1, 0: 2}]
    diagonal = {(0, 0), (1, 1)}
    off_diagonal = {(0, 1), (1, 0)}
    assert stable(diagonal, pm, pw) and stable(off_diagonal, pm, pw)
    assert proposer_dominates(diagonal, off_diagonal, pm)
    assert not proposer_dominates(off_diagonal, diagonal, pm)
    assert queue_da(pm, pw) == diagonal
    assert rejection_set_da(pm, pw) == (diagonal, 0)
    return ["blocking-pair detection", "unacceptable-assignment detection",
            "recipient outside option rejection", "two-stable-matching optimality separation"]


def main():
    controls = positive_controls()
    results = []
    for nm, nw in [(0, 0), (0, 2), (2, 0), (1, 1), (1, 2), (2, 1),
                   (2, 2), (2, 3), (3, 2)]:
        count, max_round = 0, 0
        matchings = partial_matchings(nm, nw)
        for pm in itertools.product(rankings(nw), repeat=nm):
            for pw in itertools.product(rankings(nm), repeat=nw):
                held, rounds = rejection_set_da(pm, pw)
                max_round = max(max_round, rounds)
                assert held == queue_da(pm, pw), (nm, nw, pm, pw, held)
                assert stable(held, pm, pw), (nm, nw, pm, pw, held)
                for alternative in matchings:
                    if stable(alternative, pm, pw):
                        assert proposer_dominates(held, alternative, pm)
                count += 1
        results.append({"men": nm, "women": nw, "strict_profiles": count,
                        "max_rejection_updates": max_round,
                        "queue_agreement": True, "stable": True,
                        "proposer_optimal": True})
    result = {"status": "passed", "positive_controls": controls,
              "total_profiles": sum(r["strict_profiles"] for r in results),
              "outside_option": "-1, included at every possible rank",
              "scope": "Exact bounded enumeration; not a general proof or Lean execution",
              "results": results}
    output = Path(__file__).with_name("da-hostile-result.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
