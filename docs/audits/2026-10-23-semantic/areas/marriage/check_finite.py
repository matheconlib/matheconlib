#!/usr/bin/env python3
"""Bounded semantic check, not a proof of the general Lean implementation.

Encode exactly the declared strict orders on optional partners: -1 is none,
larger numeric rank is preferred, and all permutations are enumerated.
The source rejection-set recurrence is compared with the conventional sequential
deferred-acceptance procedure and all injective optional assignment vectors.
No Lean source is executed, and no compilation claim is made.
"""

import itertools
import json


def orders(size):
    return [dict(zip(p, range(size + 1)))
            for p in itertools.permutations(range(-1, size))]


def assignments(n, k):
    for mu in itertools.product(range(-1, k), repeat=n):
        used = [w for w in mu if w != -1]
        if len(used) == len(set(used)):
            yield mu


def inverse(mu, k):
    inv = [-1] * k
    for m, w in enumerate(mu):
        if w != -1:
            inv[w] = m
    return inv


def formal_stability(mu, pm, pw):
    inv = inverse(mu, len(pw))
    ir = (all(pm[m][-1] <= pm[m][w] for m, w in enumerate(mu))
          and all(pw[w][-1] <= pw[w][m] for w, m in enumerate(inv)))
    unblocked_m = all(not (pm[m][mu[m]] < pm[m][w]
                          and pw[w][inv[w]] < pw[w][m])
                      for m in range(len(pm)) for w in range(len(pw)))
    unblocked_w = all(not (pw[w][inv[w]] < pw[w][m]
                          and pm[m][mu[m]] < pm[m][w])
                      for w in range(len(pw)) for m in range(len(pm)))
    return ir and unblocked_m and unblocked_w


def conventional_stability(mu, pm, pw):
    """An unacceptable matched pair or mutually improving unmatched pair fails."""
    inv = inverse(mu, len(pw))
    if any(w != -1 and (pm[m][w] < pm[m][-1]
                        or pw[w][m] < pw[w][-1])
           for m, w in enumerate(mu)):
        return False
    for m in range(len(pm)):
        for w in range(len(pw)):
            if mu[m] != w and pm[m][w] > pm[m][mu[m]] and pw[w][m] > pw[w][inv[w]]:
                return False
    return True


def rejection_recurrence(pm, pw):
    """Direct transcription of gsProposals / gsHeld / gsStep, finite ranks."""
    n, k = len(pm), len(pw)
    rejected = set()
    for _ in range(n * k):
        proposal = {m: max([-1] + [w for w in range(k) if (m, w) not in rejected],
                           key=pm[m].get) for m in range(n)}
        proposal = {m: w for m, w in proposal.items() if w != -1}
        holds = {w: max([-1] + [m for m in proposal if proposal[m] == w],
                        key=pw[w].get) for w in range(k)}
        rejected |= {(m, w) for m, w in proposal.items() if holds[w] != m}
    proposal = {m: max([-1] + [w for w in range(k) if (m, w) not in rejected],
                       key=pm[m].get) for m in range(n)}
    holds = {w: max([-1] + [m for m in proposal if proposal[m] == w],
                    key=pw[w].get) for w in range(k)}
    final_new_rejections = {(m, w) for m, w in proposal.items()
                            if w != -1 and holds[w] != m}
    assert not final_new_rejections, (pm, pw, rejected)
    return tuple(proposal[m] for m in range(n))


def sequential_da(pm, pw):
    """Independent conventional implementation: free men make new offers."""
    n, k = len(pm), len(pw)
    remaining = {m: sorted([w for w in range(k) if pm[m][w] > pm[m][-1]],
                           key=pm[m].get, reverse=True) for m in range(n)}
    mu, inv = [-1] * n, [-1] * k
    while True:
        free = [m for m in range(n) if mu[m] == -1 and remaining[m]]
        if not free:
            return tuple(mu)
        m = free[0]
        w = remaining[m].pop(0)
        old = inv[w]
        if pw[w][m] > pw[w][old]:
            if old != -1:
                mu[old] = -1
            mu[m], inv[w] = w, m


def main():
    totals = {"profiles": 0, "matching_stability_comparisons": 0,
              "both_sides_da_comparisons": 0, "extremality_comparisons": 0}
    by_size = []
    for n in range(3):
        for k in range(3):
            profiles = 0
            matches = list(assignments(n, k))
            for pm in itertools.product(orders(k), repeat=n):
                for pw in itertools.product(orders(n), repeat=k):
                    profiles += 1
                    stable = []
                    for mu in matches:
                        fs = formal_stability(mu, pm, pw)
                        assert fs == conventional_stability(mu, pm, pw), (pm, pw, mu)
                        totals["matching_stability_comparisons"] += 1
                        if fs:
                            stable.append(mu)
                    got = rejection_recurrence(pm, pw)
                    seq = sequential_da(pm, pw)
                    assert got == seq and got in stable, (pm, pw, got, seq)
                    woman_first = rejection_recurrence(pw, pm)
                    woman_seq = sequential_da(pw, pm)
                    assert woman_first == woman_seq, (pm, pw)
                    woman_result = tuple(inverse(woman_first, n))
                    assert woman_result in stable, (pm, pw, woman_result)
                    totals["both_sides_da_comparisons"] += 2
                    for mu in stable:
                        inv_mu, inv_got = inverse(mu, k), inverse(got, k)
                        assert all(pm[m][mu[m]] <= pm[m][got[m]] for m in range(n))
                        assert all(pw[w][inv_got[w]] <= pw[w][inv_mu[w]] for w in range(k))
                        assert all(pw[w][inv_mu[w]] <= pw[w][woman_first[w]] for w in range(k))
                        assert all(pm[m][woman_result[m]] <= pm[m][mu[m]] for m in range(n))
                        totals["extremality_comparisons"] += 4
            totals["profiles"] += profiles
            by_size.append({"men": n, "women": k, "profiles": profiles,
                            "partial_matchings_per_profile": len(matches)})
    print(json.dumps({"scope": "all strict orders, optional partners, both populations size 0..2",
                      "source_execution": False, "result": "PASS", "totals": totals,
                      "by_size": by_size}, indent=2))


if __name__ == "__main__":
    main()
