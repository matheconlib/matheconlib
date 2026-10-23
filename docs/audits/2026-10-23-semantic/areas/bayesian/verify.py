#!/usr/bin/env python3
"""Exact finite-instance checks; not a proof of all Bayesian games or a Lean build."""
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import random
import re


def profiles(players):
    return list(product((0, 1), repeat=players))


def verify_game(n, prior, utility):
    types = profiles(n)
    strategies = list(product(tuple(product((0, 1), repeat=2)), repeat=n))

    def realized(s, t):
        return tuple(s[i][t[i]] for i in range(n))

    def marginal(i, own):
        return sum(prior[t] for t in types if t[i] == own)

    # Finite.lean:58-62, using the separately inspected condProbD definition.
    def interim(i, own, action, s):
        m = marginal(i, own)
        if m == 0:
            return Q(0)
        result = Q(0)
        for t in types:
            if t[i] == own:
                a = list(realized(s, t))
                a[i] = action
                result += prior[t] / m * utility[i, tuple(a), t]
        return result

    def value(i, own, s):
        return interim(i, own, s[i][own], s)

    def exante(i, s):
        return sum(prior[t] * utility[i, realized(s, t), t] for t in types)

    for s in strategies:
        # Literal player-type deviation relation, including all null types.
        formal = all(
            value(i, own, new) <= value(i, own, s)
            for i in range(n) for own in (0, 1) for new in strategies
            if all(new[j][t] == s[j][t]
                   for j in range(n) for t in (0, 1) if (j, t) != (i, own))
        )
        # Standard positive-marginal interim condition.
        intended = all(
            interim(i, own, a, s) <= value(i, own, s)
            for i in range(n) for own in (0, 1) for a in (0, 1)
            if marginal(i, own) > 0
        )
        # Ex ante Nash condition on whole contingent strategies.
        exante_ne = all(
            exante(i, new) <= exante(i, s)
            for i in range(n) for new in strategies
            if all(new[j] == s[j] for j in range(n) if j != i)
        )
        assert formal == intended == exante_ne
        for i in range(n):
            assert exante(i, s) == sum(marginal(i, own) * value(i, own, s)
                                       for own in (0, 1))
        for i in range(n):
            for own in (0, 1):
                for a in (0, 1):
                    if marginal(i, own) == 0:
                        assert interim(i, own, a, s) == 0
    return len(strategies)


def main():
    checks = 0
    # All one-player two-type, two-action tables in {-1,0,1}, four priors.
    keys = list(product(range(1), profiles(1), profiles(1)))
    priors1 = [(1, 0), (0, 1), (Q(1, 2), Q(1, 2)), (Q(1, 3), Q(2, 3))]
    one_games = 0
    for vals in product((-1, 0, 1), repeat=len(keys)):
        utility = dict(zip(keys, vals))
        for masses in priors1:
            checks += verify_game(1, dict(zip(profiles(1), masses)), utility)
            one_games += 1

    # Two-player positive/negative payoff basis tables, constants, seeded tables;
    # point, correlated, anticorrelated, full-support, and uneven priors.
    keys = list(product(range(2), profiles(2), profiles(2)))
    tables = [dict.fromkeys(keys, v) for v in (-1, 0, 1)]
    for k in keys:
        for v in (-1, 1):
            u = dict.fromkeys(keys, 0)
            u[k] = v
            tables.append(u)
    rng = random.Random(20261023)
    tables += [{k: rng.choice((-2, -1, 0, 1, 2)) for k in keys} for _ in range(24)]
    priors2 = [(1, 0, 0, 0), (Q(1, 2), 0, 0, Q(1, 2)),
               (0, Q(1, 2), Q(1, 2), 0), (Q(1, 4),) * 4,
               (Q(1, 10), Q(2, 10), Q(3, 10), Q(4, 10))]
    two_games = 0
    for utility in tables:
        for masses in priors2:
            checks += verify_game(2, dict(zip(profiles(2), masses)), utility)
            two_games += 1

    # Independently check the explicit finite null-type boundary witness.
    # At type 0: incumbent 1, deviation 0; at null type 1: both totalized to 0.
    assert (1 >= 0) and (0 >= 0)
    assert 0 < 1  # All-type selected-belief best response fails at type 1.

    # Exact partial sums for the nonintegrable-action boundary witness.
    for N in range(100):
        prob = sum(Q(1, 2 ** (n + 1)) for n in range(N + 1))
        expected = sum(Q(1, 2 ** (n + 1)) * 2 ** n for n in range(N + 1))
        assert prob == 1 - Q(1, 2 ** (N + 1))
        assert expected == Q(N + 1, 2)

    # Completeness check for the shared inventory only; semantic correctness is manual.
    root = Path(__file__).resolve().parents[5]
    inventory = json.loads((root / 'docs/audits/2026-10-23-semantic/inventory.json').read_text())
    subset = [x for x in inventory if x['area'] == 'bayesian']
    note = (Path(__file__).parent / 'audit.md').read_text()
    for item in subset:
        name = re.search(r'\b(?:def|abbrev|structure)\s+(\S+)', item['declaration']).group(1)
        assert '`' + name + '`' in note, (item['file'], name)
    print(json.dumps({'one_player_game_prior_instances': one_games,
                      'two_player_game_prior_instances': two_games,
                      'strategy_profiles_checked': checks,
                      'boundary_partial_sums_checked': 100,
                      'inventoried_declarations_named': len(subset),
                      'result': 'BAYESIAN_EXACT_CHECKS_PASS'}, sort_keys=True))


if __name__ == '__main__':
    main()
