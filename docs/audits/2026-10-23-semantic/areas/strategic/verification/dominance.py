#!/usr/bin/env python3
"""Finite semantic cross-check for Strategic/Basic.lean.

Run from any directory; JSON is printed to stdout. This verifies exactly the
finite games encoded below. The separate changer-set argument in the audit,
not this enumeration, establishes the unbounded coalition equivalence.
No Lean sources or generated Lean artifacts are modified.
"""

from itertools import product
import json


def exhaustive_binary_games():
    """The independently run checker, with named counters added for reporting."""
    profiles = list(product(range(2), repeat=2))
    count = 0
    dominance_cases = 0
    for vals in product(range(2), repeat=8):
        u = {a: vals[2 * k : 2 * k + 2] for k, a in enumerate(profiles)}
        for a in profiles:
            strong_code = all(
                any(a[i] != b[i] and u[b][i] <= u[a][i] for i in range(2))
                for b in profiles if b != a
            )
            strong_standard = not any(
                all(u[b][i] > u[a][i] for i in C)
                for C in [(0,), (1,), (0, 1)]
                for b in profiles
                if all(b[j] == a[j] for j in range(2) if j not in C)
            )
            assert strong_code == strong_standard, (u, a)
            strict_code = all(
                u[tuple((s if j == i else a[j]) for j in range(2))][i] < u[a][i]
                for i in range(2) for s in range(2) if s != a[i]
            )
            strict_standard = all(
                u[a][i] > u[b][i]
                for i in range(2) for b in profiles
                if b != a and all(b[j] == a[j] for j in range(2) if j != i)
            )
            assert strict_code == strict_standard, (u, a)
            count += 1
        for i in range(2):
            for s in range(2):
                def le(x, y):
                    return all(
                        u[tuple((x if j == i else a[j]) for j in range(2))][i]
                        <= u[tuple((y if j == i else a[j]) for j in range(2))][i]
                        for a in profiles
                    )

                dominant_code = all(le(t, s) for t in range(2))
                dominant_standard = all(
                    u[a][i] <= u[tuple((s if j == i else a[j]) for j in range(2))][i]
                    for a in profiles
                )
                assert dominant_code == dominant_standard
                strict_order_code = all(
                    le(t, s) and not le(s, t) for t in range(2) if t != s
                )
                weak_strictsomewhere = all(
                    le(t, s) and any(
                        u[tuple((t if j == i else a[j]) for j in range(2))][i]
                        < u[tuple((s if j == i else a[j]) for j in range(2))][i]
                        for a in profiles
                    )
                    for t in range(2) if t != s
                )
                assert strict_order_code == weak_strictsomewhere
                dominance_cases += 1
    return {
        "status": "PASS",
        "games": 256,
        "players": 2,
        "actions_per_player": 2,
        "payoff_values": [0, 1],
        "game_profile_cases": count,
        "game_player_action_cases": dominance_cases,
        "checked_equivalences": [
            "Strong Nash: changing-player witness versus nonempty profitable coalition",
            "Strict Nash: different action versus different unilateral profile",
            "Dominant: top of payoff preorder versus pointwise best action",
            "Strict-order dominant: strict preorder versus weak everywhere and strict somewhere",
        ],
    }


class FiniteGame:
    """Literal finite versions of the library predicates, for boundary cases."""

    def __init__(self, actions, payoff):
        self.actions = tuple(tuple(xs) for xs in actions)
        self.players = range(len(actions))
        self.profiles = list(product(*self.actions))
        self.payoff = payoff

    def update(self, a, i, s):
        return tuple(s if j == i else a[j] for j in self.players)

    def le(self, i, s, t):
        # Direct two-profile definition, rather than its update characterization.
        return all(
            self.payoff(a)[i] <= self.payoff(b)[i]
            for a in self.profiles for b in self.profiles
            if a[i] == s and b[i] == t
            and all(a[j] == b[j] for j in self.players if j != i)
        )

    def dominant(self, i, s):
        return all(self.le(i, t, s) for t in self.actions[i])

    def strict_order_dominant(self, i, s):
        return all(
            self.le(i, t, s) and not self.le(i, s, t)
            for t in self.actions[i] if t != s
        )

    def strictly_dominant(self, i, s):
        return all(
            self.payoff(self.update(a, i, t))[i]
            < self.payoff(self.update(a, i, s))[i]
            for t in self.actions[i] if t != s for a in self.profiles
        )

    def nash(self, a):
        return all(
            self.payoff(self.update(a, i, s))[i] <= self.payoff(a)[i]
            for i in self.players for s in self.actions[i]
        )

    def strict_nash(self, a):
        return all(
            self.payoff(self.update(a, i, s))[i] < self.payoff(a)[i]
            for i in self.players for s in self.actions[i] if s != a[i]
        )

    def strong_nash(self, a):
        return all(
            any(a[i] != b[i] and self.payoff(b)[i] <= self.payoff(a)[i]
                for i in self.players)
            for b in self.profiles if b != a
        )

    def strategy_summary(self, i, s):
        return {
            "dominant": self.dominant(i, s),
            "strict_order_dominant": self.strict_order_dominant(i, s),
            "strictly_dominant": self.strictly_dominant(i, s),
        }

    def equilibrium_summary(self, a):
        return {
            "nash": self.nash(a),
            "strict_nash": self.strict_nash(a),
            "strong_nash": self.strong_nash(a),
        }


def boundary_cases():
    # Distinct actions with identical payoffs: dominance need not be strict.
    tied = FiniteGame([(0, 1)], lambda a: (0,))
    tied_strategy = {"dominant": True, "strict_order_dominant": False,
                     "strictly_dominant": False}
    tied_equilibrium = {"nash": True, "strict_nash": False, "strong_nash": True}
    assert tied.le(0, 0, 1) and tied.le(0, 1, 0)
    for s in (0, 1):
        assert tied.strategy_summary(0, s) == tied_strategy
        assert tied.equilibrium_summary((s,)) == tied_equilibrium

    # Strict-order dominance allows ties at some opponent profiles.
    some_ties = FiniteGame([(0, 1), (0, 1)], lambda a: (a[0] * a[1], 0))
    some_ties_summary = {"dominant": True, "strict_order_dominant": True,
                         "strictly_dominant": False}
    assert some_ties.strategy_summary(0, 1) == some_ties_summary
    assert some_ties.payoff((0, 0))[0] == some_ties.payoff((1, 0))[0] == 0
    assert some_ties.payoff((0, 1))[0] == 0 < some_ties.payoff((1, 1))[0] == 1

    # No opponent actions: full-profile quantification is vacuous. There is no
    # candidate equilibrium profile. This also shows why the library's bridge
    # theorem from strict to strict-order dominance needs Nonempty profiles.
    def impossible_payoff(a):
        raise AssertionError("No payoff evaluation is possible without a profile")

    empty_opponent = FiniteGame([(0, 1), ()], impossible_payoff)
    empty_summary = {"dominant": True, "strict_order_dominant": False,
                     "strictly_dominant": True}
    assert empty_opponent.profiles == []
    assert empty_opponent.le(0, 0, 1) and empty_opponent.le(0, 1, 0)
    for s in (0, 1):
        assert empty_opponent.strategy_summary(0, s) == empty_summary

    # Empty own action space: there are no strategies or equilibrium profiles.
    empty_own = FiniteGame([()], impossible_payoff)
    assert empty_own.profiles == [] and empty_own.actions[0] == ()

    # A unique action is vacuously strictly dominant and a strict equilibrium.
    singleton = FiniteGame([(0,)], lambda a: (0,))
    singleton_strategy = {"dominant": True, "strict_order_dominant": True,
                          "strictly_dominant": True}
    all_equilibria = {"nash": True, "strict_nash": True, "strong_nash": True}
    assert singleton.strategy_summary(0, 0) == singleton_strategy
    assert singleton.equilibrium_summary((0,)) == all_equilibria

    # An empty player set has one empty profile; all equilibrium conditions hold.
    no_players = FiniteGame([], lambda a: ())
    assert no_players.profiles == [()]
    assert no_players.equilibrium_summary(()) == all_equilibria
    return {
        "status": "PASS",
        "tied_duplicate_actions": {
            "game": "One player, actions 0 and 1, payoff 0 at both",
            "mutual_preorder_comparison": True,
            "each_action": tied_strategy,
            "each_profile": tied_equilibrium,
            "interpretation": "Distinct payoff-equivalent actions are weakly optimal but not strict",
        },
        "strict_order_dominance_with_some_ties": {
            "game": "Two binary-action players; payoff vector (a0*a1, 0)",
            "player_0_action_1": some_ties_summary,
            "interpretation": "Strict-order dominance and strict dominance intentionally differ",
        },
        "empty_opponent_action_space": {
            "game": "Player 0 actions 0 and 1; player 1 no actions",
            "profile_count": 0,
            "each_player_0_action": empty_summary,
            "interpretation": "Vacuity; Nonempty profile hypothesis correctly excludes this from bridge theorem",
        },
        "empty_own_action_space": {"strategy_count": 0, "profile_count": 0},
        "singleton_action_space": {
            "only_strategy": singleton_strategy,
            "only_profile": all_equilibria,
        },
        "no_players": {"profile_count": 1, "empty_profile": all_equilibria},
    }


if __name__ == "__main__":
    print(json.dumps({
        "source": "MathEconLib/GameTheory/Strategic/Basic.lean",
        "status": "PASS",
        "finite_exhaustion": exhaustive_binary_games(),
        "boundary_cases": boundary_cases(),
        "scope_limit": "Finite evidence only; no inference of a general theorem from enumeration",
    }, indent=2, sort_keys=True))
