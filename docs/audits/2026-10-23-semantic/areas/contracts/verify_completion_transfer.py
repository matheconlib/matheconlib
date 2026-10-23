#!/usr/bin/env python3
"""Exhaustively check completion transfer in the specified three-contract models.

Scope: one buyer, three labeled contracts, and one canonical seller partition
for each partition shape: (0,0,0), (0,0,1), (0,1,2). All buyer choice maps
satisfying contraction and IRC are enumerated, as are all completions that
satisfy IRC and substitutability. Sellers use all strict unit-demand preference
orders with an outside option, represented by all ordered acceptable lists.
Every possible outcome and every nonempty disjoint blocking set is checked.

Sets are bit masks. Each choice map is a tuple indexed by the menu mask.
This checks only the finite configurations encoded here, not a general theorem.
"""

from itertools import permutations, product

N = 3
MENUS = list(range(1 << N))
SUBMENUS = [[z for z in MENUS if z & y == z] for y in MENUS]


def irc(choice):
    """C(Y) subset Z subset Y implies C(Z) = C(Y)."""
    return all(
        choice[z] == choice[y]
        for y in MENUS
        for z in SUBMENUS[y]
        if choice[y] & z == choice[y]
    )


def substitutable(choice):
    """Chernoff: C(Y) intersect Z subset C(Z) whenever Z subset Y."""
    return all(
        (choice[y] & z) & ~choice[z] == 0
        for y in MENUS
        for z in SUBMENUS[y]
    )


def seller_choices(own_contracts):
    """All strict unit-demand choices; earlier acceptable contracts are better."""
    result = []
    for length in range(len(own_contracts) + 1):
        for acceptable in permutations(own_contracts, length):
            result.append(
                tuple(
                    next((1 << x for x in acceptable if menu >> x & 1), 0)
                    for menu in MENUS
                )
            )
    return result


def check_partition(seller, original_choices, completed_choices):
    seller_ids = sorted(set(seller))
    own = {
        s: sum(1 << x for x in range(N) if seller[x] == s)
        for s in seller_ids
    }

    def feasible(contracts):
        return all(bin(contracts & own[s]).count("1") <= 1 for s in seller_ids)

    profiles = list(
        product(
            *(
                seller_choices([x for x in range(N) if seller[x] == s])
                for s in seller_ids
            )
        )
    )

    def stable(buyer_choice, seller_profile, outcome):
        # Individual rationality: the unique buyer chooses all of the outcome,
        # and each seller chooses exactly its own outcome contracts.
        if buyer_choice[outcome] != outcome:
            return False
        if any(
            seller_profile[i][outcome] != outcome & own[s]
            for i, s in enumerate(seller_ids)
        ):
            return False
        # Blocks must be nonempty, new, and chosen by all involved agents.
        for block in MENUS[1:]:
            if outcome & block:
                continue
            if block & ~buyer_choice[outcome | block]:
                continue
            if all(
                (block & own[s]) & ~seller_profile[i][outcome | block] == 0
                for i, s in enumerate(seller_ids)
            ):
                return False
        return True

    pairs = [
        (original, completed)
        for original in original_choices
        for completed in completed_choices
        if all(
            completed[menu] == original[menu] or not feasible(completed[menu])
            for menu in MENUS
        )
    ]
    checks = 0
    for original, completed in pairs:
        for profile in profiles:
            for outcome in MENUS:
                checks += 1
                assert not stable(completed, profile, outcome) or stable(
                    original, profile, outcome
                ), (seller, original, completed, profile, outcome)
    print(
        {
            "seller_partition": seller,
            "IRC_choices": len(original_choices),
            "IRC_substitutable_choices": len(completed_choices),
            "completion_pairs": len(pairs),
            "seller_profiles": len(profiles),
            "configurations_outcomes_checked": checks,
        }
    )
    return checks


def main():
    # Enumerating subsets at every menu makes contraction a built-in invariant.
    choices = list(product(*SUBMENUS))
    assert len(choices) == 4096
    original_choices = [choice for choice in choices if irc(choice)]
    completed_choices = [
        choice for choice in original_choices if substitutable(choice)
    ]
    assert len(original_choices) == 246
    assert len(completed_choices) == 35
    checks = sum(
        check_partition(partition, original_choices, completed_choices)
        for partition in [(0, 0, 0), (0, 0, 1), (0, 1, 2)]
    )
    assert checks == 63856
    print(
        "PASS: completed-stable implies original-stable for",
        checks,
        "finite configurations/outcomes",
    )


if __name__ == "__main__":
    main()
