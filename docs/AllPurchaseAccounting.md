# All-purchase accounting

An all-purchase bidder buys `bᵢ` editions at posted unit price `p` and receives a separate prize if
strictly highest. At total purchases `B`, the editions have per-unit resale value `φ(B)`.
The bidder's utility is

```
prize value + φ(B) bᵢ - p bᵢ.
```

The seller receives `p bᵢ`. Resale proceeds belong to the bidder's outcome value. Charging the
seller for those proceeds incorrectly reports seller revenue as `(p - φ(B)) B`.

This repair follows the report and proposed fix by
[yoshiki-pramaana in #239](https://github.com/matheconlib/matheconlib/issues/239).

## Monetary mechanism

`Mechanism.Auctions.AllPurchaseSpec M alloc purchases` requires:

- `purchases (M.outcome b) = b`, so valuations can observe the purchased editions;
- `M.transfer i b = -(spec.price * b i)`, so payments to the seller are gross expenditure;
- the existing strictly highest purchaser allocation rule, positive price, and continuous,
  strictly decreasing scarcity schedule.

Use `spec.environment` to include prize value and resale value in the bidder's valuation.
`spec.utility_eq` gives the net-cost utility formula. `spec.revenue_eq` gives actual receipts
`p * B`, and `spec.price_unique` identifies the posted price when there is at least one bidder.
`spec.netCost` is expenditure less resale value; `spec.payment_eq` now gives gross expenditure.

## Scalar bidder analysis and revenue API

The scalar `Auction` carrier represents prize-only values. Existing all-purchase bidding,
quadratic-cost, and envelope calculations use `AllPurchaseBidderSpec` to represent bidder net
costs. `AllPurchaseBidderModel` packages that auxiliary calculation with its price and scarcity
specification, with no automatic conversion to a generic `Auction`.

For an adapter `A`, the public financial methods have distinct names:

- `A.sellerRevenue b`: actual seller receipts at purchase profile `b`;
- `A.expectedSellerRevenue β`: actual expected seller receipts under common strategy `β`;
- `A.expectedNetCost β`: expected total bidder net cost, after resale value.

Both expectation methods require an explicit strategy. `A.expectedRevenue` and
`Auction.expectedRevenue A` are rejected by Lean. The raw scalar model remains available by
explicit `A.toNetCostAuction`; its payments, `p_strat`, and `expectedRevenue` represent bidder
net costs. In particular, `A.expectedNetCost id` agrees with the raw auction's truthful
`expectedRevenue`. There is no ambiguous revenue alias on the adapter.

`A.toMechanism` records purchases and charges gross expenditure. `A.environment` includes resale
value. At the specification level, `spec.utility_toMechanism` and
`spec.preference_toMechanism` prove that the actual mechanism and auxiliary model give every
bidder the same utility and deviation comparisons on the unchanged real action domain.

`expectedSellerRevenue_eq` gives posted price times expected purchases under the same strategy.
`sellerRevenue_integrable` proves receipt integrability from integrable individual purchases.
The bridges in `RevenueDecomposition.lean` connect these APIs to the existing gross-revenue and
net-payment formulas. Revenue decomposition, profit comparison, and welfare-moment results keep
their economic hypotheses and conclusions.

## Migration

Code constructing a monetary `AllPurchaseSpec` must add the purchases projection and
`purchases_eq`, and change transfers to gross expenditure. Pair the mechanism with
`spec.environment` to preserve bidder utility. A transfer-only edit changes the game.

Code using the old scalar net-cost specification should use `AllPurchaseBidderSpec A.rules`.
Package the scalar auction and specification as an `AllPurchaseBidderModel` when exposing it to
callers; use the safe revenue methods above.

`LinearScarcityAuction` now extends `AllPurchaseBidderModel` rather than `Auction`. Its old
implicit conversion and `toAuction` projection are removed. Supply the parent bidder model in
constructors, and use explicit `A.toNetCostAuction` for scalar proof machinery and typeclasses,
for example `[A.toNetCostAuction.HasIdenticalTypes]`.

Replace an old scalar `expectedRevenue` call with `expectedNetCost id` when the intended quantity
is bidder net cost. For seller receipts use `expectedSellerRevenue β` with the actual strategy;
use `id` only for truthful play. The old ambiguous call fails instead of silently changing its
meaning. Scalar `payment_eq` and `p_strat` formulas remain net costs behind the explicit
projection. The affected API pins include these projection changes and the new financial APIs;
IC, integrability, and baseline-utility assumptions are retained.

## Scope

Purchases remain real-valued. `spec.revenue_nonnegative` assumes nonnegative purchases;
`spec.isNoDeficit_nonnegative` establishes global no-deficit for the existing `comap` restriction
to `Set.Ici 0`. With at least one bidder, unrestricted real actions admit negative purchases and
violate global no-deficit. Restricting actions changes the set of allowed deviations.

The repair preserves the current scarcity model. It does not impose no-arbitrage conditions or
prove equilibrium existence. The exponential scarcity example in #239 still has no best response,
even with nonnegative purchases. Expected-revenue comparisons must use the same strategy and
establish integrability; Lean's totalized integral identities alone do not provide finite
expectations. The resale valuation models the bidder's proceeds, not an entire secondary market.
