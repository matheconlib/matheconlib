module

public import Auctionlib.AllPurchase.Definitions

/-!
# All-Purchase Auction — Weak Monotonicity (Lemma 6.1)

In any symmetric pure-strategy BNE, the composite winning probability `q = G ∘ β`
is nondecreasing, and if `G` is strictly increasing, the bidding function `β`
is itself weakly increasing.

## Main results

- `AllPurchaseCore.q_monotoneOn`: `q = G ∘ β` is nondecreasing on `[a, b]`.
- `AllPurchaseCore.weakMonotonicity`: Under `StrictMono G`, `β` is nondecreasing on `[a, b]`.
-/

@[expose] public section

section monotonicity

namespace AllPurchaseCore

variable (ε : AllPurchaseCore)

/-- The composite winning probability `q = G ∘ β` is nondecreasing on `[a, b]`.
Direct consequence of `EnvelopeSetUpMathsCore.q_monotoneOn` via the coercion
`AllPurchaseCore.toEnvelopeSetUpMathsCore`. -/
lemma q_monotoneOn : MonotoneOn ε.q (Set.Icc ε.a ε.b) :=
  ε.toEnvelopeSetUpMathsCore.q_monotoneOn

/-- **Lemma 6.1 — Weak Monotonicity.** In any symmetric pure-strategy BNE
with strictly increasing winning probability `G`, the bidding strategy `β`
is weakly increasing on `[a, b]`.

Proof: IC implies `G ∘ β` is nondecreasing (`q_monotoneOn`). Since `G` is
strictly increasing, `G(β(x)) ≤ G(β(y))` implies `β(x) ≤ β(y)`. -/
lemma weakMonotonicity (hG : StrictMono ε.G) :
    MonotoneOn ε.β (Set.Icc ε.a ε.b) :=
  fun _ hx _ hy hxy => hG.le_iff_le.mp (ε.q_monotoneOn hx hy hxy)

end AllPurchaseCore

end monotonicity

end
