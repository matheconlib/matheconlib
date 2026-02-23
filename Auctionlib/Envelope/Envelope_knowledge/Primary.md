# §5 Revenue Equivalence: Prerequisites & Theorems

## Setup

- `n` bidders, single indivisible good
- Each bidder has private valuation `θᵢ ∈ [θ̲, θ̄]`, i.i.d. ~ CDF `F`, density `f`
- Quasi-linear utility: `uᵢ = θᵢ · xᵢ − tᵢ` (win probability × value − payment)
- `xᵢ(θ)` = allocation rule (probability bidder i wins), `tᵢ(θ)` = payment rule
- Interim quantities (expectations over `θ₋ᵢ`):
  - `qᵢ(θᵢ) = 𝔼_{θ₋ᵢ}[xᵢ(θᵢ, θ₋ᵢ)]` (interim win probability)
  - `Uᵢ(θᵢ) = θᵢ · qᵢ(θᵢ) − 𝔼_{θ₋ᵢ}[tᵢ(θᵢ, θ₋ᵢ)]` (interim expected utility)

## IC (Incentive Compatibility)

Truthful reporting is optimal.

**DSIC:** For all `i`, all `θᵢ, θᵢ', θ₋ᵢ`:
```
θᵢ · xᵢ(θᵢ, θ₋ᵢ) − tᵢ(θᵢ, θ₋ᵢ) ≥ θᵢ · xᵢ(θᵢ', θ₋ᵢ) − tᵢ(θᵢ', θ₋ᵢ)
```
Truthful is optimal regardless of others' reports.

**BIC:** Same but in expectation over `θ₋ᵢ`:
```
Uᵢ(θᵢ) ≥ θᵢ · qᵢ(θᵢ') − 𝔼_{θ₋ᵢ}[tᵢ(θᵢ', θ₋ᵢ)]
```
Truthful is optimal on average.

**Key consequences of IC:** Write IC in both directions for any `θᵢ, θᵢ'` and sum:
```
(θᵢ − θᵢ') · [xᵢ(θᵢ, θ₋ᵢ) − xᵢ(θᵢ', θ₋ᵢ)] ≥ 0
```
i.e., IC ⟹ allocation is monotone nondecreasing in type.

Write IC in both directions and rearrange to get the sandwich:
```
(θᵢ − θᵢ') · qᵢ(θᵢ') ≤ Uᵢ(θᵢ) − Uᵢ(θᵢ') ≤ (θᵢ − θᵢ') · qᵢ(θᵢ)
```

## IR (Individual Rationality)

Participation is no worse than opting out (utility ≥ 0). Three strengths:

- **Ex-post IR:** `θᵢ · xᵢ(θ) − tᵢ(θ) ≥ 0` for all `θ`
- **Interim IR:** `Uᵢ(θᵢ) ≥ 0` for all `θᵢ`
- **Ex-ante IR:** `𝔼_θ[uᵢ] ≥ 0`

§5 uses the boundary condition `U(θ̲) = 0` (lowest type gets zero utility), which pins down the constant of integration.

---

# §5 Theorems

## Theorem 5.1: Envelope Theorem

IC ⟹ `dUᵢ/dθᵢ = qᵢ(θᵢ)` a.e., hence `Uᵢ(θᵢ) = Uᵢ(θ̲) + ∫_{θ̲}^{θᵢ} qᵢ(ψ) dψ`.

**Proof:** Divide the sandwich by `θᵢ − θᵢ'`, squeeze to get the derivative, then apply FTC.

## Lemma 5.2: Myerson's Lemma

`xᵢ` is implementable by a DSIC mechanism ⟺ `xᵢ` is monotone in `θᵢ`. If monotone, the unique payment is:
```
tᵢ = θᵢ · xᵢ − ∫_{θ̲}^{θᵢ} xᵢ(ψ, θ₋ᵢ) dψ − hᵢ(θ₋ᵢ)
```

**Proof:** Necessity = sum both IC directions to get monotonicity. Sufficiency = use Envelope Theorem to solve for `tᵢ`.

## Theorem 5.3: Revenue Equivalence

Any mechanism satisfying (1) efficient allocation, (2) IC, (3) `U(θ̲) = 0` yields the same expected payment:
```
𝔼[tᵢ(θᵢ, ·)] = θᵢ · F(θᵢ)^{n-1} − ∫_{θ̲}^{θᵢ} F(ψ)^{n-1} dψ
```

**Proof:** Envelope Thm + `U(θ̲) = 0` pins down `Uᵢ`; efficient allocation ⟹ `qᵢ(θᵢ) = F(θᵢ)^{n-1}`; solve `Uᵢ = θᵢqᵢ − 𝔼[tᵢ]` for expected payment — depends only on `F, n`.