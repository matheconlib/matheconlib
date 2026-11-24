/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.GeneralEquilibrium.PureExchange.Basic
public import MathEconLib.GeneralEquilibrium.PureExchange.Existence

/-!
# Finite pure-exchange equilibrium

The public interface separates complete preferences, their sufficient regularity conditions,
full endowment budgets, and the Walrasian equilibrium predicate. The existence theorem uses
ordinary convex preferences and therefore permits multivalued demand; its conclusion gives
positive normalized prices, full-budget household optimality, and exact market clearing.
It requires at least one good and allows an empty household set; uniform positive prices
support the empty allocation.

Use `budgetSet`, `demand`, and `IsWalrasianEquilibrium` to state a model without imposing the
existence assumptions. Supply `PreferenceRegularity` and positive individual endowments to
`exists_walrasianEquilibrium`. The `Internal` namespace contains the capped-demand and
price-response proof machinery. Worked examples and public-import tests exercise the public
interface separately.

The theorem follows Victor H. Aguiar's ECON 803 convex-preference appendix and the classical
Arrow–Debreu/Debreu fixed-point method; full source references and the specialization's scope
are documented in `PureExchange/Existence.lean`.
-/
