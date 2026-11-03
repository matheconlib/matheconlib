/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import MathEconLib.GameTheory.Routing.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Braess's paradox

One unit of traffic travels from `W` to `E` through the intermediate nodes `N` and `S`. The roads
`W → N` and `S → E` have latency equal to their load, the roads `N → E` and `W → S` have latency
`1`, and the link `N → S` has latency `0`.

Without the link, traffic splits equally between the routes `W → N → E` and `W → S → E`, and each
driver's latency is `3 / 2`. With the link, every driver takes the zigzag route `W → N → S → E` at
the Wardrop equilibrium, and each driver's latency rises to `2`: adding a free road makes everyone
worse off. The equal split over the outer routes remains optimal in the larger network, so the
Wardrop flow costs `4 / 3` times the optimum, again attaining the Roughgarden–Tardos bound.

## Main definitions

* `braess`: The network with the link `N → S`.
* `braessWithoutLink`: The network without the link, with only the two outer routes.
* `zigzagFlow`: All traffic on the zigzag route.
* `splitFlow` and `outerSplitFlow`: Half the traffic on each outer route, in each network.

## Main statements

* `isWardrop_outerSplitFlow` and `cost_outerSplitFlow`: Without the link, the equal split is a
  Wardrop equilibrium with total latency `3 / 2`.
* `isWardrop_zigzagFlow` and `cost_zigzagFlow`: With the link, the zigzag flow is a Wardrop
  equilibrium with total latency `2`.
* `cost_splitFlow_le`: The equal split minimizes total latency in the network with the link.
* `cost_zigzagFlow_eq`: The Wardrop flow costs exactly `4 / 3` times the optimum.

## Tags

braess paradox, routing games, wardrop equilibrium, price of anarchy
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory

namespace MathEconLibExamples.GameTheory.Braess

/-- The five roads of the network. -/
inductive Road
  /-- The congestible road `W → N`. -/
  | westNorth
  /-- The constant road `N → E`. -/
  | northEast
  /-- The constant road `W → S`. -/
  | westSouth
  /-- The congestible road `S → E`. -/
  | southEast
  /-- The free link `N → S`. -/
  | link
  deriving DecidableEq

/-- The three routes from `W` to `E`. -/
inductive Route
  /-- The route `W → N → E`. -/
  | north
  /-- The route `W → S → E`. -/
  | south
  /-- The route `W → N → S → E` through the link. -/
  | zigzag
  deriving DecidableEq

/-- The two routes that avoid the link. -/
inductive OuterRoute
  /-- The route `W → N → E`. -/
  | north
  /-- The route `W → S → E`. -/
  | south
  deriving DecidableEq

open Road Route

instance : Fintype Road where
  elems := {westNorth, northEast, westSouth, southEast, link}
  complete x := by cases x <;> simp

instance : Fintype Route where
  elems := {north, south, zigzag}
  complete x := by cases x <;> simp

instance : Fintype OuterRoute where
  elems := {.north, .south}
  complete x := by cases x <;> simp

/-- The roads used by each route. -/
def Route.roads : Route → Finset Road
  | north => {westNorth, northEast}
  | south => {westSouth, southEast}
  | zigzag => {westNorth, link, southEast}

/-- The route through the full network corresponding to each outer route. -/
def OuterRoute.toRoute : OuterRoute → Route
  | .north => Route.north
  | .south => Route.south

/-- Road latencies: the load on the congestible roads, `1` on the constant roads, and `0` on the
link. -/
def Road.latency : Road → ℝ → ℝ
  | westNorth, x => x
  | southEast, x => x
  | northEast, _ => 1
  | westSouth, _ => 1
  | link, _ => 0

/-- Braess's network with the link, carrying one unit of traffic. -/
def braess : RoutingGame Unit Route Road :=
  .ofFinset (fun _ ↦ ()) Route.roads (fun _ ↦ 1) Road.latency

/-- Braess's network without the link, carrying one unit of traffic on the two outer routes. -/
def braessWithoutLink : RoutingGame Unit OuterRoute Road :=
  .ofFinset (fun _ ↦ ()) (fun r ↦ r.toRoute.roads) (fun _ ↦ 1) Road.latency

/-- All traffic takes the zigzag route. -/
def zigzagFlow : Route → ℝ
  | zigzag => 1
  | _ => 0

/-- Half the traffic takes each outer route in the network with the link. -/
def splitFlow : Route → ℝ
  | zigzag => 0
  | _ => 1 / 2

/-- Half the traffic takes each route in the network without the link. -/
def outerSplitFlow : OuterRoute → ℝ := fun _ ↦ 1 / 2

/-!
## Loads, latencies, and costs
-/

/-- A sum over routes has one term per route. -/
lemma sum_route (g : Route → ℝ) : ∑ r, g r = g north + g south + g zigzag := by
  rw [show (Finset.univ : Finset Route) = {north, south, zigzag} from rfl]
  simp [add_assoc]

/-- A sum over outer routes has one term per route. -/
lemma sum_outerRoute (g : OuterRoute → ℝ) : ∑ r, g r = g .north + g .south := by
  rw [show (Finset.univ : Finset OuterRoute) = {.north, .south} from rfl]
  simp

/-- Each road's load in the network with the link is the flow on the routes through it. -/
lemma load_eq (f : Route → ℝ) (e : Road) :
    braess.load f e = (if e ∈ north.roads then f north else 0) +
      (if e ∈ south.roads then f south else 0) + (if e ∈ zigzag.roads then f zigzag else 0) := by
  refine (RoutingGame.load_ofFinset _ _ _ _ f e).trans ?_
  rw [Finset.sum_filter, sum_route]

/-- Each road's load in the network without the link is the flow on the routes through it. -/
lemma load_eq_withoutLink (f : OuterRoute → ℝ) (e : Road) :
    braessWithoutLink.load f e = (if e ∈ north.roads then f .north else 0) +
      (if e ∈ south.roads then f .south else 0) := by
  refine (RoutingGame.load_ofFinset _ _ _ _ f e).trans ?_
  rw [Finset.sum_filter, sum_outerRoute]
  rfl

/-- A route's latency in the network with the link is the sum of its roads' latencies. -/
lemma pathLatency_eq_sum (f : Route → ℝ) (r : Route) :
    braess.pathLatency f r = ∑ e ∈ r.roads, Road.latency e (braess.load f e) :=
  RoutingGame.pathLatency_ofFinset _ _ _ _ f r

/-- A route's latency in the network without the link is the sum of its roads' latencies. -/
lemma pathLatency_withoutLink_eq_sum (f : OuterRoute → ℝ) (r : OuterRoute) :
    braessWithoutLink.pathLatency f r =
      ∑ e ∈ r.toRoute.roads, Road.latency e (braessWithoutLink.load f e) :=
  RoutingGame.pathLatency_ofFinset _ _ _ _ f r

/-- The route `W → N → E` has latency equal to the load on `W → N`, plus one. -/
lemma pathLatency_north (f : Route → ℝ) :
    braess.pathLatency f north = f north + f zigzag + 1 := by
  simp [pathLatency_eq_sum, load_eq, Route.roads, Road.latency]

/-- The route `W → S → E` has latency one plus the load on `S → E`. -/
lemma pathLatency_south (f : Route → ℝ) :
    braess.pathLatency f south = 1 + f south + f zigzag := by
  simp [pathLatency_eq_sum, load_eq, Route.roads, Road.latency]
  ring

/-- The zigzag route has latency equal to the loads on `W → N` and `S → E`. -/
lemma pathLatency_zigzag (f : Route → ℝ) :
    braess.pathLatency f zigzag = f north + f zigzag + (f south + f zigzag) := by
  simp [pathLatency_eq_sum, load_eq, Route.roads, Road.latency]

/-- Without the link, the route `W → N → E` has latency equal to its flow, plus one. -/
lemma pathLatency_withoutLink_north (f : OuterRoute → ℝ) :
    braessWithoutLink.pathLatency f .north = f .north + 1 := by
  simp [pathLatency_withoutLink_eq_sum, load_eq_withoutLink, OuterRoute.toRoute, Route.roads,
    Road.latency]

/-- Without the link, the route `W → S → E` has latency one plus its flow. -/
lemma pathLatency_withoutLink_south (f : OuterRoute → ℝ) :
    braessWithoutLink.pathLatency f .south = 1 + f .south := by
  simp [pathLatency_withoutLink_eq_sum, load_eq_withoutLink, OuterRoute.toRoute, Route.roads,
    Road.latency]

/-- Total latency in the network with the link in terms of the flow on each route. -/
lemma cost_eq (f : Route → ℝ) :
    braess.cost f = f north * (f north + f zigzag + 1) + f south * (1 + f south + f zigzag) +
      f zigzag * (f north + f zigzag + (f south + f zigzag)) := by
  rw [RoutingGame.cost, sum_route, pathLatency_north, pathLatency_south, pathLatency_zigzag]

/-- Total latency in the network without the link in terms of the flow on each route. -/
lemma cost_eq_withoutLink (f : OuterRoute → ℝ) :
    braessWithoutLink.cost f = f .north * (f .north + 1) + f .south * (1 + f .south) := by
  rw [RoutingGame.cost, sum_outerRoute, pathLatency_withoutLink_north,
    pathLatency_withoutLink_south]

/-- Feasible flows in the network with the link are nonnegative and sum to one. -/
lemma isFeasible_iff (f : Route → ℝ) :
    braess.IsFeasible f ↔ (∀ r, 0 ≤ f r) ∧ f north + f south + f zigzag = 1 := by
  simp [RoutingGame.IsFeasible, braess, RoutingGame.ofFinset, sum_route]

/-!
## Equilibria and the paradox
-/

/-- Without the link, the equal split is a Wardrop equilibrium: both routes have latency `3 / 2`. -/
theorem isWardrop_outerSplitFlow : braessWithoutLink.IsWardrop outerSplitFlow := by
  refine (RoutingGame.isWardrop_iff _ _).2 ⟨⟨fun _ ↦ by norm_num [outerSplitFlow], fun _ ↦ ?_⟩,
    fun p q _ _ ↦ ?_⟩
  · simp [braessWithoutLink, RoutingGame.ofFinset, outerSplitFlow,
      show Fintype.card OuterRoute = 2 from rfl]
  · cases p <;> cases q <;>
      norm_num [pathLatency_withoutLink_north, pathLatency_withoutLink_south, outerSplitFlow]

/-- Without the link, total latency at equilibrium is `3 / 2`. -/
theorem cost_outerSplitFlow : braessWithoutLink.cost outerSplitFlow = 3 / 2 := by
  norm_num [cost_eq_withoutLink, outerSplitFlow]

/-- With the link, the zigzag flow is a Wardrop equilibrium: every route has latency `2`. -/
theorem isWardrop_zigzagFlow : braess.IsWardrop zigzagFlow := by
  refine (RoutingGame.isWardrop_iff _ _).2 ⟨(isFeasible_iff _).2 ⟨fun r ↦ ?_, ?_⟩,
    fun p q _ _ ↦ ?_⟩
  · cases r <;> norm_num [zigzagFlow]
  · norm_num [zigzagFlow]
  · cases p <;> cases q <;>
      norm_num [pathLatency_north, pathLatency_south, pathLatency_zigzag, zigzagFlow]

/-- With the link, total latency at equilibrium is `2`. -/
theorem cost_zigzagFlow : braess.cost zigzagFlow = 2 := by
  norm_num [cost_eq, zigzagFlow]

/-- **Braess's paradox.** Adding the free link raises total latency at equilibrium. -/
theorem cost_outerSplitFlow_lt_cost_zigzagFlow :
    braessWithoutLink.cost outerSplitFlow < braess.cost zigzagFlow := by
  rw [cost_outerSplitFlow, cost_zigzagFlow]
  norm_num

/-- The equal split over the outer routes minimizes total latency in the network with the link. -/
theorem cost_splitFlow_le {g : Route → ℝ} (hg : braess.IsFeasible g) :
    braess.cost splitFlow ≤ braess.cost g := by
  obtain ⟨hg0, hsum⟩ := (isFeasible_iff g).1 hg
  rw [cost_eq, cost_eq]
  norm_num [splitFlow]
  nlinarith [sq_nonneg (g north - g south), sq_nonneg (g zigzag), hg0 zigzag]

/-- The Wardrop flow costs `4 / 3` times the optimum, so the Roughgarden–Tardos bound is tight. -/
theorem cost_zigzagFlow_eq : braess.cost zigzagFlow = 4 / 3 * braess.cost splitFlow := by
  norm_num [cost_eq, zigzagFlow, splitFlow]

end MathEconLibExamples.GameTheory.Braess
