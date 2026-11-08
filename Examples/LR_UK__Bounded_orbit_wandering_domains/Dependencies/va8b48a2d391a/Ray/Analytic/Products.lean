module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Analytic.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Mathlib.Tactic.Cases
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Analytic.Analytic
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Analytic.Holomorphic
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Analytic.Series
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Misc.Bound
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Misc.Bounds
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Misc.Finset
/-!
## Infinite products of analytic functions

We define convergence of infinite products, and show that uniform limits of products of
analytic functions are analytic.
-/
open Complex (exp log)
open Filter (atTop)
open Metric (ball closedBall sphere)
open Set
open scoped Classical Real NNReal ENNReal Topology
noncomputable section
variable {ι : Type}
/-!
### Basics about products of sequences
-/
lemma norm_mul_sub_one_le {a b : ℂ} :
    ‖a * b - 1‖ ≤ (1 + ‖a - 1‖) * (1 + ‖b - 1‖) - 1 := by
  -- Ugly semi-GPT 5.1 proof, but meh, it works.
  have h1 : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring_nf
  have h2 : ‖a * b - 1‖ ≤ ‖(a - 1) * (b - 1) + (a - 1)‖ + ‖b - 1‖ := by
    simpa [h1, add_assoc] using (norm_add_le ((a - 1) * (b - 1) + (a - 1)) (b - 1))
  have h3 : ‖(a - 1) * (b - 1) + (a - 1)‖ ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ := by bound
  have h4 : ‖a * b - 1‖ ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ + ‖b - 1‖ :=
    le_trans h2 (by simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right h3 ‖b - 1‖)
  have h5 : ‖a * b - 1‖ ≤ ‖a - 1‖ * ‖b - 1‖ + ‖a - 1‖ + ‖b - 1‖ := by
    simpa [norm_mul, add_comm, add_left_comm, add_assoc] using h4
  grind
lemma Finset.norm_prod_sub_one_le {f : ι → ℂ} {s : Finset ι} :
    ‖∏ i ∈ s, f i - 1‖ ≤ ∏ i ∈ s, (1 + ‖f i - 1‖) - 1 := by
  induction' s using Finset.induction with i s is h
  · simp only [prod_empty, sub_self, norm_zero, le_refl]
  · simp only [Finset.prod_insert is]
    exact le_trans norm_mul_sub_one_le (by bound)
/-- Bound a product in terms of bounds on the first few terms, and a geometric tail bound -/
public lemma HasProd.norm_sub_one_le {f : ℕ → ℂ} {g : ℂ} (fg : HasProd f g)
    {n : ℕ} {b : Fin n → ℝ} (lo : ∀ k : Fin n, ‖f k - 1‖ ≤ b k)
    {c a : ℝ} (hi : ∀ k ≥ n, ‖f k - 1‖ ≤ c * a ^ k)
    (b0 : ∀ k, 0 ≤ b k) (c0 : 0 ≤ c) (a0 : 0 ≤ a) (a1 : a < 1) (ca : c * a ^ n / (1 - a) ≤ 1 / 2) :
    ‖g - 1‖ ≤ (∏ k, (1 + b k)) * (1 + 4 * c * a ^ n / (1 - a)) - 1 := by
  have le1 : ‖∏ i ∈ .range n, f i - 1‖ ≤ ∏ i, (1 + b i) - 1 := by
    refine le_trans Finset.norm_prod_sub_one_le ?_
    simp only [Finset.prod_fin_eq_prod_range]
    apply tsub_le_tsub_right
    gcongr with i m
    specialize lo ⟨i, by simpa using m⟩
    grind
  rw [le_sub_iff_add_le, add_comm] at le1
  simp only [HasProd] at fg
  apply le_of_tendsto (Filter.Tendsto.comp continuous_norm.continuousAt (fg.sub_const 1))
  simp only [Function.comp_apply, SummationFilter.unconditional_filter, Filter.eventually_atTop]
  refine ⟨Finset.range n, fun s ns ↦ ?_⟩
  have le2 : ‖∏ i ∈ s \ .range n, f i - 1‖ ≤ 4 * c * a ^ n / (1 - a) := by
    simp only [mul_assoc, div_eq_mul_inv]
    set t := (s \ .range n).image fun k ↦ k - n
    have st : s \ .range n = t.image fun k ↦ k + n := by
      simp only [t, Finset.image_image, Function.comp_def]
      rw [Finset.image_congr (g := id), Finset.image_id]
      intro k m
      simp at m ⊢
      omega
    have inj : InjOn (fun k ↦ k + n) t := by intro  a _ b _; simp
    simp only [st, Finset.prod_image inj, ← mul_assoc c]
    refine dist_prod_one_le_abs_sum ?_ ca
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (partial_geometric_bound t a0 a1) (by bound))
    simp only [Finset.mul_sum, mul_assoc, ← pow_add, add_comm n]
    exact Finset.sum_le_sum fun i m ↦ hi _ (by omega)
  have d : Disjoint (Finset.range n) (s \ Finset.range n) := Finset.disjoint_sdiff
  have e : s = (Finset.range n).disjUnion (s \ Finset.range n) d := by simpa using ns
  rw [e, Finset.prod_disjUnion]
  exact le_trans norm_mul_sub_one_le (by bound)
