module
public import Examples.sthubbar__goldbach_lean.Dependencies.v6400253cb469.LeanLab.Halupczok2012.U1460Reduction
/-!
# P0077 Halupczok 2012, the analytic layer for `SingSeriesTails`, unit U-1462

AI wrote the Lean code, Claude, run 20261022T0403Z-7595. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

Everything here is elementary and PROVED, no cited input.

* `rankin_tail`: Rankin's trick over subsets of a finite set of primes,
  `∑_{t ⊆ P, ∏ t > z} |∏_{p ∈ t} f p| ≤ z^{-σ} ∏_{p ∈ P} (1 + |f p| p^σ)`.
* `prod_le_Kc`: `∏ (1 + a_p) ≤ Kc σ` when `0 ≤ a_p ≤ 8 p^{-1-σ}`, with
  `Kc σ = exp (8 ζ(1 + σ))`.
* `prod_abs_le`: the Euler product of a weight bounded by `1/(p-1)² + [p ∣ r]/(p-1)`, times `p^σ`,
  is at most `Kc σ · Hs σ r`, `Hs σ r = ∏_{p ∣ r} (1 + p^σ/(p-1))`.
* `prod_primeFactors_eq_sum`: `∏_{p ∣ r} (1 + h p) = ∑_{t ⊆ primes ≤ N, ∏ t ∣ r} ∏_{p ∈ t} h p`.
* `sum_Hs_sq_le`: `∑_{m ∈ window} Hs σ (n - m)² ≤ Kc σ (y + n^{2σ})`.
* `sum_Hs_div_totient_le`: `∑_{q ≤ N} Hs σ q / φ(q) ≤ Kc σ (1 + log N)`.
* `hasProd_primes_tendsto`: partial products over the primes up to `w` of a summably perturbed
  function tend to its `tprod` over `Nat.Primes`.
-/
@[expose] public section
namespace LeanLab.Halupczok2012
open Finset Filter Topology
/-- The primes `p ≤ N`. -/
def PrN (N : ℕ) : Finset ℕ := (range (N + 1)).filter Nat.Prime
theorem mem_PrN {N p : ℕ} : p ∈ PrN N ↔ p ≤ N ∧ p.Prime := by
  simp [PrN]
theorem prime_of_mem_PrN {N p : ℕ} (h : p ∈ PrN N) : p.Prime := (mem_PrN.mp h).2
/-! ### Rankin's trick -/
theorem hasProd_primes_tendsto (f : ℕ → ℝ)
    (hs : Summable (fun k : ℕ => if k.Prime then f k - 1 else 0)) :
    Tendsto (fun w => ∏ p ∈ PrN w, f p) atTop (𝓝 (∏' p : Nat.Primes, f p)) := by
  set F : ℕ → ℝ := fun k => if k.Prime then f k else 1 with hF
  have hF1 : F = fun k => 1 + (if k.Prime then f k - 1 else 0) := by
    funext k; simp only [hF]; split_ifs <;> ring
  have hm : Multipliable F := by rw [hF1]; exact Real.multipliable_one_add_of_summable hs
  have hP : HasProd (F ∘ (Subtype.val : Nat.Primes → ℕ)) (∏' k, F k) := by
    rw [Subtype.val_injective.hasProd_iff]
    · exact hm.hasProd
    · intro k hk
      simp only [hF]
      rw [if_neg]
      intro hp; exact hk ⟨⟨k, hp⟩, rfl⟩
  have hcomp : (F ∘ (Subtype.val : Nat.Primes → ℕ)) = fun p : Nat.Primes => f p := by
    funext p; simp only [Function.comp, hF, if_pos p.prop]
  rw [hcomp] at hP
  have e : (∏' p : Nat.Primes, f p) = ∏' k, F k := hP.tprod_eq
  rw [e]
  have ht := hm.hasProd.tendsto_prod_nat
  have ht2 := ht.comp (tendsto_add_atTop_nat 1)
  refine ht2.congr (fun w => ?_)
  simp only [Function.comp, PrN, hF]
  rw [prod_filter]
end LeanLab.Halupczok2012
