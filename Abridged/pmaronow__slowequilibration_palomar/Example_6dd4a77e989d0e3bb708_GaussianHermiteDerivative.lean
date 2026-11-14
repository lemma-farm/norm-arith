module

public import Mathlib

-- ==== Examples.pmaronow__slowequilibration_palomar.Dependencies.v3f58d72b5afe.SlowEquilibration.Upstream.OAI.Computability.MinUncut.GaussianHermite ====
public section
-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
-- lean/OAI/Computability/MinUncut/Estimates/Basic.lean.
-- Module/public-import adaptation; unused MinUncut game-model import removed.
set_option autoImplicit false
@[expose] public section
set_option maxHeartbeats 2000000
namespace OAI
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
abbrev γ : Measure ℝ := gaussianReal 0 1
def he (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n)

def H (n : ℕ) (x : ℝ) : ℝ := he n x / Real.sqrt (n.factorial : ℝ)

section Product
variable {ι : Type*} [Fintype ι]
abbrev γpi (ι : Type*) [Fintype ι] : Measure (ι → ℝ) := Measure.pi (fun _ => γ)

def psi (a : ι → ℕ) (x : ι → ℝ) : ℝ := ∏ i, H (a i) (x i)

end Product

variable {ι : Type*} [Fintype ι]

def coeff (f : (ι → ℝ) → ℝ) (a : ι → ℕ) : ℝ := ∫ x, psi a x * f x ∂γpi ι
def degree (a : ι → ℕ) : ℕ := ∑ i, a i
def bump [DecidableEq ι] (i : ι) (a : ι → ℕ) : ι → ℕ := Function.update a i (a i+1)

end MinUncut.GaussianHermite
end
end OAI

end
end

-- ==== Examples.pmaronow__slowequilibration_palomar.Examples.Example_6dd4a77e989d0e3bb708_GaussianHermiteDerivative ====
-- SPDX-License-Identifier: Apache-2.0
set_option autoImplicit false
/-! The finite Bessel estimate used by Hermite truncation.  This file keeps
the analytic coefficient identity explicit: it does not assert integration
by parts for a function without hypotheses justifying that identity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianHermiteDerivative
open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

set_option linter.unusedVariables false in
/-- The coordinate raising identity and square integrability of the actual
derivatives imply the finite weighted-energy bound needed by truncation.
Only finitely many coefficients are summed, so no exchange of infinite
weighted sums and integrals is required. -/
theorem finite_weighted_energy_le_of_coeff_identity [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (g : ι → (ι → ℝ) → ℝ)
    (hg : ∀ i, MemLp (g i) 2 (γpi ι))
    (hcoeff : ∀ i a,
      coeff (g i) a = Real.sqrt (a i + 1 : ℝ) * coeff f (bump i a))
    (s : Finset (ι → ℕ)) 
    (h_SlowEquilibration_GaussianHermiteDerivative_finite_coeff_square_sum_le : ∀ {ι : Type u_1} [inst : Fintype ι] {f : (ι → ℝ) → ℝ},
      MeasureTheory.MemLp f 2 (OAI.MinUncut.GaussianHermite.γpi ι) →
        ∀ (s : Finset (ι → ℕ)),
          ∑ a ∈ s, OAI.MinUncut.GaussianHermite.coeff f a ^ 2 ≤
            ∫ (x : ι → ℝ), f x ^ 2 ∂OAI.MinUncut.GaussianHermite.γpi ι)
    :
    ∑ a ∈ s, (degree a : ℝ) * (coeff f a) ^ 2 ≤
      ∑ i, ∫ x, (g i x) ^ 2 ∂γpi ι := by
  classical
  have hcoord (i : ι) :
      ∑ a ∈ s, (a i : ℝ) * (coeff f a) ^ 2 ≤
        ∫ x, (g i x) ^ 2 ∂γpi ι := by
    let t := s.filter (fun a => 0 < a i)
    let lower : (ι → ℕ) → (ι → ℕ) := fun a => Function.update a i (a i - 1)
    have hlower (a : ι → ℕ) (ha : a ∈ t) : bump i (lower a) = a := by
      have ha' : 0 < a i := (Finset.mem_filter.mp ha).2
      ext j
      by_cases hj : j = i
      · subst j
        simp only [bump, lower, Function.update_self]
        omega
      · simp [bump, lower, Function.update_of_ne hj]
    have hinj : ∀ a ∈ t, ∀ b ∈ t, lower a = lower b → a = b := by
      intro a ha b hb hab
      rw [← hlower a ha, ← hlower b hb, hab]
    have hterm (a : ι → ℕ) (ha : a ∈ t) :
        (coeff (g i) (lower a)) ^ 2 = (a i : ℝ) * (coeff f a) ^ 2 := by
      have ha' : 0 < a i := (Finset.mem_filter.mp ha).2
      rw [hcoeff, hlower a ha, mul_pow, Real.sq_sqrt (by positivity)]
      congr 1
      simp only [lower, Function.update_self]
      exact_mod_cast (show a i - 1 + 1 = a i by omega)
    calc
      _ = ∑ a ∈ t, (a i : ℝ) * (coeff f a) ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro a ha hna
        have hz : a i = 0 := by
          have : ¬ 0 < a i := by simpa [t, ha] using hna
          omega
        simp [hz]
      _ = ∑ a ∈ t, (coeff (g i) (lower a)) ^ 2 := by
        exact Finset.sum_congr rfl (fun a ha => (hterm a ha).symm)
      _ = ∑ b ∈ t.image lower, (coeff (g i) b) ^ 2 := by
        rw [Finset.sum_image hinj]
      _ ≤ _ := h_SlowEquilibration_GaussianHermiteDerivative_finite_coeff_square_sum_le (hg i) _
  calc
    _ = ∑ a ∈ s, ∑ i, (a i : ℝ) * (coeff f a) ^ 2 := by
      simp only [degree, Nat.cast_sum, Finset.sum_mul]
    _ = ∑ i, ∑ a ∈ s, (a i : ℝ) * (coeff f a) ^ 2 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hcoord i)
end SlowEquilibration.GaussianHermiteDerivative
