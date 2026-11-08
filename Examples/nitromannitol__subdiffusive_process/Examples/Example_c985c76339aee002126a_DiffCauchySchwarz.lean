module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v6409549b3905.SubdiffusiveProcess.ResponseMoments.BilinearCS
public import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# The relative form of two candidate energies, Lemma `mfd:lem-diff`

`mfd:lem-diff`: with
`m Γ_E ≤ Γ_F ≤ M Γ_E` and `c ∈ [m, M]`, the relative measure
`Γ_D = Γ_F - c Γ_E` satisfies
`|Γ_D(u,v)|(B) ≤ Δ √(Γ_E(u)(B) Γ_E(v)(B))` with `Δ = M - m`.
The proof is matrix Cauchy--Schwarz applied to the two nonnegative
combinations `Δ Γ_E ± Γ_D`, exactly as in paper label `mfd:lem-diff`.
-/
open Real
noncomputable section
namespace SubdiffusiveProcess
namespace ResponseMoments
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {X : Type*} [MeasurableSpace X]
theorem minimizer_difference_energy_le (E F : LocalEnergy V X) (m M c : ℝ)
    (hm : 0 < m) (_hmc : m ≤ c) (_hcM : c ≤ M) (uE w : V)
    (hcoercive : m * E.form w w ≤ F.form w w)
    (heuler : F.form w w = -(F.form uE w - c * E.form uE w))
    (hCS : |F.form uE w - c * E.form uE w| ≤
      (M - m) * Real.sqrt (E.form uE uE * E.form w w)) :
    E.form w w ≤ ((M - m) / m) ^ 2 * E.form uE uE := by
  have hEu : 0 ≤ E.form uE uE := E.form_nonneg uE
  have hEw : 0 ≤ E.form w w := E.form_nonneg w
  have hsplit : Real.sqrt (E.form uE uE * E.form w w) =
      Real.sqrt (E.form uE uE) * Real.sqrt (E.form w w) := Real.sqrt_mul hEu _
  have hneg : -(F.form uE w - c * E.form uE w) ≤
      |F.form uE w - c * E.form uE w| := neg_le_abs _
  have hkey : m * E.form w w ≤
      (M - m) * (Real.sqrt (E.form uE uE) * Real.sqrt (E.form w w)) := by
    rw [← hsplit]
    calc m * E.form w w ≤ F.form w w := hcoercive
      _ = -(F.form uE w - c * E.form uE w) := heuler
      _ ≤ |F.form uE w - c * E.form uE w| := hneg
      _ ≤ (M - m) * Real.sqrt (E.form uE uE * E.form w w) := hCS
  have hy : Real.sqrt (E.form w w) ^ 2 = E.form w w := Real.sq_sqrt hEw
  have hx : Real.sqrt (E.form uE uE) ^ 2 = E.form uE uE := Real.sq_sqrt hEu
  have hynn : 0 ≤ Real.sqrt (E.form w w) := Real.sqrt_nonneg _
  have hxnn : 0 ≤ Real.sqrt (E.form uE uE) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hynn with hy0 | hy0
  · have : E.form w w = 0 := by rw [← hy, ← hy0]; ring
    rw [this]
    positivity
  · have hstep : m * Real.sqrt (E.form w w) ≤ (M - m) * Real.sqrt (E.form uE uE) := by
      have := hkey
      rw [← hy] at this
      nlinarith [this, hy0]
    have hdiv : Real.sqrt (E.form w w) ≤ (M - m) / m * Real.sqrt (E.form uE uE) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm]
      nlinarith [hstep]
    have hsq := mul_self_le_mul_self hynn hdiv
    rw [← hy, ← hx]
    nlinarith [hsq, hxnn]
end ResponseMoments
end SubdiffusiveProcess
