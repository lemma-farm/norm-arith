module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v5dc4108844b3.SubdiffusiveProcess.ResponseMoments.BilinearCS
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
theorem harmonic_replacement_error_le (E : LocalEnergy V X) (u pr : V)
    (f2 nrm Kp hmesh s : ℝ) (_hs : 0 < s) (hh : 0 < hmesh) (hK : 0 ≤ Kp)
    (_hf2 : 0 ≤ f2) (_hnrm : 0 ≤ nrm)
    (hload : E.form u pr = E.form pr pr)
    (hCS : E.form u pr ≤ f2 * nrm)
    (hpoin : nrm ^ 2 ≤ Kp * hmesh ^ (2 * s) * E.form pr pr) :
    E.form pr pr ≤ Kp * hmesh ^ (2 * s) * f2 ^ 2 := by
  have hA : 0 ≤ E.form pr pr := E.form_nonneg pr
  have hpow : 0 < hmesh ^ (2 * s) := Real.rpow_pos_of_pos hh _
  have h1 : E.form pr pr ≤ f2 * nrm := by rw [← hload]; exact hCS
  rcases eq_or_lt_of_le hA with hA0 | hA0
  · rw [← hA0]
    positivity
  · have h2 : E.form pr pr ^ 2 ≤ f2 ^ 2 * nrm ^ 2 := by
      have := mul_self_le_mul_self hA h1
      nlinarith [this, _hnrm, _hf2]
    nlinarith [h2, hpoin, hA0, hpow, hK, sq_nonneg f2]
end ResponseMoments
end SubdiffusiveProcess
