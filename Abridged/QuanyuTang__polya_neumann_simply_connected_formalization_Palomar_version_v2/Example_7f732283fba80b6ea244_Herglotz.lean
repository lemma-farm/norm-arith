module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Operator.Compact
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

-- ==== Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Examples.Example_7f732283fba80b6ea244_Herglotz ====
/-!
# Herglotz waves and their driven transport equation (Lemma 4.4)

For `E = k² ≥ 0` and a direction density `a ∈ L²(0, 2π)`, the Herglotz wave is
`u_a(z) = (2π)⁻¹ ∫₀^{2π} a(φ) e^{-ik Re(z e^{-iφ})} dφ`.
Its "holomorphic jets" `y_{a,n} = (2i/k)ⁿ ∂ⁿ u_a` are the coefficients
`F_n(z) = (2π)⁻¹ ∫₀^{2π} a(φ) e^{-inφ} e^{-ik Re(z e^{-iφ})} dφ` (`herglotzCoeff`), the Fourier
coefficients of `a · e^{-ik Re(z e^{-i·})}`. The vector
`y_a(z) = (F_0(z)/√2, F_1(z), F_2(z), …)` lies in `ℓ²(ℕ₀)` by Parseval (`herglotzVec`).

Along a Lipschitz curve `γ` we prove Lemma 4.4 of the paper (`herglotz_driven`):
`y_a ∘ γ` is continuous and satisfies the driven transport equation
`y_a' = C_E y_a - (i/√2) g_a e₀` in integral form, where
`g_a(θ) = D u_a(γ(θ)) (-i γ'(θ))` is the conormal derivative `|γ'| ∂_ν u_a` (`herglotzConormal`);
moreover `h_a = u_a ∘ γ` satisfies `h_a' = -i g_a - i k γ' y_{a,1}`.

As a consequence (the pairing step of Lemma 10.5) a fixed vector `v` of `V_E = W_E(L)` has an
observation `O_E v` orthogonal to every Herglotz conormal trace:
`∫₀^{2π} conj(g_a) (O_E v) = 0` (`integral_conj_herglotzConormal_mul_observation`).
-/
@[expose] public section
open MeasureTheory Set Filter
open scoped ComplexConjugate Real Interval
noncomputable section
namespace PolyaNeumann
/-- The plane wave `e^{-ik Re(z e^{-iφ})}`. -/
def planeWave (k : ℝ) (z : ℂ) (φ : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * k) * ((z * Complex.exp (-(φ * Complex.I))).re : ℂ))
/-- The Herglotz coefficients `F_m(z) = (2π)⁻¹ ∫₀^{2π} e^{-imφ} a(φ) e^{-ik Re(z e^{-iφ})} dφ`.
For `m ≥ 1`, `F_m = (2i/k)^m ∂^m u_a`. -/
def herglotzCoeff (k : ℝ) (a : ℝ → ℂ) (m : ℤ) (z : ℂ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π),
    Complex.exp (-((m : ℂ) * φ * Complex.I)) * (a φ * planeWave k z φ)

/-! ### Basic properties -/

/-! ### Derivatives -/


set_option linter.unusedVariables false in
lemma norm_fderiv_herglotzCoeff_le {a : ℝ → ℂ} (ha : IntervalIntegrable a volume 0 (2 * π))
    (k : ℝ) (m : ℤ) (z : ℂ) 
    (h_PolyaNeumann_norm_herglotzCoeff_le : ∀ {a : ℝ → ℂ} (k : ℝ) (m : ℤ) (z : ℂ),
      ‖PolyaNeumann.herglotzCoeff k a m z‖ ≤ (2 * Real.pi)⁻¹ * ∫ (φ : ℝ) in 0..2 * Real.pi, ‖a φ‖)
    (h_PolyaNeumann_fderiv_herglotzCoeff_apply : ∀ {a : ℝ → ℂ},
      IntervalIntegrable a MeasureTheory.MeasureSpace.volume 0 (2 * Real.pi) →
        ∀ (k : ℝ) (m : ℤ) (z w : ℂ),
          (fderiv ℝ (PolyaNeumann.herglotzCoeff k a m) z : ℂ → ℂ) w =
            -(Complex.I * (↑k : ℂ) / 2) *
              (w * PolyaNeumann.herglotzCoeff k a (m + 1) z +
                (starRingEnd ℂ : ℂ → ℂ) w * PolyaNeumann.herglotzCoeff k a (m - 1) z))
    :
    ‖fderiv ℝ (herglotzCoeff k a m) z‖ ≤ |k| * ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖) := by
  set A := (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖
  have hA0 : 0 ≤ A := by
    have : 0 ≤ ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖ :=
      intervalIntegral.integral_nonneg (by positivity) fun _ _ => norm_nonneg _
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [h_PolyaNeumann_fderiv_herglotzCoeff_apply ha, norm_mul]
  have hc : ‖-(Complex.I * k / 2)‖ = |k| / 2 := by
    rw [norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]; norm_num
  rw [hc]
  have h1 := h_PolyaNeumann_norm_herglotzCoeff_le (a := a) k (m + 1) z
  have h2 := h_PolyaNeumann_norm_herglotzCoeff_le (a := a) k (m - 1) z
  calc |k| / 2 * ‖w * herglotzCoeff k a (m + 1) z + conj w * herglotzCoeff k a (m - 1) z‖
      ≤ |k| / 2 * (‖w‖ * A + ‖w‖ * A) := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_conj]
        gcongr
    _ = |k| * A * ‖w‖ := by ring

/-! ### Lemma 4.4 -/

/-! ### Every vector is Herglotz data (Lemma 4.4, last clause) -/

end PolyaNeumann
