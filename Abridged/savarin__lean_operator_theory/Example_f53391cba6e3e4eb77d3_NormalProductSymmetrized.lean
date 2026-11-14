import Mathlib
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

-- ==== Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.SpectralSet.Basic ====
section
/-
# Polynomial spectral sets — definitions (L2.1)

Defines `polynomialSupNorm`, `IsKPolynomialSpectralSet`, and `IsPolynomialSpectralSet`.
These are *polynomial* spectral sets (norm bound on `Polynomial.aeval`).
-/
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open scoped Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
noncomputable def polynomialSupNorm (p : Polynomial ℂ) (X : Set ℂ) : ℝ :=
  ⨆ z ∈ X, ‖Polynomial.eval z p‖

end

-- ==== Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ContourIntegral ====
section
/-
# Parameterized contour integrals (L4.2a)

Contour integrals along a parameterized closed curve `γ : ℝ → ℂ`, defined as the interval
integral `∫ t in 0..2π, deriv γ t • f (γ t)`.  This is exactly the shape of Mathlib's
`circleIntegral` (the special case `γ = circleMap c R`), so the circle results of
`CircleCauchy.lean` transfer by `rfl`, while general smooth boundaries of convex domains — the
contours of the Crouzeix–Palencia argument — become available.

## Main declarations

* `ContourIntegrable f γ` — integrability of `t ↦ deriv γ t • f (γ t)` on `[0, 2π]`.
* `contourIntegral f γ` — the contour integral `∫ t in 0..2π, deriv γ t • f (γ t)`.
* `contourIntegral_circleMap`, `contourIntegrable_circleMap_iff` — agreement with Mathlib's
  `circleIntegral` / `CircleIntegrable` for `γ = circleMap c R`.
* `ContourIntegrable.of_continuousOn` — continuity of the curve derivative and of `f` on the
  trace gives integrability.
* `contourIntegral_add`, `contourIntegral_sub`, `contourIntegral_neg`, `contourIntegral_smul` —
  linearity in the integrand.
* `ContinuousLinearMap.contourIntegral_comp_comm`, `contourIntegral_const_mul`,
  `contourIntegral_mul_const` — continuous linear maps and constant algebra factors commute
  with the integral.
* `norm_contourIntegral_le_of_norm_le_const` — the length-type bound `‖∫‖ ≤ 2π C`.
* `contourIntegral_eq_sub_of_hasDerivAt`, `contourIntegral_eq_zero_of_hasDerivAt_of_closed` —
  the fundamental theorem of calculus along `γ`: an integrand with a global primitive
  integrates to the boundary difference, hence to `0` along a closed curve (Cauchy's theorem
  for integrands with a primitive).
-/
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
/-- `f` is integrable along the parameterized curve `γ` over `[0, 2π]`: the integrand
`t ↦ deriv γ t • f (γ t)` is interval integrable. -/
def ContourIntegrable (f : ℂ → F) (γ : ℝ → ℂ) : Prop :=
  IntervalIntegrable (fun t => deriv γ t • f (γ t)) volume 0 (2 * π)
/-- The contour integral `∫ t in 0..2π, γ'(t) • f (γ t)` of `f` along the parameterized curve
`γ`. -/
noncomputable def contourIntegral (f : ℂ → F) (γ : ℝ → ℂ) : F :=
  ∫ t in (0 : ℝ)..(2 * π), deriv γ t • f (γ t)

section Linearity
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

end Linearity

end

-- ==== Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothApprox ====
section
/-
# Smooth Jordan domains containing compact planar sets

This file supplies the first kernel-checked part of L4.2b.  It packages the
geometric data needed to integrate around the boundary of a smooth strictly
convex planar domain and proves that every compact set in `ℂ` is contained in
such a domain: take a sufficiently large open disk.

The stronger approximation needed by the full Crouzeix--Palencia argument --
a nested sequence of smooth domains whose intersection is the original compact
convex set -- is not asserted here.  In particular, the enclosing-disk theorem
must not be mistaken for that remaining planar approximation result.

The imports have separate roles: `Strict` supplies strict convexity of open
convex sets, `Ball.Pointwise` identifies closures of metric thickenings,
`RCLike.Real` identifies the frontier of a complex ball, and `CircleIntegral`
supplies the smooth regular circle parametrization API.
-/
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Metric Set
open scoped ContDiff
/-- A smooth Jordan domain, represented by a `2π`-periodic regular boundary
parametrization.  Injectivity is imposed on the half-open fundamental interval
`[0, 2π)`, so the periodic identification of its two endpoints is the only
allowed repetition there. -/
structure SmoothJordanDomain where
  carrier : Set ℂ
  isOpen_carrier : IsOpen carrier
  strictConvex_carrier : StrictConvex ℝ carrier
  boundaryParam : ℝ → ℂ
  boundaryParam_periodic : Function.Periodic boundaryParam (2 * Real.pi)
  boundaryParam_contDiff : ContDiff ℝ ∞ boundaryParam
  boundaryParam_range : Set.range boundaryParam = frontier carrier
  boundaryParam_injOn : Set.InjOn boundaryParam (Set.Ico 0 (2 * Real.pi))
  boundaryParam_regular : ∀ t, deriv boundaryParam t ≠ 0
/-- A positive-radius open disk, with `circleMap` as its smooth Jordan boundary. -/
noncomputable def SmoothJordanDomain.ball (c : ℂ) (R : ℝ) (hR : 0 < R) :
    SmoothJordanDomain where
  carrier := Metric.ball c R
  isOpen_carrier := Metric.isOpen_ball
  strictConvex_carrier := (convex_ball c R).strictConvex_of_isOpen Metric.isOpen_ball
  boundaryParam := circleMap c R
  boundaryParam_periodic := periodic_circleMap c R
  boundaryParam_contDiff := contDiff_circleMap c R
  boundaryParam_range := by
    rw [range_circleMap, abs_of_pos hR, frontier_ball c hR.ne']
  boundaryParam_injOn := by
    apply injOn_circleMap_of_abs_sub_le' hR.ne'
    simp only [sub_zero]
    exact le_rfl
  boundaryParam_regular := fun _ => deriv_circleMap_ne_zero hR.ne'

end

-- ==== Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.AuxOperator ====
section
/-
# The Crouzeix--Palencia auxiliary operator (L4.2c)

This file supplies the kernel-checked contour-integral part of the auxiliary
operator construction.  If a smooth Jordan domain `Omega` strictly contains
`closure (numericalRange A)`, every point of its boundary lies in the
resolvent set of `A`.  Consequently, any continuous scalar boundary datum
`h` gives an integrable operator-valued kernel
`z ↦ h z • resolvent A z` and hence the bounded operator

`G = (2 * pi * i)⁻¹ • contourIntegral (h • resolvent A) Omega.boundaryParam`.

The sharp L4.2d/e estimates are intentionally not asserted here: they require
identifying the resulting contour expressions through boundary
Cauchy-transform identities.  Mathlib has no located Plemelj boundary-value
theorem from which those identities follow directly.

## Main declarations

* `SmoothJordanDomain.boundaryParam_mem_resolventSet` -- the boundary of a
  domain containing `closure (numericalRange A)` lies in the resolvent set.
* `exists_smoothJordanDomain_for_numericalRange` -- such a containing smooth
  Jordan domain exists for every bounded operator.
* `crouzeixAuxiliaryIntegrand_contourIntegrable` -- continuity of the scalar
  boundary datum implies integrability of the operator-valued kernel.
* `crouzeixAuxiliaryOperator` -- the normalized contour-integral operator.
* `crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable` -- integrability
  for conjugate polynomial boundary values.
* `crouzeixPolynomialAuxiliaryOperator` -- its specialization to the
  conjugate boundary values of a polynomial.
* `exists_bound_crouzeixPolynomialAuxiliaryIntegrand` -- the polynomial
  resolvent kernel is uniformly bounded along the compact parameter interval.
* `norm_crouzeixAuxiliaryOperator_le` -- its explicit contour-length bound.
* `exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator` --
  the packaged bounded auxiliary-operator construction.
-/
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace SmoothJordanDomain

end SmoothJordanDomain

/-- The normalized Crouzeix--Palencia auxiliary operator associated to a
scalar boundary datum `h` on a smooth Jordan domain. -/
noncomputable def crouzeixAuxiliaryOperator (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (h : ℂ → ℂ) : E →L[ℂ] E :=
  (2 * (Real.pi : ℂ) * I)⁻¹ •
    contourIntegral (fun z => h z • resolvent A z) Omega.boundaryParam

noncomputable def crouzeixPolynomialAuxiliaryOperator (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : E →L[ℂ] E :=
  crouzeixAuxiliaryOperator A Omega (fun z => star (Polynomial.eval z p))

end

-- ==== Examples.savarin__lean_operator_theory.Examples.Example_f53391cba6e3e4eb77d3_NormalProductSymmetrized ====
/-
# Universal circle symmetrization implies the normal auxiliary product bound

For any operator, the sharp symmetrized estimate on every polynomial forces
an enclosing circle's center into the closed numerical range.  Indeed, if the
center were outside, an affine polynomial separator would have value one at
the center and norm at most `r < 1` on the closed numerical range.  Applying
symmetrization to its powers makes the functional-calculus term tend to zero
by the unconditional Crouzeix--Palencia bound, while the circle auxiliary
remains the identity, a contradiction.

The aligned-circle normal product theorem then supplies the literal sharp
auxiliary product estimate.

## Main declarations

* `circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  proves alignment over a compact nonempty convex control set directly from
  universal symmetrization.
* `circle_center_mem_of_isCompact_nonempty_convex_of_global_polynomial_bound_of_forall_symmetrized_bound`
  retains the earlier finite-calculus interface as a corollary.
* `circle_center_mem_closure_numericalRange_of_global_polynomial_bound_of_forall_symmetrized_bound`
  specializes that result to the closed numerical range.
* `circle_center_mem_closure_numericalRange_of_forall_symmetrized_bound`
  specializes direct center alignment to the closed numerical range.
* `norm_pow_aeval_le_two_mul_pow_polynomialSupNorm_of_eval_eq_zero_of_forall_symmetrized_bound`
  gives a uniform power bound on the polynomial ideal vanishing at the circle
  center.
* `norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound`
  preserves the coupled operator/scalar cancellation for every shifted power.
* `norm_pow_aeval_sub_eval_smul_one_le_two_mul_pow_polynomialSupNorm_sub_C_of_forall_symmetrized_bound`
  gives the corresponding centered power bound for every polynomial.
* `spectrum_aeval_sub_eval_smul_one_subset_closedBall_of_forall_symmetrized_bound`
  derives the sharp centered spectral inclusion from those power bounds.
* `spectrum_aeval_subset_closedBall_eval_of_forall_symmetrized_bound`
  translates that inclusion back to the spectrum of `p(A)`.
* `spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound`
  gives the analogous sharp spectral disk around every scalar shift.
* `spectrum_aeval_subset_closedBall_shift_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  discharges center membership from compact convex geometry.
* `spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_mem_of_forall_symmetrized_bound`
  converts a shifted disk and center membership to a shifted spectral radius.
* `spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  gives the sharp spectral-radius bound after every scalar shift.
* `spectralRadius_aeval_le_polynomialSupNorm_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  records its zero-shift specialization.
* `spectrum_aeval_subset_closedBall_shift_closure_numericalRange_of_forall_symmetrized_bound`
  specializes every shifted disk to the closed numerical range.
* `spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_closure_numericalRange_of_forall_symmetrized_bound`
  gives the corresponding sharp shifted spectral-radius bound.
* `spectralRadius_aeval_le_polynomialSupNorm_closure_numericalRange_of_forall_symmetrized_bound`
  gives its zero-shift consequence.
* `spectrum_subset_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  proves that the compact convex control set itself contains the spectrum.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_eval_center_le_sqrt_two_sub_one_mul`
  proves the sharp product bound without normality when the center value is
  at most `sqrt 2 - 1` times the control norm.
* `norm_aeval_le_two_mul_polynomialSupNorm_sub_C_add_norm_eval_sub_two_mul_of_forall_symmetrized_bound`
  extracts the operator-norm estimate obtained from any scalar shift.
* `isKPolynomialSpectralSet_three_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  packages universal symmetrization as a constant-three polynomial spectral set.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_shifted_scalar_bound_of_forall_symmetrized_bound`
  exposes an arbitrary scalar shift for optimizing the product estimate.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_half_centered_scalar_bound_of_forall_symmetrized_bound`
  specializes the shift to `p(c) / 2`, eliminating the residual scalar term.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_scalar_bound_of_forall_symmetrized_bound`
  isolates the exact adaptive scalar criterion obtained by centering `p`.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_polynomialSupNorm_le_sub_of_forall_symmetrized_bound`
  proves the complementary sharp near-constant branch.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_one_add_sqrt_two_mul_sq_of_forall_symmetrized_bound`
  gives the resulting product estimate for an arbitrary operator at the
  global Crouzeix--Palencia factor.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_aeval_of_forall_symmetrized_bound`
  gives the sharp product estimate whenever the individual value `p(A)` is
  star-normal.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_of_forall_symmetrized_bound`
  specializes the sharp estimate to a star-normal operator.
-/
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


set_option linter.unusedVariables false in
theorem spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K) (hc : c ∈ K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) 
    (h_norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound : ∀ {E : Type u} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℂ E]
      [inst_2 : CompleteSpace E] (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hA : ‖A - c • 1‖ < R) {K : Set ℂ},
      IsCompact K →
        (∀ (q : Polynomial ℂ),
            ‖(Polynomial.aeval A : Polynomial ℂ → E →L[ℂ] E) q +
                  Star.star
                    (crouzeixPolynomialAuxiliaryOperator A
                      (SmoothJordanDomain.ball c R (LE.le.trans_lt (norm_nonneg (A - c • 1)) hA)) q)‖ ≤
              2 * polynomialSupNorm q K) →
          ∀ (p : Polynomial ℂ) (b : ℂ) (n : ℕ),
            ‖((Polynomial.aeval A : Polynomial ℂ → E →L[ℂ] E) p - b • 1) ^ (n + 1) +
                  (Polynomial.eval c p - b) ^ (n + 1) • 1‖ ≤
              2 * polynomialSupNorm (p - (Polynomial.C : ℂ → Polynomial ℂ) b) K ^ (n + 1))
    (h_bddAbove_norm_eval_image_of_isCompact : ∀ (p : Polynomial ℂ) {K : Set ℂ},
      IsCompact K → BddAbove ((fun (z : ℂ) ↦ ‖Polynomial.eval z p‖) '' K))
    (h_norm_eval_le_polynomialSupNorm : ∀ (p : Polynomial ℂ) {X : Set ℂ},
      BddAbove ((fun (z : ℂ) ↦ ‖Polynomial.eval z p‖) '' X) →
        ∀ {z : ℂ}, z ∈ X → ‖Polynomial.eval z p‖ ≤ polynomialSupNorm p X)
    (h_polynomialSupNorm_nonneg : ∀ (p : Polynomial ℂ) (X : Set ℂ), 0 ≤ polynomialSupNorm p X)
    :
    spectrum ℂ (Polynomial.aeval A p) ⊆
      Metric.closedBall b (polynomialSupNorm (p - Polynomial.C b) K) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  let _ := hE
  let T : E →L[ℂ] E := Polynomial.aeval A p -
    b • (1 : E →L[ℂ] E)
  let a : ℂ := Polynomial.eval c p - b
  let m : ℝ := polynomialSupNorm (p - Polynomial.C b) K
  have ha : ‖a‖ ≤ m := by
    have h := h_norm_eval_le_polynomialSupNorm (p - Polynomial.C b)
      (h_bddAbove_norm_eval_image_of_isCompact (p - Polynomial.C b) hK) hc
    simpa only [a, m, Polynomial.eval_sub, Polynomial.eval_C] using h
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  let w : ℂ := z - b
  have hw : w ∈ spectrum ℂ T := by
    have hshift : spectrum ℂ T =
        spectrum ℂ (Polynomial.aeval A p) - ({b} : Set ℂ) := by
      dsimp only [T]
      rw [← Algebra.algebraMap_eq_smul_one,
        ← spectrum.sub_singleton_eq]
    rw [hshift]
    exact ⟨z, hz, b, Set.mem_singleton b, rfl⟩
  by_contra hwm
  have hm : 0 ≤ m := h_polynomialSupNorm_nonneg _ _
  have hmw : m < ‖w‖ := lt_of_not_ge hwm
  have hwpos : 0 < ‖w‖ := hm.trans_lt hmw
  have hratio_nonneg : 0 ≤ m / ‖w‖ := div_nonneg hm hwpos.le
  have hratio_lt_one : m / ‖w‖ < 1 := (div_lt_one hwpos).2 hmw
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (m / ‖w‖) ^ n < (1 / 3 : ℝ) :=
    exists_pow_lt_of_lt_one (by norm_num) hratio_lt_one
  have hratio_succ : 3 * (m / ‖w‖) ^ (n + 1) < 1 := by
    have hratio_le_one : m / ‖w‖ ≤ 1 := hratio_lt_one.le
    have hpow_succ : (m / ‖w‖) ^ (n + 1) ≤ (m / ‖w‖) ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hratio_nonneg n) hratio_le_one
    nlinarith only [hn, hpow_succ]
  have hwpow_mem : w ^ (n + 1) ∈ spectrum ℂ (T ^ (n + 1)) :=
    spectrum.pow_mem_pow T (n + 1) hw
  have hadd_mem : w ^ (n + 1) + a ^ (n + 1) ∈
      spectrum ℂ (T ^ (n + 1) +
        a ^ (n + 1) • (1 : E →L[ℂ] E)) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.add_singleton_eq]
    exact ⟨w ^ (n + 1), hwpow_mem, a ^ (n + 1),
      Set.mem_singleton _, rfl⟩
  have hadd_le : ‖w ^ (n + 1) + a ^ (n + 1)‖ ≤
      ‖T ^ (n + 1) + a ^ (n + 1) • (1 : E →L[ℂ] E)‖ :=
    spectrum.norm_le_norm_of_mem hadd_mem
  have hmoment : ‖T ^ (n + 1) +
      a ^ (n + 1) • (1 : E →L[ℂ] E)‖ ≤ 2 * m ^ (n + 1) := by
    simpa only [T, a, m] using
      h_norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound
        A c hA hK hsymm p b n
  have hapow : ‖a‖ ^ (n + 1) ≤ m ^ (n + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) ha (n + 1)
  have hwpow_le : ‖w‖ ^ (n + 1) ≤ 3 * m ^ (n + 1) := by
    calc
      ‖w‖ ^ (n + 1) = ‖w ^ (n + 1)‖ := (norm_pow w (n + 1)).symm
      _ = ‖(w ^ (n + 1) + a ^ (n + 1)) - a ^ (n + 1)‖ := by
        rw [add_sub_cancel_right]
      _ ≤ ‖w ^ (n + 1) + a ^ (n + 1)‖ + ‖a ^ (n + 1)‖ :=
        norm_sub_le _ _
      _ ≤ 2 * m ^ (n + 1) + m ^ (n + 1) := by
        simpa only [norm_pow] using add_le_add (hadd_le.trans hmoment) hapow
      _ = 3 * m ^ (n + 1) := by ring
  have hstrict : 3 * m ^ (n + 1) < ‖w‖ ^ (n + 1) := by
    calc
      3 * m ^ (n + 1) =
          (3 * (m / ‖w‖) ^ (n + 1)) * ‖w‖ ^ (n + 1) := by
            rw [div_pow]
            field_simp
      _ < 1 * ‖w‖ ^ (n + 1) :=
        mul_lt_mul_of_pos_right hratio_succ (pow_pos hwpos (n + 1))
      _ = ‖w‖ ^ (n + 1) := one_mul _
  exact (not_lt_of_ge hwpow_le) hstrict
