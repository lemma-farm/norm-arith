module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.PSeries

-- ==== Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.vfb5dd9e085a6.MeyerGeneralProblem.Hermite.Scale ====
public section
@[expose] public section
/-!
# Hermite Hilbert scales in normalized coefficient coordinates

At each integer order, the weighted Hermite coefficient space is identified
isometrically with plain `ℓ²` by absorbing the order-dependent weight into the
coordinates.  Keeping the order in the type records which decoding is meant,
while the Fourier transform is the same diagonal fourth-root-of-unity unitary
on every normalized scale.
-/
namespace MeyerGeneralProblem
noncomputable section
open scoped ComplexConjugate

/-- The raw Hermite coefficient of order `n` is normalized by
`(1+n)^m` in the order-`m` scale. -/
def hermiteScaleWeight (m : ℤ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ m

end
end MeyerGeneralProblem

end
end

-- ==== Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.vfb5dd9e085a6.MeyerGeneralProblem.Hermite.Functions ====
public section
@[expose] public section
/-!
# Concrete Hermite functions

This file starts the genuine analytic bridge between the abstract normalized
coefficient model in `Hermite.Scale` and tempered distributions.  It bundles
polynomially weighted complex Gaussians as Schwartz functions and then defines
the standard Fourier-compatible Hermite functions

`2^(1/4) / sqrt(n!) * He_n(2 * sqrt(pi) * x) * exp(-pi * x^2)`.

Here `He_n` is mathlib's probabilists' Hermite polynomial.  The scaling is the
one for which the real Fourier transform with kernel `exp(-2*pi*i*x*xi)` has
eigenvalue `(-i)^n`; the Fourier theorem and the coefficient summability needed
for Dirac masses are deliberately proved in later bridge modules.
-/
namespace MeyerGeneralProblem
noncomputable section
open Filter Function Set
open scoped ContDiff Topology
/-- The polynomial multiplying a Gaussian after `n` real derivatives.

If `g x = exp (-b * x^2)`, differentiation sends `P * g` to
`(P' - 2 * b * X * P) * g`.
-/
def gaussianDerivativePolynomial (b : ℂ) : ℕ → Polynomial ℂ → Polynomial ℂ
  | 0, P => P
  | n + 1, P =>
      (gaussianDerivativePolynomial b n P).derivative -
        Polynomial.C (2 * b) * Polynomial.X * gaussianDerivativePolynomial b n P

/-- Exact formula for every real derivative of a polynomial times a complex
Gaussian. -/
axiom iteratedDeriv_polynomial_mul_cexp_neg_quadratic
    (P : Polynomial ℂ) (b : ℂ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ P.eval (y : ℂ) * Complex.exp (-b * (y : ℂ) ^ 2)) x =
      (gaussianDerivativePolynomial b n P).eval (x : ℂ) *
        Complex.exp (-b * (x : ℂ) ^ 2)
/-- A complex polynomial restricted to the real line has temperate growth. -/
axiom polynomial_eval_real_hasTemperateGrowth (P : Polynomial ℂ) :
    Function.HasTemperateGrowth (fun x : ℝ ↦ P.eval (x : ℂ))
/-- Polynomially weighted complex Gaussians, together with any additional
power of `|x|`, are bounded when the quadratic coefficient has positive real
part. -/
axiom exists_polynomial_mul_cexp_neg_quadratic_bound
    (P : Polynomial ℂ) {b : ℂ} (hb : 0 < b.re) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      |x| ^ k * ‖P.eval (x : ℂ) * Complex.exp (-b * (x : ℂ) ^ 2)‖ ≤ C
/-- A polynomial times `exp (-b*x^2)`, for `re b > 0`, as a bundled
Schwartz function. -/
def polynomialGaussian (P : Polynomial ℂ) (b : ℂ) (hb : 0 < b.re) : SchwartzMap ℝ ℂ where
  toFun x := P.eval (x : ℂ) * Complex.exp (-b * (x : ℂ) ^ 2)
  smooth' := by
    have hG : ContDiff ℝ ∞ (fun x : ℝ ↦ Complex.exp (-b * (x : ℂ) ^ 2)) := by
      have hOfReal : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
      fun_prop
    exact (polynomial_eval_real_hasTemperateGrowth P).1.mul hG
  decay' k n := by
    obtain ⟨C, hC⟩ :=
      exists_polynomial_mul_cexp_neg_quadratic_bound
        (gaussianDerivativePolynomial b n P) hb k
    refine ⟨C, fun x ↦ ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_polynomial_mul_cexp_neg_quadratic]
    simpa only [Real.norm_eq_abs] using hC x

/-- The probabilists' Hermite polynomial with coefficients promoted to `ℂ`. -/
def complexHermitePolynomial (n : ℕ) : Polynomial ℂ :=
  (Polynomial.hermite n).map (Int.castRingHom ℂ)

/-- The polynomial `He_n(2 * sqrt(pi) * x)` in the Fourier-compatible
Hermite function. -/
def scaledHermitePolynomial (n : ℕ) : Polynomial ℂ :=
  (complexHermitePolynomial n).comp
    (Polynomial.C (2 * Real.sqrt Real.pi : ℂ) * Polynomial.X)

/-- The unnormalised Schwartz Hermite function
`He_n(2*sqrt(pi)*x) * exp(-pi*x^2)`. -/
def hermiteFunctionCore (n : ℕ) : SchwartzMap ℝ ℂ :=
  polynomialGaussian (scaledHermitePolynomial n) (Real.pi : ℂ)
    (by simpa using Real.pi_pos)

/-- Multiplication by the real coordinate on complex Schwartz space. -/
def coordinateMultiplicationCLM : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))

/-- The creation operator `2*pi*x - d/dx` on complex Schwartz space. -/
def hermiteCreationOperator : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (2 * (Real.pi : ℂ)) • coordinateMultiplicationCLM -
    SchwartzMap.derivCLM ℂ ℂ

/-- The positive real normalization `2^(1/4) / sqrt(n!)`, written using
nested square roots to avoid branch choices. -/
def hermiteFunctionNormalization (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt 2) / Real.sqrt n.factorial

/-- The standard `L²`-normalized Hermite function for mathlib's Fourier
convention:

`2^(1/4) / sqrt(n!) * He_n(2 * sqrt(pi) * x) * exp(-pi*x^2)`.

This is a genuine Schwartz function, not an abstract coefficient atom.
-/
def normalizedHermiteSchwartz (n : ℕ) : SchwartzMap ℝ ℂ :=
  (hermiteFunctionNormalization n : ℂ) •
    hermiteFunctionCore n

end
end MeyerGeneralProblem

end
end

-- ==== Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Examples.Example_1f821ef731eca6975116_HermitePointMass ====
@[expose] public section
/-!
# Hermite coefficients of a Dirac mass

This module records the concrete normalized coefficient sequence of a Dirac
mass at `x`, proves its square summability at every integer order `m ≥ 1`, and
packages it as a genuine element of the negative Hermite scale.
-/
namespace MeyerGeneralProblem
noncomputable section
/-- The normalized order-`-m` Hermite coefficient sequence of evaluation at
`x`: `(1+n)^(-m) h_n(x)`.

The theorem `hermiteDiracCoefficients_memℓp` below proves that this sequence is
an element of `HermiteScale (-(m : ℤ))` whenever `m ≥ 1`.
-/
def hermiteDiracCoefficients (m : ℕ) (x : ℝ) (n : ℕ) : ℂ :=
  (hermiteScaleWeight (-(m : ℤ)) n : ℂ) *
    normalizedHermiteSchwartz n x

/-- The squared normalized Dirac coefficient is bounded by a convergent
`p = 3/2` majorant, uniformly in the evaluation point. -/
axiom hermiteDiracCoefficients_norm_sq_le
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (n : ℕ) :
    ‖hermiteDiracCoefficients m x n‖ ^ 2 ≤
      (2 * Real.sqrt (2 * Real.pi)) /
        (((n : ℝ) + 1) ^ (3 / 2 : ℝ))
/-- Dirac evaluation belongs to every negative integer Hermite scale of order
at least one.  This is the first genuine point-evaluation summability theorem,
not an abstract coefficient-space hypothesis. -/
theorem hermiteDiracCoefficients_memℓp
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    Memℓp (hermiteDiracCoefficients m x) 2 := by
  have hs₀ : Summable (fun n : ℕ =>
      1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
  have hs : Summable (fun n : ℕ =>
      (2 * Real.sqrt (2 * Real.pi)) /
        (((n : ℝ) + 1) ^ (3 / 2 : ℝ))) := by
    apply (hs₀.mul_left (2 * Real.sqrt (2 * Real.pi))).congr
    intro n
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    ring
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat]
  exact hs.of_nonneg_of_le
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _) fun n => by
      simpa only [Real.rpow_two] using
        hermiteDiracCoefficients_norm_sq_le m hm x n
end
end MeyerGeneralProblem
