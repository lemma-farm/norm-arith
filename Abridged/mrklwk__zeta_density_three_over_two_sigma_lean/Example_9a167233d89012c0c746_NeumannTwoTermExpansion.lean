module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.RCLike.Sqrt

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v001436028ebf.MathCollab.Density.Stronger.Atkinson.BesselY0 ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from DFIBesselKernel.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
/-- The exponentially decaying term in Schläfli's real integral
representation of the order-zero Neumann kernel. -/
noncomputable def dfiBesselY0Tail (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Real.exp (-x * t) / Real.sqrt (1 + t ^ 2)
/-- The oscillatory term in Schläfli's representation, written after the
change of variables `u = π/2 - θ`.  Taking the imaginary part packages the
real sine integral while retaining the complex exponential needed for the
first-derivative estimate. -/
noncomputable def dfiBesselY0Osc (x : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..Real.pi / 2,
    Complex.exp (Complex.I * (x * Real.cos u))).im
/-- DFI's order-zero Neumann kernel, defined by the DLMF/Schläfli integral
representation
`Y₀(x) = (2/π) ( ∫₀^π/² sin(x cos u) du
                         - ∫₀^∞ exp(-xt)/sqrt(1+t²) dt )`.
The representation is used only for positive arguments, exactly as in DFI
Proposition 1. -/
noncomputable def dfiBesselY0 (x : ℝ) : ℝ :=
  (2 / Real.pi) * (dfiBesselY0Osc x - dfiBesselY0Tail x)
end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v001436028ebf.MathCollab.Density.Stronger.Atkinson.NeumannLaplaceAmplitude ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannLaplaceAmplitude.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
/-!
# A global quadratic remainder for the complex Laplace amplitude

The inverse square root is the principal one. Its first-order
approximation and a uniform quadratic error are derived algebraically
from the actual square root, not supplied as an asymptotic premise.
-/
set_option autoImplicit false
noncomputable section
open Complex
namespace MathCollab.Density.Stronger.Atkinson
def neumannLaplaceAmplitude (u : ℝ) : ℂ :=
  (1 + (u : ℂ) * I) ^ (-(1 / 2 : ℂ))

end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v001436028ebf.MathCollab.Density.Stronger.Atkinson.NeumannRayFactorization ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannRayFactorization.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
/-!
# Factoring the genuine Neumann ray into its decaying Laplace integral

The coefficient remains an explicit principal complex half-power.
The angular phase, arithmetic normalization and entire amplitude
are retained exactly.
-/
set_option autoImplicit false
noncomputable section
open Complex Filter MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson

def neumannRayCoefficient : ℂ := (-I) ^ (-(1 / 2 : ℂ)) * (2 : ℂ) ^ (-(1 / 2 : ℂ))
def neumannLaplaceIntegrand (x t : ℝ) : ℂ :=
  ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-x * t) : ℝ) : ℂ) * neumannLaplaceAmplitude (t / 2)
def neumannLaplaceIntegral (x : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, neumannLaplaceIntegrand x t

axiom dfiBesselY0_eq_neumannLaplaceIntegral {x : ℝ} (hx : 0 < x) :
    dfiBesselY0 x = -(2 / Real.pi) *
      (Complex.exp (I * (x : ℂ)) * neumannRayCoefficient * neumannLaplaceIntegral x).re
end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v001436028ebf.MathCollab.Density.Stronger.Atkinson.NeumannLaplaceMoments ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannLaplaceMoments.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
/-!
# Exact Gaussian-half-line moments of the decaying Neumann ray

The three actual Laplace moments give the two leading terms and the
integrable quadratic remainder. All identities hold for every x > 0.
-/
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson

axiom norm_neumannRayCoefficient_le_one : ‖neumannRayCoefficient‖ ≤ 1
end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v001436028ebf.MathCollab.Density.Stronger.Atkinson.NeumannLaplaceRemainder ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannLaplaceRemainder.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
/-!
# Integrating the proved quadratic remainder on the Neumann ray

The approximation is obtained by integrating the actual constant
and linear amplitude terms. The quadratic error is integrable and
has its exact x^(-5/2) scale.
-/
set_option autoImplicit false
noncomputable section
open Complex Filter MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson
def neumannLaplaceApproximation (x : ℝ) : ℂ :=
  ((Real.sqrt Real.pi * x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) -
    I / 8 * ((Real.sqrt Real.pi * x ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)

axiom norm_neumannLaplaceIntegral_sub_approximation_le {x : ℝ} (hx : 0 < x) :
    ‖neumannLaplaceIntegral x - neumannLaplaceApproximation x‖ ≤
      (9 / 128 : ℝ) * Real.sqrt Real.pi * x ^ (-(5 / 2 : ℝ))
end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_9a167233d89012c0c746_NeumannTwoTermExpansion ====
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannTwoTermExpansion.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
/-!
# A two-term expansion of the literal order-zero Neumann kernel

The phase is written in sine/cosine coordinates to expose both
oscillatory carriers directly. The error has the globally valid
positive-argument bound C x^(-5/2).
-/
set_option autoImplicit false
noncomputable section
open Complex
namespace MathCollab.Density.Stronger.Atkinson
def neumannTwoTerm (x : ℝ) : ℝ :=
  (Real.sqrt Real.pi / Real.pi) *
    ((Real.sin x - Real.cos x) * x ^ (-(1 / 2 : ℝ)) -
      (Real.sin x + Real.cos x) / 8 * x ^ (-(3 / 2 : ℝ)))
def neumannTwoTermErrorConstant : ℝ := (2 / Real.pi) * (9 / 128 : ℝ) * Real.sqrt Real.pi
axiom neumannTwoTerm_eq_ray_approximation (x : ℝ) :
    neumannTwoTerm x = -(2 / Real.pi) *
      (Complex.exp (I * (x : ℂ)) * neumannRayCoefficient * neumannLaplaceApproximation x).re
theorem abs_dfiBesselY0_sub_neumannTwoTerm_le {x : ℝ} (hx : 0 < x) :
    |dfiBesselY0 x - neumannTwoTerm x| ≤ neumannTwoTermErrorConstant * x ^ (-(5 / 2 : ℝ)) := by
  have hcoef : ‖Complex.exp (I * (x : ℂ)) * neumannRayCoefficient‖ ≤ 1 := by
    rw [norm_mul]
    have he : ‖Complex.exp (I * (x : ℂ))‖ = 1 := by simp [Complex.norm_exp, mul_re]
    rw [he, one_mul]
    exact norm_neumannRayCoefficient_le_one
  have hp : ‖Complex.exp (I * (x : ℂ)) * neumannRayCoefficient *
      (neumannLaplaceIntegral x - neumannLaplaceApproximation x)‖ ≤
        (9 / 128 : ℝ) * Real.sqrt Real.pi * x ^ (-(5 / 2 : ℝ)) := by
    rw [norm_mul]
    calc
      _ ≤ 1 * ((9 / 128 : ℝ) * Real.sqrt Real.pi * x ^ (-(5 / 2 : ℝ))) := by
        gcongr
        exact norm_neumannLaplaceIntegral_sub_approximation_le hx
      _ = _ := one_mul _
  have heq : dfiBesselY0 x - neumannTwoTerm x = -(2 / Real.pi) *
      (Complex.exp (I * (x : ℂ)) * neumannRayCoefficient *
        (neumannLaplaceIntegral x - neumannLaplaceApproximation x)).re := by
    rw [dfiBesselY0_eq_neumannLaplaceIntegral hx, neumannTwoTerm_eq_ray_approximation]
    simp only [mul_sub, Complex.sub_re]
  rw [heq, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 / Real.pi)]
  have h := mul_le_mul_of_nonneg_left
    ((Complex.abs_re_le_norm _).trans hp) (by positivity : 0 ≤ 2 / Real.pi)
  convert h using 1
  unfold neumannTwoTermErrorConstant
  ring
end MathCollab.Density.Stronger.Atkinson
