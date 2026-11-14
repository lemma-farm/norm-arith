module

public import Mathlib
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.vd9214b13f109.MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonSaddle ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-!
# Unique nondegenerate saddle of the actual source carrier

The same real parameter b covers zero (the logarithmic main term)
and the two prospective Bessel carriers sqrt(n) and -sqrt(n).
A is the normalized height; the consumer substitutes T/(2*pi).
These exact calculus statements are not a stationary-phase estimate.
-/
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
def atkinsonSaddleRoot (A b : ℝ) : ℝ := (b + Real.sqrt (b ^ 2 + 4 * A)) / 2

end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.vd9214b13f109.MathCollab.Density.Stronger.Atkinson.AtkinsonRootPhase ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-!
# Square-root coordinates for both actual Atkinson carriers

The divisor frequency enters linearly. The normalized phase has
curvature at most minus two, and its slope is factored at the
actual positive saddle. No stationary approximation is assumed.
-/
noncomputable section
open Complex Set
open scoped ContDiff
namespace MathCollab.Density.Stronger.Atkinson
def atkinsonRootPhase (T b y : ℝ) : ℝ :=
  (T / Real.pi) * Real.log y - y ^ 2 + 2 * b * y
end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.vd9214b13f109.MathCollab.Density.Stronger.Atkinson.AtkinsonRootIntegral ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-!
# Uniform integral bound through the actual saddle

Two nonstationary tails and a length-two central interval give one
bound for every positive interval and every real carrier parameter.
The divisor frequency and its sign do not enter the bound.
-/
noncomputable section
open Complex MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson
def atkinsonRootKernel (T b y : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * I * (atkinsonRootPhase T b y : ℂ))
end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_d6563eb9afbe8769c930_AtkinsonSaddleTaylor ====
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-!
# Quantitative quadratic remainder at the actual root saddle

The cubic error is derived from the true logarithm, with no supplied
stationary-phase estimate. It controls the actual oscillatory kernel locally.
-/
noncomputable section
open Complex
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonRootQuadratic (T b y : ℝ) : ℝ :=
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  atkinsonRootPhase T b r - (1 + (T / (2 * Real.pi)) / r ^ 2) * (y - r) ^ 2


set_option linter.unusedVariables false in
theorem norm_atkinsonRootKernel_sub_quadratic_le {T y : ℝ} (hT : 0 < T) (b : ℝ)
    (hy : |y - atkinsonSaddleRoot (T / (2 * Real.pi)) b| ≤
      atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2) 
    (h_MathCollab_Density_Stronger_Atkinson_norm_exp_real_phase_sub_le : ∀ (a b : ℝ), ‖Complex.exp ((↑a : ℂ) * Complex.I) - Complex.exp ((↑b : ℂ) * Complex.I)‖ ≤ |a - b|)
    (h_MathCollab_Density_Stronger_Atkinson_abs_atkinsonRootPhase_sub_quadratic_le : ∀ {T y : ℝ},
      0 < T →
        ∀ (b : ℝ),
          |y - MathCollab.Density.Stronger.Atkinson.atkinsonSaddleRoot (T / (2 * Real.pi)) b| ≤
              MathCollab.Density.Stronger.Atkinson.atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2 →
            |MathCollab.Density.Stronger.Atkinson.atkinsonRootPhase T b y -
                  MathCollab.Density.Stronger.Atkinson.atkinsonRootQuadratic T b y| ≤
              2 * T *
                  |y - MathCollab.Density.Stronger.Atkinson.atkinsonSaddleRoot (T / (2 * Real.pi)) b| ^
                    3 /
                (Real.pi *
                  MathCollab.Density.Stronger.Atkinson.atkinsonSaddleRoot (T / (2 * Real.pi)) b ^ 3))
    :
    ‖atkinsonRootKernel T b y - Complex.exp
      (((2 * Real.pi * atkinsonRootQuadratic T b y : ℝ) : ℂ) * I)‖ ≤
      4 * T * |y - atkinsonSaddleRoot (T / (2 * Real.pi)) b| ^ 3 /
        (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3 := by
  have he : atkinsonRootKernel T b y =
      Complex.exp (((2 * Real.pi * atkinsonRootPhase T b y : ℝ) : ℂ) * I) := by
    unfold atkinsonRootKernel
    congr 1
    push_cast
    ring
  rw [he]
  apply (h_MathCollab_Density_Stronger_Atkinson_norm_exp_real_phase_sub_le _ _).trans
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply (mul_le_mul_of_nonneg_left (h_MathCollab_Density_Stronger_Atkinson_abs_atkinsonRootPhase_sub_quadratic_le hT b hy)
    (show 0 ≤ 2 * Real.pi by positivity)).trans_eq
  field_simp
  ring
end MathCollab.Density.Stronger.Atkinson
