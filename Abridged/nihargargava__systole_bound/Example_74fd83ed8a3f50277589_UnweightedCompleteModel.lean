module

public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Calculus.MeanValue

-- ==== Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.CircleMethod ====
public section
/-
Copyright (c) 2026.
Released under Apache 2.0 license.

The additive-character and interval-orthogonality proofs in this file are
adapted from Gershon Bialer's `ternary-goldbach-lean`,
`MathExtras.NumberTheory.Vinogradov.CircleMethod` (Apache-2.0).  The
arbitrary-arity cubic coefficient extraction is new to this project.
-/
@[expose] public section
open MeasureTheory
open scoped ArithmeticFunction BigOperators
namespace SystolicGrowth
/-! # Exact circle-method identities for `x^3 - x`

This file contains the algebraic and Fourier-analytic part of the
Cook--Magyar specialization.  There are no asymptotic estimates here: the
main result, `integral_cubicVonMangoldtExpSum_pow`, is the exact identity
which turns a Fourier integral into the von-Mangoldt-weighted number of
representations of a target by `n` values of `x^3-x`.
-/
/-- The cubic polynomial used throughout the arithmetic construction. -/
def primeCubic (x : ℕ) : ℕ := x ^ 3 - x
namespace CookMagyarCircle
/-- The additive character `e(kα) = exp(2πikα)`. -/
noncomputable def addChar (α : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (α : ℂ))

end CookMagyarCircle
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.Arcs ====
public section
/-
Copyright (c) 2026.
Released under Apache 2.0 license.

The elementary major/minor-arc decomposition in this file is adapted from
Gershon Bialer's `ternary-goldbach-lean`, in particular
`MathExtras.NumberTheory.Vinogradov.CircleMethod` and
`Math.Problems.TernaryGoldbach.CircleMethodDecomposition.Core`
(Apache-2.0).  The cubic scaling and arbitrary-power integrand are specific
to the Cook--Magyar specialization developed here.
-/
@[expose] public section
open MeasureTheory
namespace SystolicGrowth
namespace CookMagyarArcs
open CookMagyarCircle
/-! # Major and minor arcs for the cubic Cook--Magyar sum

For a cutoff `Q`, the major-arc centers are the reduced fractions `a / q`
with `0 <= a < q <= Q`.  At cubic scale `N`, each arc has radius
`Q / N^3`, as in the one-equation specialization of Cook--Magyar.  All arcs
are clipped to the fixed fundamental interval `[0, 1]`; the minor arcs are
the relative complement there.

This file only establishes the exact decomposition and its elementary
analytic prerequisites.  Estimates on the two pieces belong in subsequent
modules.
-/
noncomputable def rationalCenter (a q : ℕ) : ℝ :=
  (a : ℝ) / (q : ℝ)
end CookMagyarArcs
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.FiniteFourier ====
public section
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
@[expose] public section
open scoped BigOperators
namespace SystolicGrowth
namespace CookMagyarFiniteFourier
/-! # Finite Fourier expansion of the local cubic count

This file proves the exact finite-group identity underlying the local factors
in the Cook--Magyar circle method.  It contains no analytic estimate.
-/
variable {q : ℕ} [NeZero q]
/-- The reduction modulo `q` of the polynomial `X³ - X`. -/
def cubicResidue (x : ZMod q) : ZMod q := x ^ 3 - x
noncomputable abbrev standardAdditiveCharacter : AddChar (ZMod q) ℂ :=
  ZMod.stdAddChar
end CookMagyarFiniteFourier
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.CubicAbelPhase ====
public section
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
@[expose] public section
open Finset MeasureTheory
namespace SystolicGrowth
namespace CookMagyarMajorArc
open CookMagyarCircle
/-! # Smooth cubic phase for major-arc partial summation

The natural cubic here is `x^3 - x`, not `x^3 - 1`.  This real extension
agrees with the discrete character at every natural argument and has an
explicit derivative bound on the interval used by Abel summation.
-/
/-- The real phase occurring in the displaced cubic character. -/
noncomputable def cubicAbelRealPhase (beta t : ℝ) : ℝ :=
  2 * Real.pi * beta * (t ^ 3 - t)
/-- A smooth extension of `addChar beta (primeCubic k)`. -/
noncomputable def cubicAbelWeight (beta t : ℝ) : ℂ :=
  Complex.exp ((cubicAbelRealPhase beta t : ℂ) * Complex.I)

end CookMagyarMajorArc
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.UnweightedResidueAbel ====
public section
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
@[expose] public section
open Finset MeasureTheory
namespace SystolicGrowth
namespace CookMagyarMajorArc
open CookMagyarCircle
/-! # All-residue cubic Abel approximation

The elementary `1/q` density applies to every residue, not merely to
units. The resulting error bound is uniform in the residue and phase.
-/

/-- The uniform-density model for a single residue class. -/
noncomputable def cubicUnweightedResidueClassModel
    (q : ℕ) (beta : ℝ) (N : ℕ) : ℂ :=
  ((1 / (q : ℝ) : ℝ) : ℂ) *
    ∑ k ∈ Icc 0 N, addChar beta (primeCubic k)

end CookMagyarMajorArc
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.HuaShift ====
public section
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace SystolicGrowth
namespace CookMagyarCircle
/-! # Finite shift identities for the cubic eighth moment

The second-difference energy is proved in `HuaEstimate`. This module
connects that energy to the unweighted cubic exponential sum. -/
noncomputable def cubicUnweightedExpSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (N + 1), addChar α (primeCubic m)
end CookMagyarCircle
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Examples.Example_74fd83ed8a3f50277589_UnweightedCompleteModel ====
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
@[expose] public section
open Finset MeasureTheory
open scoped BigOperators
namespace SystolicGrowth
namespace CookMagyarMajorArc
open CookMagyarCircle CookMagyarArcs CookMagyarFiniteFourier
/-! # The all-residue complete cubic model -/
/-- The complete cubic sum includes *all* residues, not only units. -/
noncomputable def allResidueCubicExponentialSum
    (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ r : ZMod q, standardAdditiveCharacter (a * cubicResidue r)

/-- The ordinary cubic complete sum times the real integral with the
*inhomogeneous* phase `t³-t`. -/
noncomputable def cubicAllResidueIntegralModel
    (q : ℕ) [NeZero q] (a : ZMod q) (beta : ℝ) (N : ℕ) : ℂ :=
  allResidueCubicExponentialSum q a * ((1 / (q : ℝ) : ℝ) : ℂ) *
    ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t
set_option linter.unusedVariables false in
/-- The all-residue complete model with its real integral, before the
homogeneous-cubic replacement. -/
theorem norm_cubicUnweightedExpSum_sub_allResidueIntegralModel_le
    (q a N : ℕ) [NeZero q] (hq : 0 < q) (hN : 0 < N) (beta : ℝ) 
    (h_SystolicGrowth_CookMagyarMajorArc_norm_cubicUnweightedExpSum_sub_allResidueModel_le : ∀ (q a N : ℕ) [inst : NeZero q],
      0 < q →
        0 < N →
          ∀ (beta : ℝ),
            ‖SystolicGrowth.CookMagyarCircle.cubicUnweightedExpSum
                    (SystolicGrowth.CookMagyarArcs.rationalCenter a q + beta) N -
                  SystolicGrowth.CookMagyarMajorArc.allResidueCubicExponentialSum q (↑a : ZMod q) *
                    SystolicGrowth.CookMagyarMajorArc.cubicUnweightedResidueClassModel q beta N‖ ≤
              (↑q : ℝ) * (1 + (↑N : ℝ) * (2 * Real.pi * |beta| * (3 * (↑N : ℝ) ^ 2 + 1))))
    (h_SystolicGrowth_CookMagyarMajorArc_norm_sum_cubicAbelWeight_sub_integral_le : ∀ (beta : ℝ) (N : ℕ),
      ‖∑ k ∈ Finset.Icc 0 N, SystolicGrowth.CookMagyarMajorArc.cubicAbelWeight beta (↑k : ℝ) -
            ∫ (t : ℝ) in Set.Icc 0 (↑N : ℝ), SystolicGrowth.CookMagyarMajorArc.cubicAbelWeight beta t‖ ≤
        1 + (↑N : ℝ) * (2 * Real.pi * |beta| * (3 * (↑N : ℝ) ^ 2 + 1)))
    (h_SystolicGrowth_CookMagyarMajorArc_norm_allResidueCubicExponentialSum_le : ∀ (q : ℕ) [inst : NeZero q] (a : ZMod q),
      ‖SystolicGrowth.CookMagyarMajorArc.allResidueCubicExponentialSum q a‖ ≤ (↑q : ℝ))
    (h_SystolicGrowth_CookMagyarMajorArc_cubicAbelWeight_nat : ∀ (beta : ℝ) (k : ℕ),
      SystolicGrowth.CookMagyarMajorArc.cubicAbelWeight beta (↑k : ℝ) =
        SystolicGrowth.CookMagyarCircle.addChar beta (SystolicGrowth.primeCubic k))
    :
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        cubicAllResidueIntegralModel q (a : ZMod q) beta N‖ ≤
      ((q : ℝ) + 1) *
        (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
  let C : ℂ := allResidueCubicExponentialSum q (a : ZMod q)
  let E : ℝ := 1 + (N : ℝ) *
    (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))
  let S : ℂ := ∑ k ∈ Icc 0 N, addChar beta (primeCubic k)
  let V : ℂ := ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hC : ‖C‖ ≤ (q : ℝ) :=
    h_SystolicGrowth_CookMagyarMajorArc_norm_allResidueCubicExponentialSum_le q (a : ZMod q)
  have hcoef : ‖C * ((1 / (q : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (q : ℝ))]
    calc
      ‖C‖ * (1 / (q : ℝ)) ≤ (q : ℝ) * (1 / (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ = 1 := by field_simp
  have hSV : ‖S - V‖ ≤ E := by
    dsimp [S, V, E]
    simpa only [h_SystolicGrowth_CookMagyarMajorArc_cubicAbelWeight_nat] using
      h_SystolicGrowth_CookMagyarMajorArc_norm_sum_cubicAbelWeight_sub_integral_le beta N
  have hmodel :
      ‖C * cubicUnweightedResidueClassModel q beta N -
          cubicAllResidueIntegralModel q (a : ZMod q) beta N‖ ≤ E := by
    have heq :
        C * cubicUnweightedResidueClassModel q beta N -
            cubicAllResidueIntegralModel q (a : ZMod q) beta N =
          (C * ((1 / (q : ℝ) : ℝ) : ℂ)) * (S - V) := by
      dsimp [C, S, V, cubicUnweightedResidueClassModel,
        cubicAllResidueIntegralModel]
      ring
    rw [heq, norm_mul]
    simpa only [one_mul] using
      (mul_le_mul hcoef hSV (norm_nonneg _) (by norm_num))
  have hfinite :
      ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
          C * cubicUnweightedResidueClassModel q beta N‖ ≤ (q : ℝ) * E := by
    simpa only [C, E] using
      h_SystolicGrowth_CookMagyarMajorArc_norm_cubicUnweightedExpSum_sub_allResidueModel_le q a N hq hN beta
  calc
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        cubicAllResidueIntegralModel q (a : ZMod q) beta N‖ ≤
      ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
          C * cubicUnweightedResidueClassModel q beta N‖ +
        ‖C * cubicUnweightedResidueClassModel q beta N -
          cubicAllResidueIntegralModel q (a : ZMod q) beta N‖ := by
      calc
        ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
            cubicAllResidueIntegralModel q (a : ZMod q) beta N‖ =
          ‖(cubicUnweightedExpSum (rationalCenter a q + beta) N -
              C * cubicUnweightedResidueClassModel q beta N) +
            (C * cubicUnweightedResidueClassModel q beta N -
              cubicAllResidueIntegralModel q (a : ZMod q) beta N)‖ := by
            congr 1
            ring
        _ ≤ _ := norm_add_le _ _
    _ ≤ (q : ℝ) * E + E := add_le_add hfinite hmodel
    _ = ((q : ℝ) + 1) * E := by ring
end CookMagyarMajorArc
end SystolicGrowth
