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

-- ==== Examples.nihargargava__systole_bound.Dependencies.v55588d36833b.CookMagyar.CircleMethod ====
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

-- ==== Examples.nihargargava__systole_bound.Dependencies.v55588d36833b.CookMagyar.Arcs ====
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

-- ==== Examples.nihargargava__systole_bound.Dependencies.v55588d36833b.CookMagyar.FiniteFourier ====
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

-- ==== Examples.nihargargava__systole_bound.Dependencies.v55588d36833b.CookMagyar.UnweightedResidueAbel ====
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

/-- The unweighted cubic sum over one residue class. -/
noncomputable def cubicUnweightedResidueClassSum
    (q r : ℕ) (beta : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ Icc 0 N,
    if k ≡ r [MOD q] then addChar beta (primeCubic k) else 0
/-- The uniform-density model for a single residue class. -/
noncomputable def cubicUnweightedResidueClassModel
    (q : ℕ) (beta : ℝ) (N : ℕ) : ℂ :=
  ((1 / (q : ℝ) : ℝ) : ℂ) *
    ∑ k ∈ Icc 0 N, addChar beta (primeCubic k)

end CookMagyarMajorArc
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Dependencies.v55588d36833b.CookMagyar.HuaShift ====
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

-- ==== Examples.nihargargava__systole_bound.Examples.Example_6eee332daea832274cc4_UnweightedCompleteModel ====
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


set_option linter.unusedVariables false in
/-- Elementary unweighted major-arc model, before replacing the finite
real cubic phase sum by its homogeneous integral. -/
theorem norm_cubicUnweightedExpSum_sub_allResidueModel_le
    (q a N : ℕ) [NeZero q] (hq : 0 < q) (hN : 0 < N) (beta : ℝ) 
    (h_SystolicGrowth_CookMagyarMajorArc_norm_cubicUnweightedResidueClassSum_sub_model_le : ∀ (q r : ℕ),
      0 < q →
        ∀ (beta : ℝ) (N : ℕ),
          0 < N →
            ‖SystolicGrowth.CookMagyarMajorArc.cubicUnweightedResidueClassSum q r beta N -
                  SystolicGrowth.CookMagyarMajorArc.cubicUnweightedResidueClassModel q beta N‖ ≤
              1 + (↑N : ℝ) * (2 * Real.pi * |beta| * (3 * (↑N : ℝ) ^ 2 + 1)))
    (h_SystolicGrowth_CookMagyarMajorArc_cubicUnweightedExpSum_rationalCenter_add : ∀ (q a N : ℕ) [inst : NeZero q],
      0 < q →
        ∀ (beta : ℝ),
          SystolicGrowth.CookMagyarCircle.cubicUnweightedExpSum
              (SystolicGrowth.CookMagyarArcs.rationalCenter a q + beta) N =
            ∑ r : ZMod q,
              (SystolicGrowth.CookMagyarFiniteFourier.standardAdditiveCharacter : ZMod q → ℂ)
                  ((↑a : ZMod q) * SystolicGrowth.CookMagyarFiniteFourier.cubicResidue r) *
                SystolicGrowth.CookMagyarMajorArc.cubicUnweightedResidueClassSum q r.val beta N)
    (h_SystolicGrowth_CookMagyarMajorArc_sum_allResidueCubicModels_eq_complete : ∀ (q a N : ℕ) [inst : NeZero q],
      0 < q →
        ∀ (beta : ℝ),
          ∑ r : ZMod q,
              (SystolicGrowth.CookMagyarFiniteFourier.standardAdditiveCharacter : ZMod q → ℂ)
                  ((↑a : ZMod q) * SystolicGrowth.CookMagyarFiniteFourier.cubicResidue r) *
                SystolicGrowth.CookMagyarMajorArc.cubicUnweightedResidueClassModel q beta N =
            SystolicGrowth.CookMagyarMajorArc.allResidueCubicExponentialSum q (↑a : ZMod q) *
              SystolicGrowth.CookMagyarMajorArc.cubicUnweightedResidueClassModel q beta N)
    :
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        allResidueCubicExponentialSum q (a : ZMod q) *
          cubicUnweightedResidueClassModel q beta N‖ ≤
      (q : ℝ) *
        (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
  classical
  rw [h_SystolicGrowth_CookMagyarMajorArc_cubicUnweightedExpSum_rationalCenter_add q a N hq beta,
    ← h_SystolicGrowth_CookMagyarMajorArc_sum_allResidueCubicModels_eq_complete q a N hq beta,
    ← Finset.sum_sub_distrib]
  have hnorm (r : ZMod q) :
      ‖standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassSum q r.val beta N -
        standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassModel q beta N‖ ≤
        1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)) := by
    rw [← mul_sub, norm_mul, AddChar.norm_apply, one_mul]
    exact h_SystolicGrowth_CookMagyarMajorArc_norm_cubicUnweightedResidueClassSum_sub_model_le
      q r.val hq beta N hN
  calc
    ‖∑ r : ZMod q,
      (standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassSum q r.val beta N -
        standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassModel q beta N)‖ ≤
        ∑ r : ZMod q,
          ‖standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
              cubicUnweightedResidueClassSum q r.val beta N -
            standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
              cubicUnweightedResidueClassModel q beta N‖ := norm_sum_le _ _
    _ ≤ ∑ _r : ZMod q,
          (1 + (N : ℝ) *
            (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
      exact Finset.sum_le_sum (fun r _ => hnorm r)
    _ = (q : ℝ) *
          (1 + (N : ℝ) *
            (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
      simp
      ring
end CookMagyarMajorArc
end SystolicGrowth
