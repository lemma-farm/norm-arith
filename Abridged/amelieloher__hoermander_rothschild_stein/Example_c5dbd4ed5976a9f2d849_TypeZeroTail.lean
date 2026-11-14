module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.Algebra.Support
public import Mathlib
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.LConvolution
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.polynomialProduct ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def polynomialProduct {N : ℕ}
    (P : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℝ)
    (x y : Fin N → ℝ) : Fin N → ℝ :=
  fun j => MvPolynomial.eval (Sum.elim x y) (P j)
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.coordinateDilation ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def coordinateDilation {N : ℕ} (w : Fin N → ℕ)
    (t : ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun j => t ^ w j * x j
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.HomogeneousGroup ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
structure HomogeneousGroup (N : ℕ) where
  dimension_pos : 0 < N
  weight : Fin N → ℕ
  weight_pos : ∀ j, 0 < weight j
  weight_mono : Monotone weight
  productPolynomial : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℝ
  inversePolynomial : Fin N → MvPolynomial (Fin N) ℝ
  zero_left : ∀ x, polynomialProduct productPolynomial 0 x = x
  zero_right : ∀ x, polynomialProduct productPolynomial x 0 = x
  assoc : ∀ x y z,
    polynomialProduct productPolynomial (polynomialProduct productPolynomial x y) z =
      polynomialProduct productPolynomial x (polynomialProduct productPolynomial y z)
  inverse_left : ∀ x,
    polynomialProduct productPolynomial
      (fun j => MvPolynomial.eval x (inversePolynomial j)) x = 0
  inverse_right : ∀ x,
    polynomialProduct productPolynomial x
      (fun j => MvPolynomial.eval x (inversePolynomial j)) = 0
  dilation_product : ∀ t : ℝ, 0 < t → ∀ x y,
    coordinateDilation weight t (polynomialProduct productPolynomial x y) =
      polynomialProduct productPolynomial
        (coordinateDilation weight t x) (coordinateDilation weight t y)
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.HomogeneousGroup.dilate ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def HomogeneousGroup.dilate {N : ℕ} (G : HomogeneousGroup N)
    (t : ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  coordinateDilation G.weight t x
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.HomogeneousGroup.IsHomogeneousGauge ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def HomogeneousGroup.IsHomogeneousGauge {N : ℕ} (G : HomogeneousGroup N)
    (ν : (Fin N → ℝ) → ℝ) : Prop :=
  Continuous ν ∧ (∀ x, 0 ≤ ν x) ∧
    (∀ x, ν x = 0 ↔ x = 0) ∧
    (∀ t : ℝ, 0 < t → ∀ x, ν (G.dilate t x) = t * ν x)
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.HomogeneousGroup.mul ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def HomogeneousGroup.mul {N : ℕ} (G : HomogeneousGroup N)
    (x y : Fin N → ℝ) : Fin N → ℝ :=
  polynomialProduct G.productPolynomial x y
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.HomogeneousGroup.inv ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def HomogeneousGroup.inv {N : ℕ} (G : HomogeneousGroup N)
    (x : Fin N → ℝ) : Fin N → ℝ :=
  fun j => MvPolynomial.eval x (G.inversePolynomial j)
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.G2.Gauge ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G2
/-- Homogeneous norm, with one constant for inversion and multiplication
(BB Definition 3.8, pp. 98–99). The analytic gauge axioms use the predicate. -/
structure HomogeneousNorm {N : ℕ} (G : HomogeneousGroup N) where
  toFun : (Fin N → ℝ) → ℝ
  gauge : G.IsHomogeneousGauge toFun
  c : ℝ
  one_le_c : 1 ≤ c
  inv_le : ∀ x, toFun (G.inv x) ≤ c * toFun x
  mul_le : ∀ x y, toFun (G.mul x y) ≤ c * (toFun x + toFun y)
instance HomogeneousNorm.instCoeFun {N : ℕ} {G : HomogeneousGroup N} :
    CoeFun (HomogeneousNorm G) (fun _ => (Fin N → ℝ) → ℝ) := ⟨HomogeneousNorm.toFun⟩
variable {N : ℕ} {G : HomogeneousGroup N}

end RothschildStein.G2

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def HomogeneousGroup.homogeneousDimension {N : ℕ} (G : HomogeneousGroup N) : ℕ :=
  ∑ j, G.weight j
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.H3.TypeZero ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)
/-- The fixed-gauge mean is taken over the closed unit-to-e shell
(BB Prop 6.26, p. 274). -/
def kernelMean (ν f : (Fin N → ℝ) → ℝ) : ℝ :=
  ∫ x in {x | 1 ≤ ν x ∧ ν x ≤ Real.exp 1}, f x
/-- The function version of the type-zero class in Chapter 8:
smoothness off the origin, degree minus Q, and zero fixed-gauge mean
(BB Def. 8.21 and Remark 8.23, p. 354). -/
structure TypeZero (ν f : (Fin N → ℝ) → ℝ) : Prop where
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) f {0}ᶜ
  homogeneous : ∀ (t : ℝ), 0 < t → ∀ x : Fin N → ℝ, x ≠ 0 →
    f (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * f x
  mean_zero : kernelMean ν f = 0
end RothschildStein.H3

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.H3.Truncation ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open RothschildStein.G2
/-- The fixed radial cutoff (BB Lemma 8.24, pp. 354–356). -/
def radialCutoff (t : ℝ) : ℝ := min 1 (max 0 (2 - t))

end RothschildStein.H3

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.H3.KernelSphereBound ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}
/-- The order-zero kernel seminorm is the actual unit-sphere maximum
Λ_{T,0} (BB Definition 8.13 and (8.7), p. 346). -/
def kernelSphereBound (ν T : (Fin N → ℝ) → ℝ) : ℝ :=
  sSup ((fun x => |T x|) '' {x | ν x = 1})
end RothschildStein.H3

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Examples.Example_c5dbd4ed5976a9f2d849_TypeZeroTail ====
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Set
open scoped ENNReal
variable {N : ℕ} {G : HomogeneousGroup N}
/-- The finite annular tail in the unit-ball principal-value decomposition. -/
def typeZeroUnitTail (ν k : (Fin N → ℝ) → ℝ) : (Fin N → ℝ) → ℝ :=
  {x | 1 ≤ ν x ∧ ν x ≤ 2}.indicator (fun x => (1 - radialCutoff (ν x)) * k x)
set_option linter.unusedVariables false in
/-- The annular tail is bounded by the actual unit-sphere kernel seminorm. -/
theorem TypeZero.unitTail_norm_le {ν : G2.HomogeneousNorm G}
    {k : (Fin N → ℝ) → ℝ} (hk : TypeZero G ν k) (x : Fin N → ℝ) 
    (h_RothschildStein_H3_kernelSphereBound_continuous : ∀ {N : ℕ} {G : RothschildStein.HomogeneousGroup N} {ν T : (Fin N → ℝ) → ℝ},
      G.IsHomogeneousGauge ν →
        ContinuousOn T {0}ᶜ →
          0 ≤ RothschildStein.H3.kernelSphereBound ν T ∧
            (∃ (z : Fin N → ℝ), ν z = 1 ∧ |T z| = RothschildStein.H3.kernelSphereBound ν T) ∧
              ∀ (z : Fin N → ℝ), ν z = 1 → |T z| ≤ RothschildStein.H3.kernelSphereBound ν T)
    (h_RothschildStein_H3_radialCutoff_bounds : ∀ (t : ℝ), 0 ≤ RothschildStein.H3.radialCutoff t ∧ RothschildStein.H3.radialCutoff t ≤ 1)
    (h_RothschildStein_H3_kernelSphereBound_homogeneous : ∀ {N : ℕ} {G : RothschildStein.HomogeneousGroup N} {ν T : (Fin N → ℝ) → ℝ},
      G.IsHomogeneousGauge ν →
        ∀ {γ : ℝ},
          ContinuousOn T {0}ᶜ →
            (∀ (t : ℝ), 0 < t → ∀ (x : Fin N → ℝ), x ≠ 0 → T (G.dilate t x) = t ^ γ * T x) →
              ∀ (x : Fin N → ℝ), x ≠ 0 → |T x| ≤ RothschildStein.H3.kernelSphereBound ν T * ν x ^ γ)
    :
    ‖typeZeroUnitTail ν k x‖ ≤ kernelSphereBound ν k := by
  have hΛ := (h_RothschildStein_H3_kernelSphereBound_continuous ν.gauge hk.smooth.continuousOn).1
  by_cases hx : x ∈ {y | 1 ≤ ν y ∧ ν y ≤ 2}
  · rw [typeZeroUnitTail, indicator_of_mem hx, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (h_RothschildStein_H3_radialCutoff_bounds (ν x)).2), Real.norm_eq_abs]
    have hx0 : x ≠ 0 := by
      intro he
      subst x
      have hz := (ν.gauge.2.2.1 0).mpr rfl
      change 1 ≤ ν 0 ∧ ν 0 ≤ 2 at hx
      linarith
    have hb := h_RothschildStein_H3_kernelSphereBound_homogeneous ν.gauge hk.smooth.continuousOn
      hk.homogeneous x hx0
    have hp : (ν x) ^ (-(G.homogeneousDimension : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx.1 (neg_nonpos.mpr (Nat.cast_nonneg _))
    have hbk : |k x| ≤ kernelSphereBound ν k := by
      apply hb.trans
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hΛ
    calc
      (1 - radialCutoff (ν x)) * |k x| ≤ 1 * |k x| :=
        mul_le_mul_of_nonneg_right (by linarith [(h_RothschildStein_H3_radialCutoff_bounds (ν x)).1]) (abs_nonneg _)
      _ ≤ kernelSphereBound ν k := by simpa only [one_mul] using hbk
  · rw [typeZeroUnitTail, indicator_of_notMem hx, norm_zero]
    exact hΛ
end RothschildStein.H3
