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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.polynomialProduct ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.coordinateDilation ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.HomogeneousGroup ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.HomogeneousGroup.dilate ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.HomogeneousGroup.IsHomogeneousGauge ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.HomogeneousGroup.mul ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.HomogeneousGroup.inv ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.G2.Gauge ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.H3.TypeZero ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.H3.Truncation ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.H3.KernelSphereBound ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Examples.Example_0d4bbbaef5cb916fb76b_TypeZeroTail ====
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
axiom _root_.RothschildStein.H3.TypeZero.unitTail_norm_le : ∀ {N : ℕ} {G : RothschildStein.HomogeneousGroup N} {ν : RothschildStein.G2.HomogeneousNorm G}
  {k : (Fin N → ℝ) → ℝ},
  RothschildStein.H3.TypeZero G ν.toFun k →
    ∀ (x : Fin N → ℝ),
      ‖RothschildStein.H3.typeZeroUnitTail ν.toFun k x‖ ≤
        RothschildStein.H3.kernelSphereBound ν.toFun k
set_option linter.unusedVariables false in
/-- The annular tail is integrable; its L1 bound is linear in the kernel seminorm. -/
theorem TypeZero.unitTail_integrable_and_bound {ν : G2.HomogeneousNorm G}
    {k : (Fin N → ℝ) → ℝ} (hk : TypeZero G ν k) 
    (h_RothschildStein_G2_isCompact_gauge_le : ∀ {N : ℕ} {G : RothschildStein.HomogeneousGroup N} {ν : (Fin N → ℝ) → ℝ},
      G.IsHomogeneousGauge ν → ∀ (r : ℝ), IsCompact {x : Fin N → ℝ | ν x ≤ r})
    (h_RothschildStein_H3_kernelSphereBound_continuous : ∀ {N : ℕ} {G : RothschildStein.HomogeneousGroup N} {ν T : (Fin N → ℝ) → ℝ},
      G.IsHomogeneousGauge ν →
        ContinuousOn T {0}ᶜ →
          0 ≤ RothschildStein.H3.kernelSphereBound ν T ∧
            (∃ (z : Fin N → ℝ), ν z = 1 ∧ |T z| = RothschildStein.H3.kernelSphereBound ν T) ∧
              ∀ (z : Fin N → ℝ), ν z = 1 → |T z| ≤ RothschildStein.H3.kernelSphereBound ν T)
    (h_RothschildStein_H3_radialCutoff_lipschitz : LipschitzWith 1 RothschildStein.H3.radialCutoff)
    :
    Integrable (typeZeroUnitTail ν k) volume ∧
    eLpNorm (typeZeroUnitTail ν k) 1 volume ≤ ENNReal.ofReal (kernelSphereBound ν k) *
      volume {x | 1 ≤ ν x ∧ ν x ≤ 2} := by
  let A : Set (Fin N → ℝ) := {x | 1 ≤ ν x ∧ ν x ≤ 2}
  have hAc : IsCompact A := (h_RothschildStein_G2_isCompact_gauge_le ν.gauge 2).of_isClosed_subset
    ((isClosed_le continuous_const ν.gauge.1).inter (isClosed_le ν.gauge.1 continuous_const))
    (fun _ hx => hx.2)
  have hA : MeasurableSet A := hAc.isClosed.measurableSet
  have hkA : ContinuousOn k A := hk.smooth.continuousOn.mono (by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro he
    subst x
    have hz := (ν.gauge.2.2.1 0).mpr rfl
    change 1 ≤ ν 0 ∧ ν 0 ≤ 2 at hx
    linarith)
  have hc : ContinuousOn (fun x => (1 - radialCutoff (ν x)) * k x) A :=
    (continuous_const.sub (h_RothschildStein_H3_radialCutoff_lipschitz.continuous.comp ν.gauge.1)).continuousOn.mul hkA
  have hi : Integrable (typeZeroUnitTail ν k) volume :=
    (integrable_indicator_iff hA).mpr (ContinuousOn.integrableOn_compact hAc hc)
  refine ⟨hi, ?_⟩
  have hΛ := (h_RothschildStein_H3_kernelSphereBound_continuous ν.gauge hk.smooth.continuousOn).1
  have hb : eLpNorm (typeZeroUnitTail ν k) 1 volume ≤
      eLpNorm (A.indicator (fun _ => kernelSphereBound ν k)) 1 volume := by
    apply eLpNorm_mono hi.aestronglyMeasurable
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, Real.norm_of_nonneg hΛ]
      exact hk.unitTail_norm_le x
    · rw [typeZeroUnitTail, indicator_of_notMem hx, indicator_of_notMem hx]
  apply hb.trans_eq
  rw [eLpNorm_indicator_const hA.nullMeasurableSet (by norm_num) (by norm_num)]
  simp only [Real.enorm_eq_ofReal hΛ, ENNReal.toReal_one, one_div_one, ENNReal.rpow_one]
  rfl
end RothschildStein.H3
