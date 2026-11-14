module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.LConvolution
public import Mathlib.Analysis.Convolution
public import Mathlib
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.Definitions.polynomialProduct ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.Definitions.coordinateDilation ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.Definitions.HomogeneousGroup ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.Definitions.HomogeneousGroup.mul ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.Definitions.HomogeneousGroup.inv ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.Definitions.HomogeneousGroup.dilate ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.G2.ConvolutionDefs ====
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
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ}
/-- A dedicated subtraction carrier for the group convolution.
Only subtraction and measurable structure are supplied; no commutative group
law is asserted (BB Convention 3.43, Def 3.44, pp. 118–119). -/
def ConvolutionCarrier (_G : HomogeneousGroup N) := Fin N → ℝ
instance convolutionCarrierSub (G : HomogeneousGroup N) : Sub (ConvolutionCarrier G) :=
  ⟨fun x y => G.mul x (G.inv y)⟩
instance convolutionCarrierMeasurableSpace (G : HomogeneousGroup N) :
    MeasurableSpace (ConvolutionCarrier G) := inferInstanceAs (MeasurableSpace (Fin N → ℝ))
instance convolutionCarrierMeasureSpace (G : HomogeneousGroup N) :
    MeasureSpace (ConvolutionCarrier G) := inferInstanceAs (MeasureSpace (Fin N → ℝ))
def groupConvolution {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)
    (f g : (Fin N → ℝ) → 𝕜) : (Fin N → ℝ) → 𝕜 :=
  MeasureTheory.convolution (G := ConvolutionCarrier G) g f (ContinuousLinearMap.mul ℝ 𝕜) volume

end RothschildStein.G2

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.Definitions.HomogeneousGroup.IsHomogeneousGauge ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.G2.Gauge ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v081e0f2b7a6c.RothschildStein.G2.MollifierDefs ====
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
open MeasureTheory
namespace RothschildStein.G2
variable {N : ℕ}
/-- The normalized compact smooth bump used in BB Prop 3.48,
p. 121. No symmetry or invariant differential regularity is imposed. -/
structure GroupMollifier (G : HomogeneousGroup N) (ν : HomogeneousNorm G) where
  toFun : (Fin N → ℝ) → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  compact : HasCompactSupport toFun
  nonneg : ∀ x, 0 ≤ toFun x
  integral_eq_one : (∫ x, toFun x) = 1
  vanish : ∀ x, 1 ≤ ν x → toFun x = 0
instance GroupMollifier.instCoeFun {G : HomogeneousGroup N} {ν : HomogeneousNorm G} :
    CoeFun (GroupMollifier G ν) (fun _ => (Fin N → ℝ) → ℝ) := ⟨GroupMollifier.toFun⟩
/-- The anisotropically scaled bump ε^{-Q} φ(D_{1/ε}x)
(BB Prop 3.48, p. 121). Its analytic properties require ε > 0. -/
def groupMollifierScale (G : HomogeneousGroup N) (φ : (Fin N → ℝ) → ℝ)
    (ε : ℝ) (x : Fin N → ℝ) : ℝ :=
  (ε ^ G.homogeneousDimension)⁻¹ * φ (G.dilate ε⁻¹ x)
/-- Left regularization by the scaled group bump (BB (3.30), p. 121). -/
def groupRegularize (G : HomogeneousGroup N) (φ f : (Fin N → ℝ) → ℝ)
    (ε : ℝ) : (Fin N → ℝ) → ℝ :=
  groupConvolution G (groupMollifierScale G φ ε) f
end RothschildStein.G2

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Examples.Example_4cccc2d1687efeaf899f_MollifierBound ====
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
open MeasureTheory Set
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}
set_option linter.unusedVariables false in
/-- A group mollifier preserves a global pointwise bound
(BB Prop 3.48 proof, p. 122). -/
theorem norm_groupRegularize_le (φ : GroupMollifier G ν) {f : (Fin N → ℝ) → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {ε : ℝ}
    (hε : 0 < ε) (x : Fin N → ℝ) 
    (h_RothschildStein_G2_groupRegularize_eq_integral : ∀ {N : ℕ} (G : RothschildStein.HomogeneousGroup N) (φ f : (Fin N → ℝ) → ℝ) {ε : ℝ},
      0 < ε →
        ∀ (x : Fin N → ℝ),
          RothschildStein.G2.groupRegularize G φ f ε x =
            ∫ (z : Fin N → ℝ), φ z * f (G.mul (G.inv (G.dilate ε z)) x))
    (h_RothschildStein_G2_continuous_dilate : ∀ {N : ℕ} (G : RothschildStein.HomogeneousGroup N) (t : ℝ), Continuous (G.dilate t))
    (h_RothschildStein_G2_continuous_inv : ∀ {N : ℕ} (G : RothschildStein.HomogeneousGroup N), Continuous G.inv)
    (h_RothschildStein_G2_continuous_mul : ∀ {N : ℕ} (G : RothschildStein.HomogeneousGroup N),
      Continuous fun (p : (Fin N → ℝ) × (Fin N → ℝ)) ↦ G.mul p.1 p.2)
    : ‖groupRegularize G φ f ε x‖ ≤ C := by
  have hφ : Integrable φ := φ.smooth.continuous.integrable_of_hasCompactSupport φ.compact
  have hmeas : AEStronglyMeasurable (fun z => φ z * f (G.mul (G.inv (G.dilate ε z)) x)) volume :=
    (φ.smooth.continuous.mul (hf.comp ((h_RothschildStein_G2_continuous_mul G).comp
      (((h_RothschildStein_G2_continuous_inv G).comp (h_RothschildStein_G2_continuous_dilate G ε)).prodMk continuous_const)))).aestronglyMeasurable
  have hb (z : Fin N → ℝ) :
      ‖φ z * f (G.mul (G.inv (G.dilate ε z)) x)‖ ≤ φ z * C := by
    rw [norm_mul, Real.norm_of_nonneg (φ.nonneg z)]
    exact mul_le_mul_of_nonneg_left (hC _) (φ.nonneg z)
  have hi : Integrable (fun z => φ z * f (G.mul (G.inv (G.dilate ε z)) x)) volume :=
    Integrable.mono' (hφ.mul_const C) hmeas (Filter.Eventually.of_forall fun z =>
      hb z)
  rw [h_RothschildStein_G2_groupRegularize_eq_integral G φ f hε]
  calc
    _ ≤ ∫ z, ‖φ z * f (G.mul (G.inv (G.dilate ε z)) x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, φ z * C := integral_mono hi.norm (hφ.mul_const C) hb
    _ = C := by rw [integral_mul_const, φ.integral_eq_one, one_mul]
end RothschildStein.G2
