module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Set.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Tactic.FinCases
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FunProp
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Real

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.PDEFoundation.Ambient.Basic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Ambient carriers

The common finite-dimensional carriers used by the PDE libraries. The
inherited norm on `Vec d` is the finite-product supremum norm; Euclidean
quadratic structure is defined explicitly in `PDEFoundation.Ambient.EuclideanNorm`.
-/
@[expose] public section
namespace PDE
/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.PDEFoundation.Ambient.EuclideanNorm ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Explicit Euclidean norm on native vectors

`PDE.Vec d = Fin d → ℝ` inherits the finite-product supremum norm. This
module supplies the distinct Euclidean dot product, squared norm, and norm
needed by energy estimates.
-/
@[expose] public section
open scoped BigOperators
namespace PDE
/-- The Euclidean dot product on native project vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i
/-- The square of the Euclidean norm on native project vectors. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.PDEFoundation.Geometry.EuclideanBall.Basic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Round balls on native vectors

Round balls are defined through the explicit Euclidean squared distance, not
the inherited finite-product metric. The squared-radius convention agrees
with the established homogenization API. Consequently, norm-membership and
radius-monotonicity lemmas state the required radius sign assumptions.
-/
@[expose] public section
open scoped Pointwise
namespace PDE
/-- Euclidean squared distance on native vectors. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)
/-- The explicit round Euclidean open ball. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}
end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.Geometry ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Parabolic time--velocity geometry

This module fixes the explicit Euclidean time--velocity cylinders and their
forward parabolic boundary. The terminal open-ball face is deliberately not a
boundary component.
-/
@[expose] public section
namespace HypoellipticAleksandrov.Parabolic
/-- Time--velocity points in dimension `d`. -/
abbrev TimeVelocity (d : ℕ) := ℝ × PDE.Vec d
/-- The analytic interior `(0, T) × B₁(y₀)` of a parabolic cylinder. -/
def parabolicInterior {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) : Set (TimeVelocity d) :=
  Set.Ioo 0 T ×ˢ PDE.euclideanBall y₀ 1

end HypoellipticAleksandrov.Parabolic

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Measure.TimeVelocity ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Measures and norms on time--velocity space

This module records the product Lebesgue normalization on time--velocity
space, identifies cylinders differing only by their terminal time slice, and
defines the exact `L^(d + 1)` norms used by the parabolic ABP estimate.
-/
@[expose] public section
open Filter MeasureTheory Set
open scoped ENNReal
namespace HypoellipticAleksandrov.Parabolic
noncomputable section

def parabolicExponent (d : ℕ) : ℝ≥0∞ := d + 1
def parabolicELpNormOn (d : ℕ) (f : TimeVelocity d → ℝ)
    (s : Set (TimeVelocity d)) : ℝ≥0∞ :=
  eLpNorm f (parabolicExponent d) (volume.restrict s)
/-- The `ENNReal.toReal` encoding of the extended-real `L^(d + 1)` norm restricted to a
time--velocity set. It agrees with the usual finite real `L^(d + 1)` norm whenever
`parabolicELpNormOn d f s ≠ ∞`, in particular under
`MemLp f (parabolicExponent d) (volume.restrict s)`. -/
def parabolicLpNormOn (d : ℕ) (f : TimeVelocity d → ℝ)
    (s : Set (TimeVelocity d)) : ℝ :=
  (parabolicELpNormOn d f s).toReal
end
end HypoellipticAleksandrov.Parabolic

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.LocalClassical ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Local classical parabolic predicates

This module gives the transparent local classical surfaces used by the
parabolic Harnack development.  The predicates below contain only pointwise
regularity, ellipticity, sign, and equation data; they contain no comparison
or estimate.  The `ContDiffOn ℝ 2` surface is the deliberately stronger
smooth, isotropic local `C²` classical leaf relative to the source's
`C^{1,2}` class.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder

/-- A scalar function is nonnegative at every point of a set. -/
def IsNonnegativeOn {d : ℕ} (q : TimeVelocity d → ℝ)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, 0 ≤ q z

namespace IsContinuousCoefficientOn

end IsContinuousCoefficientOn
namespace HasLowerEllipticityOn

end HasLowerEllipticityOn
namespace HasUpperEllipticityOn

end HasUpperEllipticityOn
namespace IsNonnegativeOn

end IsNonnegativeOn
namespace IsParabolicSupersolutionOn

end IsParabolicSupersolutionOn
namespace IsParabolicSolutionOn

end IsParabolicSolutionOn
namespace IsParabolicSolutionOn
end IsParabolicSolutionOn

namespace IsLocalClassicalSolutionOn

end IsLocalClassicalSolutionOn
end HypoellipticAleksandrov.Parabolic

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.HarnackGeometry ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coordinate geometry for the parabolic Harnack argument

The Krylov--Safonov boxes in this file use coordinate cubes.  In particular,
they are not the metric balls inherited by `PDE.Vec d`.
-/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace HypoellipticAleksandrov.Parabolic
noncomputable section
/-- The open coordinate cube of radius `r` about `v₀`. -/
def velocityCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) : Set (PDE.Vec d) :=
  {v | ∀ i : Fin d, |v i - v₀ i| < r}
/-- The closed coordinate cube of radius `r` about `v₀`. -/
def velocityClosedCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) : Set (PDE.Vec d) :=
  {v | ∀ i : Fin d, |v i - v₀ i| ≤ r}
/-- The forward parabolic coordinate box of height `vartheta * r^2`. -/
def parabolicBox {d : ℕ} (vartheta r t₀ : ℝ) (v₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Ioo t₀ (t₀ + vartheta * r ^ 2) ×ˢ velocityCube v₀ r
def parabolicAffine {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) :
    TimeVelocity d → TimeVelocity d :=
  fun z => (t₀ + r ^ 2 * z.1, v₀ + r • z.2)

end
end HypoellipticAleksandrov.Parabolic

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.HarnackABP ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The local ABP bridge for the parabolic Harnack argument

This file proves the translated, radius-one-half ABP consequence used in
Krylov--Safonov Lemma 3.2.  It turns local classical data on the inner
cylinder into the globally regular data required by the unit ABP
estimate, removes the zeroth-order term by exponential conjugation, and then
uses the exact parabolic restricted-norm scaling formula.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Filter MeasureTheory Set
open scoped MatrixOrder Topology
/-- The affine map from the unit cylinder to the local ABP cylinder centered
at `v0`. -/
def localABPAffine {d : ℕ} (v0 : PDE.Vec d) : TimeVelocity d → TimeVelocity d :=
  parabolicAffine (3 / 4) v0 (1 / 2)
/-- The open inner cylinder `(3/4, 1) × B_(1/2)(v0)`, presented as the affine
image of the reference parabolic interior. -/
def localABPInterior {d : ℕ} (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  localABPAffine v0 '' parabolicInterior 1 0
end HypoellipticAleksandrov.Parabolic

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_1cabd4c4f13be36a50a8_DensityNearOneMeasure ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Measure bookkeeping for the near-one density argument

This module proves the finite-support parabolic norm bound and the exact
strict-sublevel complement identity used by the near-one density-to-point
argument.  It has no coefficient, ABP, or density-to-point conclusion.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Filter MeasureTheory Set
open scoped ENNReal Topology


set_option linter.unusedVariables false in
/-- The local weighted positive source is controlled by the strict low-set
volume, with no coefficient or ABP premise. -/
theorem parabolicLpNormOn_localABP_weighted_one_sub_le
    (d : Nat) (rho : Real) (hrho : 0 ≤ rho)
    (U : Set (TimeVelocity d)) (u : TimeVelocity d → Real)
    (hQU : parabolicBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hu : ContDiffOn Real 2 u U)
    (hu_nonneg : IsNonnegativeOn u (parabolicBox 1 1 0 (0 : PDE.Vec d)))
    (v0 : PDE.Vec d) (hv0 : v0 ∈ velocityClosedCube 0 (1 / 2 : Real)) 
    (h_HypoellipticAleksandrov_Parabolic_weightedSource_nonneg : ∀ {d : ℕ} (rho : ℝ) (u : HypoellipticAleksandrov.Parabolic.TimeVelocity d → ℝ)
      (z : HypoellipticAleksandrov.Parabolic.TimeVelocity d),
      0 ≤ rho → 0 ≤ Real.exp (rho * (z.1 - 3 / 4)) * (rho * Max.max (1 - u z) 0))
    (h_HypoellipticAleksandrov_Parabolic_volume_parabolicBox_one_ne_top : ∀ (d : ℕ),
      (MeasureTheory.MeasureSpace.volume :
            Set (HypoellipticAleksandrov.Parabolic.TimeVelocity d) → ENNReal)
          (HypoellipticAleksandrov.Parabolic.parabolicBox 1 1 0 0) ≠
        ⊤)
    (h_HypoellipticAleksandrov_Parabolic_localABPInterior_subset_parabolicBox_one : ∀ {d : ℕ} {v₀ : PDE.Vec d},
      v₀ ∈ HypoellipticAleksandrov.Parabolic.velocityClosedCube 0 (1 / 2) →
        HypoellipticAleksandrov.Parabolic.localABPInterior v₀ ⊆
          HypoellipticAleksandrov.Parabolic.parabolicBox 1 1 0 0)
    (h_HypoellipticAleksandrov_Parabolic_parabolicLpNormOn_le_of_norm_le_indicator : ∀ (d : ℕ) (f : HypoellipticAleksandrov.Parabolic.TimeVelocity d → ℝ)
      (s E : Set (HypoellipticAleksandrov.Parabolic.TimeVelocity d)) (M : ℝ),
      MeasureTheory.AEStronglyMeasurable f (MeasureTheory.MeasureSpace.volume.restrict s) →
        MeasurableSet s →
          MeasurableSet E →
            0 ≤ M →
              (MeasureTheory.MeasureSpace.volume :
                      Set (HypoellipticAleksandrov.Parabolic.TimeVelocity d) → ENNReal)
                    (s ∩ E) ≠
                  ⊤ →
                (∀ z ∈ s,
                    ‖f z‖ ≤
                      E.indicator (fun (x : HypoellipticAleksandrov.Parabolic.TimeVelocity d) ↦ M) z) →
                  HypoellipticAleksandrov.Parabolic.parabolicLpNormOn d f s ≤
                    M *
                      ((MeasureTheory.MeasureSpace.volume :
                                Set (HypoellipticAleksandrov.Parabolic.TimeVelocity d) → ENNReal)
                              (s ∩ E)).toReal.rpow
                        (1 / ((↑d : ℝ) + 1)))
    (h_HypoellipticAleksandrov_Parabolic_measurableSet_localABPInterior : ∀ {d : ℕ} (v0 : PDE.Vec d), MeasurableSet (HypoellipticAleksandrov.Parabolic.localABPInterior v0))
    (h_HypoellipticAleksandrov_Parabolic_measurableSet_parabolicBox_inter_lt_one_of_contDiffOn : ∀ (d : ℕ) (U : Set (HypoellipticAleksandrov.Parabolic.TimeVelocity d))
      (u : HypoellipticAleksandrov.Parabolic.TimeVelocity d → ℝ),
      HypoellipticAleksandrov.Parabolic.parabolicBox 1 1 0 0 ⊆ U →
        ContDiffOn ℝ 2 u U →
          MeasurableSet
            (HypoellipticAleksandrov.Parabolic.parabolicBox 1 1 0 0 ∩
              {z : HypoellipticAleksandrov.Parabolic.TimeVelocity d | u z < 1}))
    (h_HypoellipticAleksandrov_Parabolic_mem_parabolicInterior_iff : ∀ {d : ℕ} {T t : ℝ} {y₀ v : PDE.Vec d},
      (t, v) ∈ HypoellipticAleksandrov.Parabolic.parabolicInterior T y₀ ↔
        0 < t ∧ t < T ∧ v ∈ PDE.euclideanBall y₀ 1)
    :
    parabolicLpNormOn d
        (fun z ↦ Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0))
        (localABPInterior v0) ≤
      rho * Real.exp (rho / 4) *
        Real.rpow (volume (parabolicBox 1 1 0 (0 : PDE.Vec d) ∩ {z | u z < 1})).toReal
          (1 / ((d : Real) + 1)) := by
  let Q : Set (TimeVelocity d) := parabolicBox 1 1 0 0
  let E : Set (TimeVelocity d) := Q ∩ {z | u z < 1}
  let f : TimeVelocity d → Real := fun z ↦
    Real.exp (rho * (z.1 - 3 / 4)) * (rho * max (1 - u z) 0)
  have hM : 0 ≤ rho * Real.exp (rho / 4) := mul_nonneg hrho (Real.exp_pos _).le
  have hE : MeasurableSet E := by
    exact h_HypoellipticAleksandrov_Parabolic_measurableSet_parabolicBox_inter_lt_one_of_contDiffOn d U u hQU hu
  have hfinite : volume (localABPInterior v0 ∩ E) ≠ ∞ := by
    apply measure_ne_top_of_subset (show localABPInterior v0 ∩ E ⊆ Q by
      intro z hz
      exact hz.2.1)
    exact h_HypoellipticAleksandrov_Parabolic_volume_parabolicBox_one_ne_top d
  have hEfinite : volume E ≠ ∞ := by
    apply measure_ne_top_of_subset (show E ⊆ Q by
      intro z hz
      exact hz.1)
    exact h_HypoellipticAleksandrov_Parabolic_volume_parabolicBox_one_ne_top d
  have hbound : ∀ z ∈ localABPInterior v0, ‖f z‖ ≤
      E.indicator (fun _ : TimeVelocity d ↦ rho * Real.exp (rho / 4)) z := by
    rintro z ⟨w, hw, rfl⟩
    have hzQ : localABPAffine v0 w ∈ Q :=
      h_HypoellipticAleksandrov_Parabolic_localABPInterior_subset_parabolicBox_one hv0 ⟨w, hw, rfl⟩
    by_cases hlow : u (localABPAffine v0 w) < 1
    · have hzE : localABPAffine v0 w ∈ E := ⟨hzQ, hlow⟩
      rw [Set.indicator_of_mem hzE]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (h_HypoellipticAleksandrov_Parabolic_weightedSource_nonneg rho u (localABPAffine v0 w) hrho)]
      have hmax : max (1 - u (localABPAffine v0 w)) 0 ≤ 1 := by
        apply max_le
        · linarith [hu_nonneg (localABPAffine v0 w) hzQ]
        · norm_num
      rcases h_HypoellipticAleksandrov_Parabolic_mem_parabolicInterior_iff.mp hw with ⟨hw0, hw1, hwv⟩
      have htimeMul : rho * w.1 ≤ rho * 1 :=
        mul_le_mul_of_nonneg_left hw1.le hrho
      have htime : rho * ((localABPAffine v0 w).1 - 3 / 4) ≤ rho / 4 := by
        dsimp only [localABPAffine, parabolicAffine]
        nlinarith [htimeMul]
      have hexp := Real.exp_le_exp.mpr htime
      calc
        Real.exp (rho * ((localABPAffine v0 w).1 - 3 / 4)) *
            (rho * max (1 - u (localABPAffine v0 w)) 0) ≤
            Real.exp (rho * ((localABPAffine v0 w).1 - 3 / 4)) * (rho * 1) := by
          gcongr
        _ ≤ Real.exp (rho / 4) * (rho * 1) := by
          gcongr
        _ = rho * Real.exp (rho / 4) := by ring
    · rw [Set.indicator_of_notMem]
      · have hfzero : f (localABPAffine v0 w) = 0 := by
          dsimp only [f]
          rw [max_eq_right]
          · ring
          · exact sub_nonpos.mpr (le_of_not_gt hlow)
        rw [hfzero, norm_zero]
      · rintro ⟨_, hzlow⟩
        exact hlow hzlow
  have hnorm := h_HypoellipticAleksandrov_Parabolic_parabolicLpNormOn_le_of_norm_le_indicator d f
    (localABPInterior v0) E (rho * Real.exp (rho / 4))
    (show AEStronglyMeasurable f (volume.restrict (localABPInterior v0)) from
      (show ContinuousOn f (localABPInterior v0) from
        (by fun_prop : Continuous (fun z : TimeVelocity d =>
          Real.exp (rho * (z.1 - 3 / 4)))).continuousOn.mul
          (continuousOn_const.mul
            ((continuousOn_const.sub (hu.continuousOn.mono
              ((h_HypoellipticAleksandrov_Parabolic_localABPInterior_subset_parabolicBox_one hv0).trans hQU))).sup
                continuousOn_const))).aestronglyMeasurable
                  (h_HypoellipticAleksandrov_Parabolic_measurableSet_localABPInterior v0))
    (h_HypoellipticAleksandrov_Parabolic_measurableSet_localABPInterior v0) hE hM hfinite hbound
  change parabolicLpNormOn d f (localABPInterior v0) ≤ _
  calc
    parabolicLpNormOn d f (localABPInterior v0) ≤
        rho * Real.exp (rho / 4) *
          Real.rpow (volume (localABPInterior v0 ∩ E)).toReal
            (1 / ((d : Real) + 1)) := hnorm
    _ ≤ rho * Real.exp (rho / 4) *
          Real.rpow (volume E).toReal (1 / ((d : Real) + 1)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.rpow_le_rpow ENNReal.toReal_nonneg
        · exact ENNReal.toReal_mono hEfinite
            (measure_mono (inter_subset_right : localABPInterior v0 ∩ E ⊆ E))
        · positivity
      · exact hM
    _ = _ := rfl
end HypoellipticAleksandrov.Parabolic
