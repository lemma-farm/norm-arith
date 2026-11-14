module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Measure

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vc368d6714a92.PDEFoundation.Ambient.Basic ====
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

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vc368d6714a92.PDEFoundation.Ambient.EuclideanNorm ====
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
/-- The Euclidean norm on native project vectors. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vc368d6714a92.PDEFoundation.Ambient.Basis ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coordinate basis of the native ambient space

The coordinate basis and its exact dot-product and Euclidean-length formulas.
-/
@[expose] public section
namespace PDE
/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vc368d6714a92.PDEFoundation.Sobolev.ClassicalGradient ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Classical gradients in the native ambient space

The inherited norm on `PDE.Vec d` is the finite-product supremum norm. This
file packages the coordinate gradient of a classically differentiable scalar
function as a native vector and relates directional derivatives to the
explicit Euclidean dot product. Quantitative PDE estimates should use the
resulting Euclidean Cauchy--Schwarz inequality, not the operator norm induced
by the inherited product norm.
-/
@[expose] public section
namespace PDE
/-- The coordinate gradient of a scalar function, expressed in the native
vector carrier. -/
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_36b2e4c1814607d6427a_SpatialDifferenceQuotientSmoothL2 ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Global `L²` control of smooth spatial difference quotients

This file proves the constant-one whole-space estimate needed before local
cutoffs are introduced.
-/
@[expose] public section
open MeasureTheory
private axiom integrable_sq_classicalGradient
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcompact : HasCompactSupport φ) :
    Integrable (fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2)
      (volume : Measure (PDE.Vec d))
private axiom spatialDifferenceQuotient_sq_le_segmentIntegral
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0) (y : PDE.Vec d) :
    ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2 ≤
      ∫ t in (0 : ℝ)..1,
        PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • (h • PDE.basisVec k))) ^ 2
private axiom integrable_sq_spatialDifferenceQuotient
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcompact : HasCompactSupport φ)
    (k : Fin d) (h : ℝ) :
    Integrable (fun y => ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2)
      (volume : Measure (PDE.Vec d))
private axiom integrable_translate_segmentAverage
    {d : ℕ} (g : PDE.Vec d → ℝ)
    (hg : Integrable g (volume : Measure (PDE.Vec d))) (z : PDE.Vec d) :
    Integrable (fun y => ∫ t in (0 : ℝ)..1, g (y + t • z))
      (volume : Measure (PDE.Vec d))
private axiom integral_translate_segmentAverage
    {d : ℕ} (g : PDE.Vec d → ℝ)
    (hg : Integrable g (volume : Measure (PDE.Vec d))) (z : PDE.Vec d) :
    (∫ y, ∫ t in (0 : ℝ)..1, g (y + t • z)) = ∫ y, g y
/-- A signed coordinate difference quotient of a smooth compactly supported
function is controlled in global `L²` by its Euclidean classical gradient.
The quotient is totalized at `h = 0`. -/
theorem integral_sq_spatialDifferenceQuotient_le_integral_sq_classicalGradient
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcompact : HasCompactSupport φ)
    (k : Fin d) (h : ℝ) :
    (∫ y, ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2
      ∂(volume : Measure (PDE.Vec d))) ≤
      ∫ y, PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2
        ∂(volume : Measure (PDE.Vec d)) := by
  by_cases hh : h = 0
  · simp only [hh, zero_smul, add_zero, sub_self, zero_div]
    simp only [pow_two, zero_mul, integral_zero]
    apply integral_nonneg
    intro y
    simpa only [Pi.zero_apply, pow_two] using
      sq_nonneg (PDE.vecEuclideanNorm (PDE.classicalGradient φ y))
  let g : PDE.Vec d → ℝ :=
    fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2
  have hg : Integrable g (volume : Measure (PDE.Vec d)) :=
    integrable_sq_classicalGradient φ hφ hφcompact
  have hq : Integrable (fun y => ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2)
      (volume : Measure (PDE.Vec d)) :=
    integrable_sq_spatialDifferenceQuotient φ hφ hφcompact k h
  have hr : Integrable (fun y => ∫ t in (0 : ℝ)..1,
      g (y + t • (h • PDE.basisVec k))) (volume : Measure (PDE.Vec d)) :=
    integrable_translate_segmentAverage g hg _
  have hpoint : ∀ y : PDE.Vec d,
      ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2 ≤
        ∫ t in (0 : ℝ)..1, g (y + t • (h • PDE.basisVec k)) := by
    intro y
    exact spatialDifferenceQuotient_sq_le_segmentIntegral φ hφ k h hh y
  calc
    (∫ y, ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2) ≤
        ∫ y, ∫ t in (0 : ℝ)..1, g (y + t • (h • PDE.basisVec k)) :=
      integral_mono_ae hq hr (Filter.Eventually.of_forall hpoint)
    _ = ∫ y, g y := integral_translate_segmentAverage g hg _
    _ = ∫ y, PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2 := rfl
