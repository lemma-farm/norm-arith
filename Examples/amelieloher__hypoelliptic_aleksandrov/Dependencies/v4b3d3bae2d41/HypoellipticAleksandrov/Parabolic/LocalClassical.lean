module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.Operator
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
/-- A coefficient field is continuous at every point of a prescribed set. -/
def IsContinuousCoefficientOn {d : ℕ} (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ContinuousOn (coefficientAt A) U
/-- A coefficient field obeys a lower Loewner ellipticity bound on a set. -/
def HasLowerEllipticityOn {d : ℕ} (lam : ℝ) (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, lam • (1 : PDE.Mat d) ≤ coefficientAt A z
/-- A coefficient field obeys an upper Loewner ellipticity bound on a set. -/
def HasUpperEllipticityOn {d : ℕ} (Lam : ℝ) (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, coefficientAt A z ≤ Lam • (1 : PDE.Mat d)
/-- A scalar function is nonnegative at every point of a set. -/
def IsNonnegativeOn {d : ℕ} (q : TimeVelocity d → ℝ)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, 0 ≤ q z
/-- A scalar function is a pointwise supersolution of the forward equation on a set. -/
def IsParabolicSupersolutionOn {d : ℕ} (A : CoefficientField d)
    (f u : TimeVelocity d → ℝ) (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, f z ≤ parabolicOperator A u z
/-- A scalar function satisfies the homogeneous forward parabolic equation on a set. -/
def IsParabolicSolutionOn {d : ℕ} (A : CoefficientField d)
    (u : TimeVelocity d → ℝ) (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, parabolicOperator A u z = 0
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
/-- The transparent local nonnegative classical solution surface for the
Harnack leaf.  Its `ContDiffOn ℝ 2` assumption deliberately selects the
stronger smooth, isotropic local `C²` leaf relative to the source's
`C^{1,2}` class. -/
def IsLocalClassicalSolutionOn (d : ℕ) (B : CoefficientField d)
    (q : TimeVelocity d → ℝ) (U : Set (TimeVelocity d)) (lam Lam : ℝ) : Prop :=
  IsContinuousCoefficientOn B U ∧
    ContDiffOn ℝ 2 q U ∧
    IsNonnegativeOn q U ∧
    HasLowerEllipticityOn lam B U ∧
    HasUpperEllipticityOn Lam B U ∧
    IsParabolicSolutionOn B q U
namespace IsLocalClassicalSolutionOn
end IsLocalClassicalSolutionOn
end HypoellipticAleksandrov.Parabolic
