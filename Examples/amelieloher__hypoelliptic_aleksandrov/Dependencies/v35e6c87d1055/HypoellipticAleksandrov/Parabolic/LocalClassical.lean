module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.Operator
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
theorem mono {d : ℕ} {A : CoefficientField d} {U V : Set (TimeVelocity d)}
    (h : IsContinuousCoefficientOn A U) (hVU : V ⊆ U) :
    IsContinuousCoefficientOn A V :=
  ContinuousOn.mono h hVU
end IsContinuousCoefficientOn
namespace HasLowerEllipticityOn
/-- A local lower ellipticity bound can be evaluated at each point of its set. -/
theorem le {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    {U : Set (TimeVelocity d)} (h : HasLowerEllipticityOn lam A U)
    {z : TimeVelocity d} (hz : z ∈ U) :
    lam • (1 : PDE.Mat d) ≤ coefficientAt A z :=
  h z hz
/-- A lower ellipticity bound restricts to a smaller set. -/
theorem mono {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    {U V : Set (TimeVelocity d)} (h : HasLowerEllipticityOn lam A U)
    (hVU : V ⊆ U) : HasLowerEllipticityOn lam A V :=
  fun z hz => h z (hVU hz)
end HasLowerEllipticityOn
namespace HasUpperEllipticityOn
/-- A local upper ellipticity bound can be evaluated at each point of its set. -/
theorem le {d : ℕ} {Lam : ℝ} {A : CoefficientField d}
    {U : Set (TimeVelocity d)} (h : HasUpperEllipticityOn Lam A U)
    {z : TimeVelocity d} (hz : z ∈ U) :
    coefficientAt A z ≤ Lam • (1 : PDE.Mat d) :=
  h z hz
/-- An upper ellipticity bound restricts to a smaller set. -/
theorem mono {d : ℕ} {Lam : ℝ} {A : CoefficientField d}
    {U V : Set (TimeVelocity d)} (h : HasUpperEllipticityOn Lam A U)
    (hVU : V ⊆ U) : HasUpperEllipticityOn Lam A V :=
  fun z hz => h z (hVU hz)
end HasUpperEllipticityOn
namespace IsNonnegativeOn
theorem mono {d : ℕ} {q : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} (h : IsNonnegativeOn q U)
    (hVU : V ⊆ U) : IsNonnegativeOn q V :=
  fun z hz => h z (hVU hz)
end IsNonnegativeOn
namespace IsParabolicSupersolutionOn
/-- A local supersolution inequality can be evaluated at each point of its set. -/
theorem le {d : ℕ} {A : CoefficientField d} {f u : TimeVelocity d → ℝ}
    {U : Set (TimeVelocity d)} (h : IsParabolicSupersolutionOn A f u U)
    {z : TimeVelocity d} (hz : z ∈ U) : f z ≤ parabolicOperator A u z :=
  h z hz
/-- A supersolution inequality restricts to a smaller set. -/
theorem mono {d : ℕ} {A : CoefficientField d} {f u : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} (h : IsParabolicSupersolutionOn A f u U)
    (hVU : V ⊆ U) : IsParabolicSupersolutionOn A f u V :=
  fun z hz => h z (hVU hz)
end IsParabolicSupersolutionOn
namespace IsParabolicSolutionOn
theorem mono {d : ℕ} {A : CoefficientField d} {u : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} (h : IsParabolicSolutionOn A u U)
    (hVU : V ⊆ U) : IsParabolicSolutionOn A u V :=
  fun z hz => h z (hVU hz)
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
/-- A local classical solution has continuous coefficients on its domain. -/
theorem continuousCoefficientOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) :
    IsContinuousCoefficientOn B U :=
  h.1
/-- A local classical solution is `C²` on its domain. -/
theorem contDiffOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) : ContDiffOn ℝ 2 q U :=
  h.2.1
/-- A local classical solution is nonnegative on its domain. -/
theorem nonnegativeOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) : IsNonnegativeOn q U :=
  h.2.2.1
/-- A local classical solution obeys its lower ellipticity bound on its domain. -/
theorem lowerEllipticityOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) : HasLowerEllipticityOn lam B U :=
  h.2.2.2.1
/-- A local classical solution obeys its upper ellipticity bound on its domain. -/
theorem upperEllipticityOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) : HasUpperEllipticityOn Lam B U :=
  h.2.2.2.2.1
/-- A local classical solution satisfies the homogeneous equation on its domain. -/
theorem solutionOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) : IsParabolicSolutionOn B q U :=
  h.2.2.2.2.2
theorem mono {d : ℕ} {B : CoefficientField d} {q : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) (hVU : V ⊆ U) :
    IsLocalClassicalSolutionOn d B q V lam Lam :=
  ⟨h.continuousCoefficientOn.mono hVU, h.contDiffOn.mono hVU,
    h.nonnegativeOn.mono hVU, h.lowerEllipticityOn.mono hVU,
    h.upperEllipticityOn.mono hVU, h.solutionOn.mono hVU⟩
end IsLocalClassicalSolutionOn
end HypoellipticAleksandrov.Parabolic
