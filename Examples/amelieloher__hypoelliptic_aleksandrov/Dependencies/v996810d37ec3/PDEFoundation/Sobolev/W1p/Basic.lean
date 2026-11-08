module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v996810d37ec3.PDEFoundation.Measure.RestrictedVolume
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v996810d37ec3.PDEFoundation.Sobolev.WeakDerivative
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Representative-level `W^{1,p}`

This compatibility carrier stores concrete value and gradient representatives.
The later Banach carrier is the closed weak-gradient graph modulo a.e.
equality; the two layers intentionally serve different purposes.
-/
@[expose] public section
open scoped ENNReal
namespace PDE
/-- Scalar `L^p` membership on a restricted domain. -/
abbrev MemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u p (volumeOn U)
/-- Coordinatewise gradient `L^p` membership, retained for exact LIH
compatibility. -/
def GradMemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemLpOn U p (fun x => Du x i)
/-- A concrete representative and a chosen coordinate weak gradient. -/
structure W1pFunction {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memLp : MemLpOn U p toFun
  gradMemLp : GradMemLpOn U p grad
  hasWeakGradient : HasWeakGradientOn U toFun grad
instance {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞} :
    CoeFun (W1pFunction U p) (fun _ => Vec d → ℝ) where
  coe u := u.toFun
theorem memLpOn_mono {d : ℕ}
    {U V : Set (Vec d)} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hVU : V ⊆ U) (hu : MemLpOn U p u) :
    MemLpOn V p u :=
  hu.mono_measure (MeasureTheory.Measure.restrict_mono_set
    MeasureTheory.volume hVU)
theorem gradMemLpOn_mono {d : ℕ}
    {U V : Set (Vec d)} {p : ℝ≥0∞} {Du : Vec d → Vec d}
    (hVU : V ⊆ U) (hDu : GradMemLpOn U p Du) :
    GradMemLpOn V p Du := by
  intro i
  exact memLpOn_mono hVU (hDu i)
namespace W1pFunction
@[ext]
theorem ext {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u v : W1pFunction U p}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) :
    u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl
def restrict {d : ℕ} {U V : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    W1pFunction V p where
  toFun := u.toFun
  grad := u.grad
  memLp := memLpOn_mono hVU u.memLp
  gradMemLp := gradMemLpOn_mono hVU u.gradMemLp
  hasWeakGradient := u.hasWeakGradient.restrict hVOpen hVU
end W1pFunction
end PDE
