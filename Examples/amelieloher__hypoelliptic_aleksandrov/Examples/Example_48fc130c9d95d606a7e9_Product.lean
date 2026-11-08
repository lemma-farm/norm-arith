module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v996810d37ec3.PDEFoundation.Sobolev.ClassicalGradient
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v996810d37ec3.PDEFoundation.Measure.NormalizedLp
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v996810d37ec3.PDEFoundation.Sobolev.W1p.Algebra
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v996810d37ec3.PDEFoundation.Sobolev.WeakDerivative.Product
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth multipliers on representative-level `W^{1,p}`

A smooth scalar multiplier preserves `W^{1,p}` when its value and coordinate
gradient are essentially bounded on the domain. The stored weak gradient is
the exact product-rule expression

`φ Du + u Dφ`.

The exponent hypothesis `1 ≤ p` is needed only to obtain the local
integrability required by the raw distributional product rule.
-/
@[expose] public section
open scoped ENNReal
namespace PDE
namespace W1pFunction
variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
/-- Multiply a representative-level Sobolev function by a smooth multiplier
whose value and first coordinate derivatives are essentially bounded on the
domain. -/
noncomputable def mulContDiffMemLpTop [Fact (1 ≤ p)]
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    W1pFunction U p where
  toFun := fun x => φ x * u x
  grad := fun x =>
    φ x • u.grad x + u x • classicalGradient φ x
  memLp := by
    simpa only [mul_comm] using u.memLp.fun_mul hφTop
  gradMemLp := by
    intro i
    have hfirst :
        MemLpOn U p (fun x => φ x * u.grad x i) := by
      simpa only [mul_comm] using
        (u.gradMemLp i).fun_mul hφTop
    have hsecond :
        MemLpOn U p
          (fun x => u x * classicalGradient φ x i) :=
      by
        simpa only [mul_comm] using
          u.memLp.fun_mul (hDφTop i)
    exact hfirst.add hsecond
  hasWeakGradient := by
    convert u.hasWeakGradient.mul_contDiff hφ
      u.locallyIntegrable_toFun u.locallyIntegrable_grad using 1
    funext x i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      classicalGradient_apply]
theorem eLpNormOn_mulContDiffMemLpTop_grad_coord_le
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i))
    (i : Fin d) :
    eLpNormOn U p
        (fun x =>
          (u.mulContDiffMemLpTop hφ hφTop hDφTop).grad x i) ≤
      eLpNormOn U ∞ φ *
          eLpNormOn U p (fun x => u.grad x i) +
        eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun := by
  let first : Vec d → ℝ :=
    fun x => φ x * u.grad x i
  let second : Vec d → ℝ :=
    fun x => u x * classicalGradient φ x i
  have hfirstMem : MemLpOn U p first := by
    simpa only [first, mul_comm] using
      (u.gradMemLp i).fun_mul hφTop
  have hsecondMem : MemLpOn U p second := by
    simpa only [second, mul_comm] using
      u.memLp.fun_mul (hDφTop i)
  have hfirstBound :
      eLpNormOn U p first ≤
        eLpNormOn U ∞ φ *
          eLpNormOn U p (fun x => u.grad x i) := by
    exact
      MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
        (f := fun x => u.grad x i) p hφTop.aestronglyMeasurable
  have hsecondBound :
      eLpNormOn U p second ≤
        eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun := by
    calc
      eLpNormOn U p second =
          eLpNormOn U p
            (fun x => classicalGradient φ x i * u x) := by
        apply MeasureTheory.eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [second, mul_comm]
      _ ≤ eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun := by
        exact
          MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
            (f := u.toFun) p (hDφTop i).aestronglyMeasurable
  calc
    eLpNormOn U p
        (fun x =>
          (u.mulContDiffMemLpTop hφ hφTop hDφTop).grad x i) =
        eLpNormOn U p (first + second) := by
      rfl
    _ ≤ eLpNormOn U p first + eLpNormOn U p second := by
      exact MeasureTheory.eLpNorm_add_le Fact.out
    _ ≤ eLpNormOn U ∞ φ *
          eLpNormOn U p (fun x => u.grad x i) +
        eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun :=
      add_le_add hfirstBound hsecondBound
end W1pFunction
end PDE
