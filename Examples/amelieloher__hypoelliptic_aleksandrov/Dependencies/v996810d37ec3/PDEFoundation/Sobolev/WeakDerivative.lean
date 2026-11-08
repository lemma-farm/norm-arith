module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v996810d37ec3.PDEFoundation.Ambient.Basis
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v996810d37ec3.PDEFoundation.Measure.RestrictedVolume
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Weak first derivatives on native vector domains

The raw integration-by-parts predicates remain compatible with LIH. A bundled
test-function facade packages smoothness, compact support, and support
containment for later PDE proofs.
-/
@[expose] public section
namespace PDE
/-- A smooth compactly supported test function whose topological support lies
inside `U`. -/
structure WeakTestFunction {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  contDiff : ContDiff ℝ (⊤ : ℕ∞) toFun
  hasCompactSupport : HasCompactSupport toFun
  tsupport_subset : tsupport toFun ⊆ U
instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (WeakTestFunction U) (fun _ => Vec d → ℝ) where
  coe φ := φ.toFun
def HasWeakPartialDerivOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume
/-- `Du` is a coordinate weak gradient of `u` on `U`. -/
def HasWeakGradientOn {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)
namespace HasWeakPartialDerivOn
end HasWeakPartialDerivOn
theorem HasWeakPartialDerivOn.restrict {d : ℕ}
    {U V : Set (Vec d)} (_hVOpen : IsOpen V) (hVU : V ⊆ U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn V i u gi := by
  intro φ hφSmooth hφCompact hφSupport
  have hφSupportU : tsupport φ ⊆ U := hφSupport.trans hVU
  have hWeak := h φ hφSmooth hφCompact hφSupportU
  have hValueZero :
      ∀ x, x ∉ V → u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx
    have hxNotIn : x ∉ tsupport φ := fun hx' => hx (hφSupport hx')
    have hφEq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hxNotIn |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφEq]
    simp
  have hGradZero :
      ∀ x, x ∉ V → gi x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport
      (fun hx' => hx (hφSupport hx'))]
  have hValueZeroU :
      ∀ x, x ∉ U → u x * (fderiv ℝ φ x) (basisVec i) = 0 :=
    fun x hx => hValueZero x (fun hx' => hx (hVU hx'))
  have hGradZeroU :
      ∀ x, x ∉ U → gi x * φ x = 0 :=
    fun x hx => hGradZero x (fun hx' => hx (hVU hx'))
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        hValueZero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hGradZero,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        hValueZeroU,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        hGradZeroU,
    hWeak]
theorem HasWeakGradientOn.restrict {d : ℕ}
    {U V : Set (Vec d)} (hVOpen : IsOpen V) (hVU : V ⊆ U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn V u Du := by
  intro i
  exact (h i).restrict hVOpen hVU
end PDE
