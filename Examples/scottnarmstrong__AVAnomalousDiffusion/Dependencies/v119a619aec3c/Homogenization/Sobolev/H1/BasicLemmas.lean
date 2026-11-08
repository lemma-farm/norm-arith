-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.Homogenization.Geometry.ConvexDomain
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.Homogenization.Geometry.TriadicPartition
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.Homogenization.Multiscale.NormalizedNorms
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.Homogenization.Sobolev.H1.Definitions
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.Homogenization.Sobolev.L2Ambient
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
open scoped ENNReal
theorem memL2On_mono {d : ℕ} {U V : Set (Vec d)} {u : Vec d → ℝ}
    (hVU : V ⊆ U) (hu : MemL2On U u) : MemL2On V u :=
  hu.mono_measure (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hVU)
theorem gradMemL2On_mono {d : ℕ} {U V : Set (Vec d)} {Du : Vec d → Vec d}
    (hVU : V ⊆ U) (hDu : GradMemL2On U Du) : GradMemL2On V Du := by
  intro i
  exact memL2On_mono hVU (hDu i)
theorem HasWeakPartialDerivOn.restrict {d : ℕ} {U V : Set (Vec d)}
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn V i u gi := by
  let _ := hVopen
  intro φ hφ_smooth hφ_compact hφ_supp
  have hφ_suppU : tsupport φ ⊆ U := hφ_supp.trans hVU
  have key := h φ hφ_smooth hφ_compact hφ_suppU
  have h1 : ∀ x, x ∉ V → u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_supp hx')
    have hφ_eq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
    simp
  have h2 : ∀ x, x ∉ V → gi x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hφ_supp hx'))]
  have h3 : ∀ x, x ∉ U → u x * (fderiv ℝ φ x) (basisVec i) = 0 :=
    fun x hx => h1 x (fun hx' => hx (hVU hx'))
  have h4 : ∀ x, x ∉ U → gi x * φ x = 0 :=
    fun x hx => h2 x (fun hx' => hx (hVU hx'))
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h1,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h2,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h3,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h4,
    key]
theorem HasWeakGradientOn.restrict {d : ℕ} {U V : Set (Vec d)}
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn V u Du := by
  intro i
  exact (h i).restrict hVopen hVU
namespace H1Function
@[ext] theorem ext {d : ℕ} {U : Set (Vec d)} {u v : H1Function U}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) : u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl
def restrict {d : ℕ} {U V : Set (Vec d)} (u : H1Function U)
    (hVopen : IsOpen V) (hVU : V ⊆ U) : H1Function V :=
  { toFun := u.toFun
    grad := u.grad
    memL2 := memL2On_mono hVU u.memL2
    gradMemL2 := gradMemL2On_mono hVU u.gradMemL2
    hasWeakGradient := u.hasWeakGradient.restrict hVopen hVU }
end H1Function
namespace H10Function
end H10Function
end Homogenization
