/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.FourierBilinearCauchySchwarz
public import Mathlib
set_option autoImplicit false
/-! # Genuine spatial Fourier factorization and angular Fubini -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Filter
open scoped RealInnerProductSpace
namespace FalconerThetaGauge
def maskedFourierPairKernel (b₁ b₂ : Plane → UnitCircle → ℝ) (r : ℝ)
    (w : UnitCircle) (p : Plane × Plane) : ℂ :=
  Complex.exp (-((r * inner ℝ (p.1 - p.2) (w : Plane) : ℝ) : ℂ) * Complex.I) *
    (b₁ p.1 w : ℂ) * (b₂ p.2 w : ℂ)
@[fun_prop]
theorem measurable_maskedFourierPairKernel {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂)) (r : ℝ) :
    Measurable (uncurry (maskedFourierPairKernel b₁ b₂ r)) := by
  have harg₁ : Measurable (fun p : UnitCircle × (Plane × Plane) ↦ (p.2.1, p.1)) :=
    (measurable_fst.comp measurable_snd).prodMk measurable_fst
  have harg₂ : Measurable (fun p : UnitCircle × (Plane × Plane) ↦ (p.2.2, p.1)) :=
    (measurable_snd.comp measurable_snd).prodMk measurable_fst
  exact ((by fun_prop : Measurable (fun p : UnitCircle × (Plane × Plane) ↦
    Complex.exp (-((r * inner ℝ (p.2.1 - p.2.2) (p.1 : Plane) : ℝ) : ℂ) *
      Complex.I))).mul (hb₁.comp harg₁).complex_ofReal).mul (hb₂.comp harg₂).complex_ofReal
theorem norm_maskedFourierPairKernel (b₁ b₂ : Plane → UnitCircle → ℝ)
    (r : ℝ) (w : UnitCircle) (p : Plane × Plane) :
    ‖maskedFourierPairKernel b₁ b₂ r w p‖ = |b₁ p.1 w| * |b₂ p.2 w| := by
  rw [maskedFourierPairKernel, norm_mul, norm_mul, Complex.norm_exp]
  simp
end FalconerThetaGauge
