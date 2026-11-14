import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.List.Sort
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Rat.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

-- ==== Examples.realazthat__zeta5_lean2.Examples.Example_4da7764ce1be9585f9fb_InnerRealKernel ====
noncomputable section
namespace Zeta5RealKernel
def overlap (u v : ℝ) : ℝ :=
  if Int.fract u<1/2 then
    if Int.fract v<1/2 then min (Int.fract u) (Int.fract v)
    else max 0 (Int.fract u+Int.fract v-1)
  else
    if Int.fract v<1/2 then max 0 (Int.fract u+Int.fract v-1)
    else min (Int.fract u) (Int.fract v)-1/2
def highLength (u : ℝ) : ℝ := Int.fract (2*u)/2
def BB (x : ℝ) : ℝ := highLength (3/40*x)-2*(highLength (3/40*x))^2
def AB (x : ℝ) : ℝ := overlap (3/40*x) x-2*highLength (3/40*x)*highLength x
def gamma (x : ℝ) : ℝ :=
  let T : ℝ := ⌊23/10*x⌋
  let a : ℝ := ⌊3/20*x⌋
  let b : ℝ := ⌊2*x⌋
  (T^2-T*b-5*T-9*a^2+3*a*b+15*a)/2 +
  highLength x*(-T+3*a)+highLength (3/40*x)*(-18*a+3*b+6)+
  3*overlap (3/40*x) x+(23/10*x-T)/2*(2*T-b-5)+
  max ((23/10*x-T)/2-highLength x) 0
def scalar (x : ℝ) : ℝ :=
  let m : ℝ := ⌊37/20*x⌋
  2*(37/40*x)*(⌊x⌋:ℝ)-12*(37/40*x)*(⌊3/40*x⌋:ℝ)-
    2*(m*(37/40*x)-m*(m+1)/4)
def kernel (x : ℝ) : ℝ := -gamma x-scalar x
def linearPart (x : ℝ) : ℝ :=
  4*(37/40)+2*(37/40)*Int.fract x-12*(37/40)*Int.fract (3/40*x)
def remainder (x : ℝ) : ℝ :=
  let τ := Int.fract (23/10*x)
  let σ := Int.fract (2*x)
  let η := Int.fract (37/20*x)
  (τ*(τ-σ)-max (τ-σ) 0+η*(1-η))/2+9*BB x-3*AB x

open  MeasureTheory Set


set_option linter.unusedVariables false in
theorem kernel_integrableOn (a b : ℝ) 
    (h_Zeta5RealKernel_kernel_decomposition : ∀ (x : ℝ), Zeta5RealKernel.kernel x = x * Zeta5RealKernel.linearPart x + Zeta5RealKernel.remainder x)
    (h_Zeta5RealKernel_linearPart_bounds : ∀ (x : ℝ), -(37 / 5) ≤ Zeta5RealKernel.linearPart x ∧ Zeta5RealKernel.linearPart x ≤ 111 / 20)
    (h_Zeta5RealKernel_measurable_kernel : Measurable Zeta5RealKernel.kernel)
    (h_Zeta5RealKernel_remainder_bounds : ∀ (x : ℝ), -(1 / 2) ≤ Zeta5RealKernel.remainder x ∧ Zeta5RealKernel.remainder x ≤ 13 / 8)
    : IntegrableOn kernel (Icc a b) := by
  apply Measure.integrableOn_of_bounded (M:=8*(|a|+|b|)+2) (measure_Icc_lt_top.ne)
    h_Zeta5RealKernel_measurable_kernel.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hx0 : |x|≤|a|+|b| := by
    apply abs_le.mpr
    constructor
    · have:=neg_abs_le a; have:=abs_nonneg b; linarith [hx.1]
    · have:=le_abs_self b; have:=abs_nonneg a; linarith [hx.2]
  rw [Real.norm_eq_abs,h_Zeta5RealKernel_kernel_decomposition]
  have hf : |linearPart x|≤8 := by
    apply abs_le.mpr
    constructor <;> linarith [(h_Zeta5RealKernel_linearPart_bounds x).1,(h_Zeta5RealKernel_linearPart_bounds x).2]
  have hr : |remainder x|≤2 := by
    apply abs_le.mpr
    constructor <;> linarith [(h_Zeta5RealKernel_remainder_bounds x).1,(h_Zeta5RealKernel_remainder_bounds x).2]
  calc
    |x*linearPart x+remainder x|≤|x*linearPart x|+|remainder x| := abs_add_le _ _
    _ ≤ (|a|+|b|)*8+2 := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul hx0 hf (abs_nonneg _) (by positivity)) hr
    _ = _ := by ring

end Zeta5RealKernel
