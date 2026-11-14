import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.Monotone

-- ==== Examples.Arthur742Ramos__myerson_satterthwaite_lean.Dependencies.v6b17d6b54e3e.MS.Defs ====
section
open MeasureTheory
noncomputable def interimQ (q : ℝ × ℝ → ℝ) (nu : Measure ℝ) (v : ℝ) : ℝ :=
  ∫ c, q (v, c) ∂nu
noncomputable def interimR (q : ℝ × ℝ → ℝ) (mu : Measure ℝ) (c : ℝ) : ℝ :=
  ∫ v, q (v, c) ∂mu
noncomputable def interimU (q tb : ℝ × ℝ → ℝ) (nu : Measure ℝ) (v : ℝ) : ℝ :=
  ∫ c, (v * q (v, c) - tb (v, c)) ∂nu
noncomputable def interimW (q tc : ℝ × ℝ → ℝ) (mu : Measure ℝ) (c : ℝ) : ℝ :=
  ∫ v, (tc (v, c) - c * q (v, c)) ∂mu
/-- The data and hypotheses for a continuous bilateral-trade instance. -/
structure MSData where
  a1 : ℝ
  b1 : ℝ
  a2 : ℝ
  b2 : ℝ
  h1 : a1 < b1
  h2 : a2 < b2
  h3 : a2 < b1
  h4 : a1 < b2
  mu : Measure ℝ
  nu : Measure ℝ
  mu_probability : IsProbabilityMeasure mu
  nu_probability : IsProbabilityMeasure nu
  mu_noAtoms : MeasureTheory.NullSingletonClass mu
  nu_noAtoms : MeasureTheory.NullSingletonClass nu
  mu_supported : Measure.support mu ⊆ Set.Icc a1 b1
  nu_supported : Measure.support nu ⊆ Set.Icc a2 b2
  vol_absB : Measure.AbsolutelyContinuous (volume.restrict (Set.Icc a1 b1)) mu
  vol_absS : Measure.AbsolutelyContinuous (volume.restrict (Set.Icc a2 b2)) nu
  mu_fullSupport : ∀ s : Set ℝ, IsOpen s → (s ∩ Set.Ioo a1 b1).Nonempty → 0 < mu s
  nu_fullSupport : ∀ s : Set ℝ, IsOpen s → (s ∩ Set.Ioo a2 b2).Nonempty → 0 < nu s
  q : ℝ × ℝ → ℝ
  q_measurable : AEStronglyMeasurable q (mu.prod nu)
  q_sectionB : ∀ v ∈ Set.Icc a1 b1, AEStronglyMeasurable (fun c => q (v, c)) nu
  q_sectionS : ∀ c ∈ Set.Icc a2 b2, AEStronglyMeasurable (fun v => q (v, c)) mu
  q_nonneg : ∀ v ∈ Set.Icc a1 b1, ∀ c ∈ Set.Icc a2 b2, 0 ≤ q (v, c)
  q_le_one : ∀ v ∈ Set.Icc a1 b1, ∀ c ∈ Set.Icc a2 b2, q (v, c) ≤ 1
  tb : ℝ × ℝ → ℝ
  tc : ℝ × ℝ → ℝ
  tb_integrable : Integrable tb (mu.prod nu)
  tc_integrable : Integrable tc (mu.prod nu)
  tb_section : ∀ v ∈ Set.Icc a1 b1, Integrable (fun c => tb (v, c)) nu
  tc_section : ∀ c ∈ Set.Icc a2 b2, Integrable (fun v => tc (v, c)) mu
  effB : q =ᵐ[(mu.prod nu).restrict {p | p.2 < p.1}] (fun _ => (1 : ℝ))
  effS : q =ᵐ[(mu.prod nu).restrict {p | p.1 < p.2}] (fun _ => (0 : ℝ))
  bicB : ∀ v ∈ Set.Icc a1 b1, ∀ v' ∈ Set.Icc a1 b1,
    interimU q tb nu v ≥ interimU q tb nu v' + (v - v') * interimQ q nu v'
  bicS : ∀ c ∈ Set.Icc a2 b2, ∀ c' ∈ Set.Icc a2 b2,
    interimW q tc mu c ≥ interimW q tc mu c' + (c' - c) * interimR q mu c'
  irB : ∀ v ∈ Set.Icc a1 b1, 0 ≤ interimU q tb nu v
  irS : ∀ c ∈ Set.Icc a2 b2, 0 ≤ interimW q tc mu c
  bb : (∫ p, tc p ∂(mu.prod nu)) ≤ (∫ p, tb p ∂(mu.prod nu))
namespace MSData
/-- The buyer's interim trade probability at value `v`. -/
noncomputable def Q (D : MSData) (v : ℝ) : ℝ := interimQ D.q D.nu v

/-- The buyer's interim utility at value `v`. -/
noncomputable def U (D : MSData) (v : ℝ) : ℝ := interimU D.q D.tb D.nu v

set_option linter.unusedVariables false in
axiom _root_.MSData.bicB' : ∀ (D : MSData),
  ∀ v ∈ Set.Icc D.a1 D.b1, ∀ v' ∈ Set.Icc D.a1 D.b1, D.U v ≥ D.U v' + (v - v') * D.Q v'

end MSData

end

-- ==== Examples.Arthur742Ramos__myerson_satterthwaite_lean.Examples.Example_781c324fac56dfd005ac_Envelope ====
set_option linter.style.haveILetI false
open MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace MSData
set_option linter.unusedVariables false in
axiom _root_.MSData.Q_nonneg : ∀ (D : MSData), ∀ v ∈ Set.Icc D.a1 D.b1, 0 ≤ D.Q v
set_option linter.unusedVariables false in
axiom _root_.MSData.Q_le_one : ∀ (D : MSData), ∀ v ∈ Set.Icc D.a1 D.b1, D.Q v ≤ 1
theorem U_lip (D : MSData) (v : ℝ) (hv : v ∈ Set.Icc D.a1 D.b1)
    (v' : ℝ) (hv' : v' ∈ Set.Icc D.a1 D.b1) :
    |D.U v - D.U v'| ≤ |v - v'| := by
  let x := v - v'
  let d := D.U v - D.U v'
  have hq₁ := D.Q_nonneg v' hv'
  have hq₂ := D.Q_le_one v' hv'
  have hq₃ := D.Q_nonneg v hv
  have hq₄ := D.Q_le_one v hv
  have hp₁ : |x * D.Q v'| ≤ |x| := by
    rw [abs_mul, abs_of_nonneg hq₁]
    exact mul_le_of_le_one_right (abs_nonneg x) hq₂
  have hp₂ : |x * D.Q v| ≤ |x| := by
    rw [abs_mul, abs_of_nonneg hq₃]
    exact mul_le_of_le_one_right (abs_nonneg x) hq₄
  have h₁ := D.bicB' v hv v' hv'
  have h₂ := D.bicB' v' hv' v hv
  have hlo : x * D.Q v' ≤ d := by
    change (v - v') * D.Q v' ≤ D.U v - D.U v'
    apply (le_sub_iff_add_le).2
    simpa [add_comm] using h₁
  have hhi : d ≤ x * D.Q v := by
    change D.U v - D.U v' ≤ (v - v') * D.Q v
    apply (sub_le_iff_le_add).2
    have hh : D.U v ≤ (v - v') * D.Q v + D.U v' := by linarith [h₂]
    exact hh
  apply (abs_le).2
  constructor
  · calc
      -|x| ≤ -|x * D.Q v'| := neg_le_neg hp₁
      _ ≤ x * D.Q v' := neg_abs_le _
      _ ≤ d := hlo
  · calc
      d ≤ x * D.Q v := hhi
      _ ≤ |x * D.Q v| := le_abs_self _
      _ ≤ |x| := hp₂
end MSData
