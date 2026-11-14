module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Ring.Ultra

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Examples.Example_0433e5614aea29a24faa_NonarchimedeanWhittakerBounds ====
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace DedekindZetaZeroFree.KPFiniteLocal

set_option linter.unusedVariables false in
theorem distinct_root_recurrence_uniform_bound (u : ℕ → ℂ) (α β : ℂ)
    (hne : α ≠ β) (hnorm : ‖β‖ ≤ ‖α‖)
    (hrec : ∀ n : ℕ, u (n + 2) - (α + β) * u (n + 1) + α * β * u n = 0)
    (H : ℝ) (hH : 0 ≤ H) (h0 : ‖u 0‖ ≤ H) (h1 : ‖u 1‖ ≤ H)
    (n : ℕ) 
    (h_DedekindZetaZeroFree_KPFiniteLocal_distinct_root_recurrence_formula : ∀ (u : ℕ → ℂ) (α β : ℂ),
      α ≠ β →
        (∀ (n : ℕ), u (n + 2) - (α + β) * u (n + 1) + α * β * u n = 0) →
          ∀ (n : ℕ), u n = (u 1 - β * u 0) / (α - β) * α ^ n + (α * u 0 - u 1) / (α - β) * β ^ n)
    :
    ‖u n‖ ≤ ((2 + ‖α‖ + ‖β‖) * H / ‖α - β‖) * ‖α‖ ^ n := by
  have hd : 0 < ‖α - β‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hA : ‖(u 1 - β * u 0) / (α - β)‖ ≤ (H + ‖β‖ * H) / ‖α - β‖ := by
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ hd.le
    calc
      _ ≤ ‖u 1‖ + ‖β * u 0‖ := norm_sub_le _ _
      _ = ‖u 1‖ + ‖β‖ * ‖u 0‖ := by rw [norm_mul]
      _ ≤ _ := by gcongr
  have hB : ‖(α * u 0 - u 1) / (α - β)‖ ≤ (‖α‖ * H + H) / ‖α - β‖ := by
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ hd.le
    calc
      _ ≤ ‖α * u 0‖ + ‖u 1‖ := norm_sub_le _ _
      _ = ‖α‖ * ‖u 0‖ + ‖u 1‖ := by rw [norm_mul]
      _ ≤ _ := by gcongr
  rw [h_DedekindZetaZeroFree_KPFiniteLocal_distinct_root_recurrence_formula u α β hne hrec n]
  calc
    _ ≤ ‖((u 1 - β * u 0) / (α - β)) * α ^ n‖ +
        ‖((α * u 0 - u 1) / (α - β)) * β ^ n‖ := norm_add_le _ _
    _ = ‖(u 1 - β * u 0) / (α - β)‖ * ‖α‖ ^ n +
        ‖(α * u 0 - u 1) / (α - β)‖ * ‖β‖ ^ n := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
    _ ≤ ((H + ‖β‖ * H) / ‖α - β‖) * ‖α‖ ^ n +
        ((‖α‖ * H + H) / ‖α - β‖) * ‖α‖ ^ n := by
      gcongr
    _ = _ := by ring

end DedekindZetaZeroFree.KPFiniteLocal
end
