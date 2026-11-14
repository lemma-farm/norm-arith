module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Data.Finset.Order
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Choose
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

-- ==== Examples.mmislan__palomar_shared_resource_realizations.Examples.Example_a3fa0a9280369f8ec3c5_AffineLayers ====
set_option warningAsError true
@[expose] public section
namespace OAI
open Filter Topology
noncomputable section
namespace Problem326.Affine
lemma offset_isLittleO_of_normalized_limit {c : ℝ → ℝ} {β q A : ℝ}
    (hqβ : q < β)
    (hc : Tendsto (fun h : ℝ => c h / h ^ β) (𝓝[>] (0 : ℝ)) (𝓝 A)) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) c (fun h : ℝ => h ^ q) := by
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousWithinAt_id
  have hpow : Tendsto (fun h : ℝ => h ^ β / h ^ q)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hlim := hid.rpow_const_nhds_zero (sub_pos.mpr hqβ)
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact Real.rpow_sub hh β q
  have hlim := hc.mul hpow
  simp only [mul_zero] at hlim
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh β)
    field_simp [hne]
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact fun hzero => (ne_of_gt (Real.rpow_pos_of_pos hh q) hzero).elim
end Problem326.Affine
end
end OAI
