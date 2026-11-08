module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Mathlib
set_option autoImplicit false
@[expose] public section
/- Adaptation: declarations are placed in ColeHopfFoundation to avoid duplicate names when imported alongside the independently sourced RSAT library. -/
namespace ColeHopfFoundation
open _root_.MeasureTheory
open _root_.ProbabilityTheory
/-!
# Fernique consequences

For a Gaussian measure `μ` on a second-countable Banach space, `x ↦ exp(C ‖x‖²)` is integrable
for some `C > 0`. Main: exponential-square integrability of continuous linear functionals.
-/
open MeasureTheory ProbabilityTheory
open scoped _root_.ENNReal _root_.Real _root_.Topology
namespace ProbabilityTheory
namespace IsGaussian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]
  {μ : Measure E} [ProbabilityTheory.IsGaussian μ]
theorem integrable_norm_pow (n : ℕ) : Integrable (fun x : E => ‖x‖ ^ n) μ := by
  have hLp : MemLp (fun x : E => x) (n : ℝ≥0∞) μ :=
    ProbabilityTheory.IsGaussian.memLp_id (μ := μ) (p := (n : ℝ≥0∞)) (by simp)
  have : IsFiniteMeasure μ := by infer_instance
  simpa using (MeasureTheory.MemLp.integrable_norm_pow' (μ := μ) (f := fun x : E => x) hLp)
/-- Polynomial growth domination helper: `(1 + ‖x‖)^n` is integrable for all `n`. -/
theorem integrable_one_add_norm_pow (n : ℕ) :
    Integrable (fun x : E => (1 + ‖x‖) ^ n) μ := by
  have hn : Integrable (fun x : E => ‖x‖ ^ n) μ := integrable_norm_pow (μ := μ) n
  have hconst : Integrable (fun _ : E => (1 : ℝ)) μ := integrable_const (μ := μ) (c := (1 : ℝ))
  have hsum : Integrable (fun x : E => (1 : ℝ) + ‖x‖ ^ n) μ := hconst.add hn
  have hsum' : Integrable (fun x : E => ((2 : ℝ) ^ (n - 1)) * ((1 : ℝ) + ‖x‖ ^ n)) μ :=
    hsum.const_mul ((2 : ℝ) ^ (n - 1))
  refine hsum'.mono' (by fun_prop) (ae_of_all _ (fun x => ?_))
  have hle : (1 + ‖x‖) ^ n ≤ (2 : ℝ) ^ (n - 1) * ((1 : ℝ) ^ n + (‖x‖) ^ n) :=
    add_pow_le (a := (1 : ℝ)) (b := ‖x‖) (by positivity) (by positivity) n
  have hpos : 0 ≤ (1 + ‖x‖) ^ n := by positivity
  have hnorm : ‖(1 + ‖x‖) ^ n‖ = (1 + ‖x‖) ^ n := Real.norm_of_nonneg hpos
  have hle' : (1 + ‖x‖) ^ n ≤ (2 : ℝ) ^ (n - 1) * ((1 : ℝ) + ‖x‖ ^ n) := by
    simpa [pow_zero, one_pow, add_assoc, add_comm, add_left_comm] using hle
  simpa [hnorm]
end IsGaussian
end ProbabilityTheory
end ColeHopfFoundation
