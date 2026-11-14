module

public import Mathlib

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Examples.Example_b08766906505eb42b669_LpWeakClosed ====
/-!
# Weak closure of bounds on higher Lebesgue norms

An `Lᵖ` norm ball, viewed as a subset of scalar `L²`, is strongly closed
by Fatou's lemma and convex by Minkowski's inequality. A closed convex
subset of a real Hilbert space contains the weak limit of its elements.
These facts pass the vorticity bound to a weak `L²` limit.
-/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace Euler2D
/-- The higher Lebesgue norm ball is convex as a subset of scalar `L²`. -/
theorem convex_eLpNorm_ball
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {q : ENNReal} (hq : 1 ≤ q) (M : ℝ) :
    Convex ℝ {f : Lp ℝ 2 μ | eLpNorm f q μ ≤ ENNReal.ofReal M} := by
  intro f hf g hg a b ha hb hab
  change eLpNorm f q μ ≤ ENNReal.ofReal M at hf
  change eLpNorm g q μ ≤ ENNReal.ofReal M at hg
  change eLpNorm (a • f + b • g : Lp ℝ 2 μ) q μ ≤ ENNReal.ofReal M
  have heq : (a • f + b • g : Lp ℝ 2 μ) =ᵐ[μ]
      (fun x => a • f x + b • g x) := by
    filter_upwards [Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f,
      Lp.coeFn_smul b g] with x hadd ha' hb'
    rw [hadd]
    change (a • f : Lp ℝ 2 μ) x + (b • g : Lp ℝ 2 μ) x = _
    rw [ha', hb']
    rfl
  rw [eLpNorm_congr_ae heq]
  calc
    eLpNorm (fun x => a • f x + b • g x) q μ ≤
        eLpNorm (a • (f : α → ℝ)) q μ + eLpNorm (b • (g : α → ℝ)) q μ :=
      eLpNorm_add_le hq
    _ = ENNReal.ofReal a * eLpNorm f q μ + ENNReal.ofReal b * eLpNorm g q μ := by
      rw [eLpNorm_const_smul, eLpNorm_const_smul]
      rw [← ofReal_norm a, ← ofReal_norm b, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal M +
        ENNReal.ofReal b * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal M := by
      rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab]
      simp
end Euler2D
end
