module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v8addd2a3c129.RequestProject.Euler.Basic
/-!
# Auxiliary estimates for weak Euler solutions

Technical lemmas on the space `L²(𝕋²)` used to manipulate the weak formulation:
`L²` bilinear estimates, continuity in time of the weak-formulation integrands along a
continuous `L²`-valued path, and the time-integrated pairing with `∂ₜφ`.
-/
@[expose] public section
open MeasureTheory Real Filter Topology Set
open scoped ContDiff
namespace Euler2D
/-- The closed square `[0,2π]²`. -/
def closedBox : Set R2 := {x | ∀ i, x i ∈ Icc 0 (2 * π)}
lemma torusBox_subset_closedBox : torusBox ⊆ closedBox :=
  fun _ hx i => Ico_subset_Icc_self (hx i)
lemma isCompact_closedBox : IsCompact closedBox := by
  have : closedBox = (WithLp.equiv 2 (Fin 2 → ℝ)).symm '' (univ.pi fun _ => Icc 0 (2 * π)) := by
    ext x
    simp only [closedBox, mem_setOf_eq, mem_image, Set.mem_pi]
    constructor
    · intro hx; exact ⟨WithLp.equiv 2 _ x, fun i _ => hx i, by simp⟩
    · rintro ⟨y, hy, rfl⟩ i; simpa using hy i (mem_univ _)
  rw [this]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
instance : IsFiniteMeasure μT :=
  isFiniteMeasure_restrict.2 (measure_mono torusBox_subset_closedBox |>.trans_lt
    isCompact_closedBox.measure_lt_top).ne
variable {φ : ℝ → R2 → R2}
variable {φ : ℝ → R2 → R2}
end Euler2D
end
