module
public import Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.v33a87da00ae6.DedekindZetaZeroFree.Arithmetic.RayClasses.Character
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.LargeSieve.Vendor
noncomputable section
open scoped NumberField Classical ContDiff
def S (b : ℝ) (N : ℕ) (h : ℝ → ℂ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1),
    sSup ((fun x : ℝ => ‖iteratedDeriv i h x‖) '' Set.Icc 0 b)
def PositiveSideSupport (b : ℝ) (h : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, b < x → h x = 0
theorem S_finite (b : ℝ) (hb : 0 < b) (N : ℕ) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) :
    ∀ i ∈ Finset.range (N + 1),
      BddAbove ((fun x : ℝ => ‖iteratedDeriv i h x‖) '' Set.Icc 0 b) := by
  intro i _
  have hcont : Continuous (fun x : ℝ => ‖iteratedDeriv i h x‖) :=
    (hh.continuous_iteratedDeriv i (by simp)).norm
  exact (isCompact_Icc.image hcont).bddAbove
theorem S_nonneg (b : ℝ) (hb : 0 < b) (N : ℕ) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) : 0 ≤ S b N h := by
  unfold S
  exact Finset.sum_nonneg fun i _ =>
    Real.sSup_nonneg fun y ⟨x, _, hy⟩ => hy ▸ norm_nonneg _
end
end DedekindZetaZeroFree.LargeSieve.Vendor
