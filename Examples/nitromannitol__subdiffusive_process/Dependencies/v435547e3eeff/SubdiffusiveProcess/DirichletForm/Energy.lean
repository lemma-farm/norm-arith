/-
# The extended energy functional, the order on forms, and Mosco convergence
-/
module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v435547e3eeff.SubdiffusiveProcess.DirichletForm.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Extended energy, order of forms, Mosco convergence

For a closed form `E` we extend `u ↦ E(u, u)` to all of `L²(X, m)` by `⊤`
outside the domain (`SubdiffusiveProcess.DirichletForm.ClosedForm.energy`).  This makes the domain
readable off the functional and lets the order of forms and Mosco convergence be
stated without side conditions.

## Main definitions

* `SubdiffusiveProcess.DirichletForm.ClosedForm.energy`: `E(u) ∈ EReal`, equal to `⊤` off `D(E)`.
* the `Preorder` on `ClosedForm m` given by `E ≤ F ↔ ∀ u, E(u) ≤ F(u)`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.LEWithConst`: `E ≤ C · F` on `D(F)`.
* `SubdiffusiveProcess.DirichletForm.TendstoWeakly`: weak convergence in `L²(X, m)`.
* `SubdiffusiveProcess.DirichletForm.MoscoConverges`: Mosco convergence (weak liminf bound and
  existence of a strong recovery sequence).

## References

* U. Mosco, *Composite media and asymptotic Dirichlet forms*, J. Funct. Anal.
  123 (1994).
-/
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
variable {X : Type*} [MeasurableSpace X] {m : Measure X}
namespace SubdiffusiveProcess.DirichletForm
namespace ClosedForm
variable (E F : ClosedForm m)
theorem tendsto_form_self_of_tendsto_energyNormSq (E : ClosedForm m)
    {u : ℕ → Lp ℝ 2 m} {w : Lp ℝ 2 m} (hu : ∀ n : ℕ, u n ∈ E.domain)
    (hw : w ∈ E.domain)
    (h : Tendsto (fun n => E.energyNormSq (u n - w)) atTop (𝓝 0)) :
    Tendsto (fun n => E.form (u n) (u n)) atTop (𝓝 (E.form w w)) := by
  have hsub : ∀ n : ℕ, u n - w ∈ E.domain := fun n => E.domain.sub_mem (hu n) hw
  -- the `L²` norms converge
  have hnsq : Tendsto (fun n => ‖u n - w‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => E.sq_norm_le_energyNormSq (hsub n)) h
  have hn : Tendsto (fun n => ‖u n - w‖) atTop (𝓝 0) := by
    have hc : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by simpa using Real.continuous_sqrt.tendsto 0
    refine (hc.comp hnsq).congr fun n => ?_
    simp [Real.sqrt_sq (norm_nonneg _)]
  have hnorm : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 (‖w‖ ^ 2)) := by
    have : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖w‖) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hn
      simpa [Real.dist_eq] using abs_norm_sub_norm_le (u n) w
    exact this.pow 2
  -- the energy norms converge
  have hsqrt : Tendsto (fun n => Real.sqrt (E.energyNormSq (u n))) atTop
      (𝓝 (Real.sqrt (E.energyNormSq w))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hc : Tendsto (fun n => Real.sqrt (E.energyNormSq (u n - w))) atTop (𝓝 0) := by
      have hc0 : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
        simpa using Real.continuous_sqrt.tendsto 0
      simpa using! hc0.comp h
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hc
    have h1 : Real.sqrt (E.energyNormSq (u n)) ≤
        Real.sqrt (E.energyNormSq w) + Real.sqrt (E.energyNormSq (u n - w)) := by
      have := E.sqrt_energyNormSq_add_le hw (hsub n)
      simpa using this
    have h2 : Real.sqrt (E.energyNormSq w) ≤
        Real.sqrt (E.energyNormSq (u n)) + Real.sqrt (E.energyNormSq (w - u n)) := by
      have := E.sqrt_energyNormSq_add_le (hu n) (E.domain.sub_mem hw (hu n))
      simpa using this
    have h3 : E.energyNormSq (w - u n) = E.energyNormSq (u n - w) :=
      E.energyNormSq_sub_comm hw (hu n)
    rw [h3] at h2
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hE1 : Tendsto (fun n => E.energyNormSq (u n)) atTop (𝓝 (E.energyNormSq w)) := by
    have hp := hsqrt.pow 2
    rw [Real.sq_sqrt (E.energyNormSq_nonneg hw)] at hp
    exact hp.congr fun n => Real.sq_sqrt (E.energyNormSq_nonneg (hu n))
  have hfin := hE1.sub hnorm
  simp only [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq] at hfin
  simpa using hfin
end ClosedForm
end SubdiffusiveProcess.DirichletForm
