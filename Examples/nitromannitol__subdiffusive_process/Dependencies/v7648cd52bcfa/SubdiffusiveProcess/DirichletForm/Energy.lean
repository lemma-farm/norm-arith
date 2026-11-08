/-
# The extended energy functional, the order on forms, and Mosco convergence
-/
module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v7648cd52bcfa.SubdiffusiveProcess.DirichletForm.Basic
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
def LEWithConst (E F : ClosedForm m) (C : ℝ) : Prop :=
  ∀ u ∈ F.domain, u ∈ E.domain ∧ E.form u u ≤ C * F.form u u
theorem LEWithConst.mem_domain {E F : ClosedForm m} {C : ℝ} (h : LEWithConst E F C)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) : u ∈ E.domain := (h u hu).1
theorem LEWithConst.form_le {E F : ClosedForm m} {C : ℝ} (h : LEWithConst E F C)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) : E.form u u ≤ C * F.form u u := (h u hu).2
theorem LEWithConst.trans {E F G : ClosedForm m} {C D : ℝ} (hC : 0 ≤ C)
    (h₁ : LEWithConst E F C) (h₂ : LEWithConst F G D) : LEWithConst E G (C * D) := by
  intro u hu
  refine ⟨h₁.mem_domain (h₂.mem_domain hu), ?_⟩
  calc E.form u u ≤ C * F.form u u := h₁.form_le (h₂.mem_domain hu)
    _ ≤ C * (D * G.form u u) := mul_le_mul_of_nonneg_left (h₂.form_le hu) hC
    _ = C * D * G.form u u := by ring
theorem LEWithConst.rfl (E : ClosedForm m) : LEWithConst E E 1 :=
  fun u hu => ⟨hu, by simp⟩
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
/-- **Closedness in the form the truncation argument uses.**  A sequence in the
domain that is Cauchy for the form and converges in `L²` has its limit in the
domain, and converges to it in the energy norm.

This is the step at `mfd:lem-truncation` ("by closedness,
`v_q ∈ D(E^Q)` and `w_ε → v_q` in form norm"): the `L²` convergence upgrades the
form-Cauchy property to an energy-norm Cauchy property, `ClosedForm.complete`
produces a limit, and uniqueness of `L²` limits identifies it. -/
theorem mem_domain_of_tendsto_of_formCauchy (E : ClosedForm m) (w : ℕ → Lp ℝ 2 m)
    (hw : ∀ n : ℕ, w n ∈ E.domain) (z : Lp ℝ 2 m) (hL2 : Tendsto w atTop (𝓝 z))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ r ≥ N,
      E.form (w p - w r) (w p - w r) < ε) :
    z ∈ E.domain ∧ Tendsto (fun n => E.energyNormSq (w n - z)) atTop (𝓝 0) := by
  have hL2cauchy : CauchySeq w := hL2.cauchySeq
  have hE1 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ r ≥ N,
      E.form (w p - w r) (w p - w r) + ‖w p - w r‖ ^ 2 < ε := by
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hcauchy (ε / 2) (by positivity)
    obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.mp hL2cauchy (Real.sqrt (ε / 2))
      (Real.sqrt_pos.mpr (by positivity))
    refine ⟨max N₁ N₂, fun p hp r hr => ?_⟩
    have h1 := hN₁ p (le_of_max_le_left hp) r (le_of_max_le_left hr)
    have h2 := hN₂ p (le_of_max_le_right hp) r (le_of_max_le_right hr)
    rw [dist_eq_norm] at h2
    have h3 : ‖w p - w r‖ ^ 2 < ε / 2 := by
      have hnn : (0 : ℝ) ≤ ‖w p - w r‖ := norm_nonneg _
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ ε / 2), h2, hnn,
        Real.sqrt_nonneg (ε / 2)]
    linarith
  obtain ⟨z', hz'mem, hz'⟩ := E.complete w hw hE1
  have hnormsq : Tendsto (fun n => ‖w n - z'‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hz'
    have := E.form_nonneg _ (E.domain.sub_mem (hw n) hz'mem)
    linarith
  have hnorm : Tendsto (fun n => ‖w n - z'‖) atTop (𝓝 0) := by
    have hcont : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0)
    have := hcont.comp hnormsq
    refine this.congr fun n => ?_
    simp [Real.sqrt_sq (norm_nonneg _)]
  have hzz' : z = z' := tendsto_nhds_unique hL2 (by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mpr hnorm))
  rw [hzz']
  exact ⟨hz'mem, hz'⟩
end ClosedForm
end SubdiffusiveProcess.DirichletForm
