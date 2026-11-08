module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v33f92a46e50d.Lemmas.GuerraTalagrand.Bound.Basic
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v33f92a46e50d.Lemmas.SmartPath.IndependentEndpoint
public import Mathlib
set_option autoImplicit true
set_option linter.deprecated false
@[expose] public section
open MeasureTheory ProbabilityTheory Real BigOperators
open PhysLean.Probability.GaussianIBP
open scoped ContDiff
set_option autoImplicit false
namespace SpinGlass.AT
/-- Euclidean space of real fields indexed by a finite state type. -/
abbrev GTStateSpace (S : Type*) [Fintype S] := EuclideanSpace ℝ S
/-- A finite-state partition function with a fixed deterministic potential. -/
noncomputable def gtStatePartition
    {S : Type*} [Fintype S] (V : S → ℝ) (H : GTStateSpace S) : ℝ :=
  ∑ ξ : S, Real.exp (H ξ + V ξ)
/-- The Gibbs probability associated with `gtStatePartition`. -/
noncomputable def gtStateGibbs
    {S : Type*} [Fintype S] (V : S → ℝ) (H : GTStateSpace S) (ξ : S) : ℝ :=
  Real.exp (H ξ + V ξ) / gtStatePartition V H
/-- The finite-state log-partition function. -/
noncomputable def gtStateLogPartition
    {S : Type*} [Fintype S] (V : S → ℝ) (H : GTStateSpace S) : ℝ :=
  Real.log (gtStatePartition V H)
lemma gtStatePartition_pos
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) :
    0 < gtStatePartition V H := by
  classical
  exact Finset.sum_pos' (fun ξ _ => (Real.exp_pos (H ξ + V ξ)).le)
    ⟨Classical.choice inferInstance, Finset.mem_univ _, Real.exp_pos _⟩
lemma gtStatePartition_ne_zero
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) :
    gtStatePartition V H ≠ 0 :=
  (gtStatePartition_pos V H).ne'
lemma gtStateGibbs_nonneg
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) (ξ : S) :
    0 ≤ gtStateGibbs V H ξ := by
  exact div_nonneg (Real.exp_pos _).le (gtStatePartition_pos V H).le
lemma gtStateGibbs_le_one
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) (ξ : S) :
    gtStateGibbs V H ξ ≤ 1 := by
  classical
  unfold gtStateGibbs gtStatePartition
  rw [div_le_one (Finset.sum_pos' (fun η _ => (Real.exp_pos _).le)
    ⟨ξ, Finset.mem_univ _, Real.exp_pos _⟩)]
  exact Finset.single_le_sum
    (f := fun η : S => Real.exp (H η + V η))
    (fun η _ => (Real.exp_pos _).le) (Finset.mem_univ ξ)
lemma sum_gtStateGibbs
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) :
    ∑ ξ : S, gtStateGibbs V H ξ = 1 := by
  classical
  rw [show (∑ ξ : S, gtStateGibbs V H ξ) =
      (∑ ξ : S, Real.exp (H ξ + V ξ)) / gtStatePartition V H by
    simp only [gtStateGibbs, Finset.sum_div]]
  exact div_self (gtStatePartition_ne_zero V H)
lemma contDiff_gtStatePartition
    {S : Type*} [Fintype S] (V : S → ℝ) :
    ContDiff ℝ ∞ (gtStatePartition V) := by
  classical
  unfold gtStatePartition
  fun_prop
lemma contDiff_gtStateLogPartition
    {S : Type*} [Fintype S] [Nonempty S] (V : S → ℝ) :
    ContDiff ℝ ∞ (gtStateLogPartition V) := by
  unfold gtStateLogPartition
  exact (contDiff_gtStatePartition V).log (fun H => gtStatePartition_ne_zero V H)
lemma contDiff_gtStateGibbs
    {S : Type*} [Fintype S] [Nonempty S] (V : S → ℝ) (ξ : S) :
    ContDiff ℝ ∞ (fun H : GTStateSpace S => gtStateGibbs V H ξ) := by
  unfold gtStateGibbs
  apply ContDiff.div
  · fun_prop
  · exact contDiff_gtStatePartition V
  · exact fun H => gtStatePartition_ne_zero V H
lemma fderiv_gtStatePartition_apply
    {S : Type*} [Fintype S]
    (V : S → ℝ) (H K : GTStateSpace S) :
    fderiv ℝ (gtStatePartition V) H K =
      ∑ ξ : S, Real.exp (H ξ + V ξ) * K ξ := by
  classical
  unfold gtStatePartition
  rw [fderiv_fun_sum]
  · simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro ξ _
    have hd : HasFDerivAt
        (fun H' : GTStateSpace S => Real.exp (H' ξ + V ξ))
        (Real.exp (H ξ + V ξ) •
          (EuclideanSpace.proj ξ : GTStateSpace S →L[ℝ] ℝ)) H :=
      (((EuclideanSpace.proj ξ : GTStateSpace S →L[ℝ] ℝ).hasFDerivAt
        ).add_const (V ξ)).exp
    have hf := hd.fderiv
    have happ := congrArg (fun L : GTStateSpace S →L[ℝ] ℝ => L K) hf
    simpa using happ
  · intro ξ _
    fun_prop
lemma fderiv_gtStateLogPartition_apply
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H K : GTStateSpace S) :
    fderiv ℝ (gtStateLogPartition V) H K =
      ∑ ξ : S, gtStateGibbs V H ξ * K ξ := by
  classical
  have hlog := ((contDiff_gtStatePartition V).differentiable (by simp)
    ).differentiableAt.hasFDerivAt.log
    (gtStatePartition_ne_zero V H)
  have hf := hlog.fderiv
  change fderiv ℝ (fun x : GTStateSpace S => Real.log (gtStatePartition V x)) H K = _
  rw [hf]
  simp only [ContinuousLinearMap.smul_apply]
  rw [fderiv_gtStatePartition_apply]
  unfold gtStateGibbs
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  field_simp [gtStatePartition_ne_zero V H]
lemma norm_fderiv_gtStateLogPartition_le_one
    {S : Type*} [Fintype S] [Nonempty S]
    (V : S → ℝ) (H : GTStateSpace S) :
    ‖fderiv ℝ (gtStateLogPartition V) H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro K
  rw [fderiv_gtStateLogPartition_apply]
  have hK (ξ : S) : |K ξ| ≤ ‖K‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (p := (2 : ENNReal)) K ξ
  rw [Real.norm_eq_abs]
  calc
    |∑ ξ : S, gtStateGibbs V H ξ * K ξ| ≤
        ∑ ξ : S, |gtStateGibbs V H ξ * K ξ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ξ : S, gtStateGibbs V H ξ * |K ξ| := by
      apply Finset.sum_congr rfl
      intro ξ _
      rw [abs_mul, abs_of_nonneg (gtStateGibbs_nonneg V H ξ)]
    _ ≤ ∑ ξ : S, gtStateGibbs V H ξ * ‖K‖ := by
      exact Finset.sum_le_sum fun ξ _ =>
        mul_le_mul_of_nonneg_left (hK ξ) (gtStateGibbs_nonneg V H ξ)
    _ ≤ 1 * ‖K‖ := by rw [← Finset.sum_mul, sum_gtStateGibbs, one_mul]
/-- Finite log-sum-exp has at most linear growth in its field. -/
noncomputable def hasModerateGrowth_gtStateLogPartition
    {S : Type*} [Fintype S] [Nonempty S] (V : S → ℝ) :
    HasModerateGrowth (gtStateLogPartition V) := by
  classical
  let D : ℝ := ∑ ξ : S, |V ξ|
  let C : ℝ := Real.log (Fintype.card S : ℝ) + D + 1
  have hcard : 0 < Fintype.card S := Fintype.card_pos
  have hcard1 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast hcard
  have hlog0 : 0 ≤ Real.log (Fintype.card S : ℝ) := Real.log_nonneg hcard1
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun ξ _ => abs_nonneg _
  refine ⟨C, 1, by dsimp [C]; linarith, ?_, ?_⟩
  · intro H
    have hH (ξ : S) : |H ξ| ≤ ‖H‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (p := (2 : ENNReal)) H ξ
    let ξ₀ : S := Classical.choice inferInstance
    have hterm : Real.exp (H ξ₀ + V ξ₀) ≤ gtStatePartition V H := by
      unfold gtStatePartition
      exact Finset.single_le_sum
        (f := fun ξ : S => Real.exp (H ξ + V ξ))
        (fun ξ _ => (Real.exp_pos _).le) (Finset.mem_univ ξ₀)
    have hlower : -(‖H‖ + D) ≤ gtStateLogPartition V H := by
      have hlogterm := Real.log_le_log (Real.exp_pos _) hterm
      rw [Real.log_exp] at hlogterm
      have hV : |V ξ₀| ≤ D := Finset.single_le_sum
        (fun ξ _ => abs_nonneg (V ξ)) (Finset.mem_univ ξ₀)
      unfold gtStateLogPartition
      linarith [neg_le_abs (H ξ₀), neg_le_abs (V ξ₀), hH ξ₀]
    have hupperZ : gtStatePartition V H ≤
        (Fintype.card S : ℝ) * Real.exp (‖H‖ + D) := by
      unfold gtStatePartition
      calc
        (∑ ξ : S, Real.exp (H ξ + V ξ)) ≤
            ∑ _ξ : S, Real.exp (‖H‖ + D) := by
          apply Finset.sum_le_sum
          intro ξ _
          apply Real.exp_le_exp.mpr
          have hV : |V ξ| ≤ D := Finset.single_le_sum
            (fun η _ => abs_nonneg (V η)) (Finset.mem_univ ξ)
          linarith [le_abs_self (H ξ), le_abs_self (V ξ), hH ξ]
        _ = (Fintype.card S : ℝ) * Real.exp (‖H‖ + D) := by simp
    have hupper : gtStateLogPartition V H ≤
        Real.log (Fintype.card S : ℝ) + ‖H‖ + D := by
      have hlog := Real.log_le_log (gtStatePartition_pos V H) hupperZ
      have hcard0 : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
      rw [Real.log_mul hcard0 (Real.exp_ne_zero _), Real.log_exp] at hlog
      simpa [gtStateLogPartition, add_assoc] using hlog
    have habs : |gtStateLogPartition V H| ≤
        Real.log (Fintype.card S : ℝ) + D + ‖H‖ := by
      rw [abs_le]
      constructor <;> linarith
    calc
      |gtStateLogPartition V H| ≤
          Real.log (Fintype.card S : ℝ) + D + ‖H‖ := habs
      _ ≤ C * (1 + ‖H‖) ^ 1 := by
        dsimp [C]
        rw [pow_one]
        nlinarith [norm_nonneg H]
  · intro H
    calc
      ‖fderiv ℝ (gtStateLogPartition V) H‖ ≤ 1 :=
        norm_fderiv_gtStateLogPartition_le_one V H
      _ ≤ C * (1 + ‖H‖) ^ 1 := by
        dsimp [C]
        rw [pow_one]
        nlinarith [norm_nonneg H]
/-- Affine pullback preserves moderate growth for a finite log-partition. -/
noncomputable def hasModerateGrowth_gtStateLogPartition_comp
    {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]
    (V : S → ℝ) (L : EuclideanSpace ℝ I →L[ℝ] GTStateSpace S)
    (H₀ : GTStateSpace S) :
    HasModerateGrowth (fun z => gtStateLogPartition V (L z + H₀)) := by
  let base := hasModerateGrowth_gtStateLogPartition V
  let C : ℝ := (base.C + 1) * (1 + ‖L‖ + ‖H₀‖) + 1
  refine ⟨C, 1, by
    dsimp [C]
    nlinarith [base.Cpos, norm_nonneg L, norm_nonneg H₀], ?_, ?_⟩
  · intro z
    have hb := base.F_bound (L z + H₀)
    have hnorm : 1 + ‖L z + H₀‖ ≤
        (1 + ‖L‖ + ‖H₀‖) * (1 + ‖z‖) := by
      have hL := L.le_opNorm z
      have hadd := norm_add_le (L z) H₀
      nlinarith [norm_nonneg L, norm_nonneg H₀, norm_nonneg z]
    rw [show base.m = 1 by rfl, pow_one] at hb
    rw [pow_one]
    calc
      |gtStateLogPartition V (L z + H₀)| ≤ base.C * (1 + ‖L z + H₀‖) := hb
      _ ≤ base.C * ((1 + ‖L‖ + ‖H₀‖) * (1 + ‖z‖)) :=
        mul_le_mul_of_nonneg_left hnorm base.Cpos.le
      _ ≤ C * (1 + ‖z‖) := by
        dsimp [C]
        nlinarith [base.Cpos, norm_nonneg L, norm_nonneg H₀, norm_nonneg z]
  · intro z
    have hg : HasFDerivAt (gtStateLogPartition V)
        (fderiv ℝ (gtStateLogPartition V) (L z + H₀)) (L z + H₀) :=
      ((contDiff_gtStateLogPartition V).differentiable (by simp)
        ).differentiableAt.hasFDerivAt
    have hcomp := hg.comp z (L.hasFDerivAt.add_const H₀)
    have hf := hcomp.fderiv
    change fderiv ℝ (fun z => gtStateLogPartition V (L z + H₀)) z = _ at hf
    rw [hf, pow_one]
    calc
      ‖(fderiv ℝ (gtStateLogPartition V) (L z + H₀)).comp L‖ ≤
          ‖fderiv ℝ (gtStateLogPartition V) (L z + H₀)‖ * ‖L‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖L‖ := by
        gcongr
        exact norm_fderiv_gtStateLogPartition_le_one V (L z + H₀)
      _ ≤ C * (1 + ‖z‖) := by
        have hbase : 1 ≤ base.C + 1 := by linarith [base.Cpos]
        have hfactor : 0 ≤ 1 + ‖L‖ + ‖H₀‖ := by positivity
        have hprod : 1 + ‖L‖ + ‖H₀‖ ≤
            (base.C + 1) * (1 + ‖L‖ + ‖H₀‖) := by
          simpa [one_mul] using mul_le_mul_of_nonneg_right hbase hfactor
        have hLC : ‖L‖ ≤ C := by
          dsimp [C]
          linarith [norm_nonneg H₀]
        have hC0 : 0 ≤ C := by
          dsimp [C]
          positivity
        calc
          1 * ‖L‖ = ‖L‖ := one_mul _
          _ ≤ C := hLC
          _ ≤ C * (1 + ‖z‖) := by
            simpa [mul_one] using
              mul_le_mul_of_nonneg_left
                (show 1 ≤ 1 + ‖z‖ by linarith [norm_nonneg z]) hC0
end SpinGlass.AT
