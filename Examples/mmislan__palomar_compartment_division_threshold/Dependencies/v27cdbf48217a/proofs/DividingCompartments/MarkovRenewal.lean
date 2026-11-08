module
public import Examples.mmislan__palomar_compartment_division_threshold.Dependencies.v27cdbf48217a.proofs.DividingCompartments.FiniteBranching
set_option warningAsError true
@[expose] public section
set_option backward.isDefEq.respectTransparency false
/-! Actual countable-state marked laws with arbitrary probability rows.
Bounded rewards permit arbitrary immigrant laws, including infinite moments.
No recurrence or occupation conclusion is a model field. -/
namespace DividingCompartments.MarkovRenewal
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
noncomputable section
def Bounded {S : Type*} (f : S → ℝ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C
theorem bounded_add {S : Type*} {f g : S → ℝ} (hf : Bounded f) (hg : Bounded g) :
    Bounded (fun x => f x+g x) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  exact ⟨C+D,add_nonneg hC hD,fun x => (abs_add_le _ _).trans (add_le_add (hf x) (hg x))⟩
structure Model (S : Type*) [MeasurableSpace S] where
  step : S → Measure S
  probability : ∀ x, IsProbabilityMeasure (step x)
  rate : S → ℝ
  rate_lower : ∀ x, 1 ≤ rate x
namespace Model
variable {S : Type*} [MeasurableSpace S] (M : Model S)
instance stepProbability (x : S) : IsProbabilityMeasure (M.step x) := M.probability x
theorem rate_pos (x : S) : 0 < M.rate x := lt_of_lt_of_le zero_lt_one (M.rate_lower x)
def apply (f : S → ℝ) (x : S) : ℝ := ∫ y, f y ∂M.step x
def iter (M : Model S) : ℕ → (S → ℝ) → S → ℝ
  | 0,f => f
  | n+1,f => M.apply (M.iter n f)
theorem apply_nonneg {f : S → ℝ} (hf : ∀ x, 0 ≤ f x) (x : S) : 0 ≤ M.apply f x :=
  integral_nonneg hf
theorem iter_nonneg {f : S → ℝ} (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    ∀ x, 0 ≤ M.iter n f x := by
  induction n with
  | zero => exact hf
  | succ n ih => exact M.apply_nonneg ih
theorem iter_succ_right (f : S → ℝ) (n : ℕ) : M.iter (n+1) f=M.iter n (M.apply f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change M.apply (M.iter (n+1) f)=M.apply (M.iter n (M.apply f))
    rw [ih]
variable [Countable S] [MeasurableSingletonClass S]
theorem bounded_integrable {f : S → ℝ} (hf : Bounded f) (x : S) : Integrable f (M.step x) := by
  obtain ⟨C,_,hC⟩ := hf
  exact Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hC y)
theorem apply_bounded {f : S → ℝ} (hf : Bounded f) : Bounded (M.apply f) := by
  obtain ⟨C,hC,hf⟩ := hf
  have hi (x : S) := M.bounded_integrable ⟨C,hC,hf⟩ x
  refine ⟨C,hC,fun x => abs_le.mpr ⟨?_,?_⟩⟩
  · have hh := integral_mono (integrable_const (-C)) (hi x) (fun y => (abs_le.mp (hf y)).1)
    simpa [apply] using hh
  · have hh := integral_mono (hi x) (integrable_const C) (fun y => (abs_le.mp (hf y)).2)
    simpa [apply] using hh
theorem iter_bounded {f : S → ℝ} (hf : Bounded f) (n : ℕ) : Bounded (M.iter n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact M.apply_bounded ih
theorem apply_add {f g : S → ℝ} (hf : Bounded f) (hg : Bounded g) :
    M.apply (fun x => f x+g x)=fun x => M.apply f x+M.apply g x := by
  funext x
  exact integral_add (M.bounded_integrable hf x) (M.bounded_integrable hg x)
theorem apply_mono {f g : S → ℝ} (hf : Bounded f) (hg : Bounded g)
    (h : ∀ x, f x ≤ g x) (x : S) : M.apply f x ≤ M.apply g x :=
  integral_mono (M.bounded_integrable hf x) (M.bounded_integrable hg x) h
theorem iter_mono {f g : S → ℝ} (hf : Bounded f) (hg : Bounded g)
    (h : ∀ x, f x ≤ g x) (n : ℕ) : ∀ x, M.iter n f x ≤ M.iter n g x := by
  induction n with
  | zero => exact h
  | succ n ih => exact M.apply_mono (M.iter_bounded hf n) (M.iter_bounded hg n) ih
theorem iter_add {f g : S → ℝ} (hf : Bounded f) (hg : Bounded g) (n : ℕ) :
    M.iter n (fun x => f x+g x)=fun x => M.iter n f x+M.iter n g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iter,ih]
    exact M.apply_add (M.iter_bounded hf n) (M.iter_bounded hg n)
theorem finite_reward_budget {V c : S → ℝ} (hV : Bounded V) (hc : Bounded c)
    (hstep : ∀ x, M.apply V x+c x ≤ V x) (N : ℕ) (x : S) :
    M.iter N V x+∑ n ∈ Finset.range N, M.iter n c x ≤ V x := by
  induction N with
  | zero => simp [iter]
  | succ N ih =>
    have h := M.iter_mono (bounded_add (M.apply_bounded hV) hc) hV hstep N x
    rw [congrFun (M.iter_add (M.apply_bounded hV) hc N) x,← M.iter_succ_right] at h
    rw [Finset.sum_range_succ]
    linarith
theorem reward_series_bound {V c : S → ℝ} (hV : Bounded V) (hc : Bounded c)
    (hV0 : ∀ x, 0 ≤ V x) (hc0 : ∀ x, 0 ≤ c x)
    (hstep : ∀ x, M.apply V x+c x ≤ V x) (x : S) :
    Summable (fun n => M.iter n c x) ∧ (∑' n, M.iter n c x) ≤ V x := by
  have hn := fun n => M.iter_nonneg hc0 n x
  have hb : ∀ N, (∑ n ∈ Finset.range N, M.iter n c x) ≤ V x := by
    intro N
    have hh := M.finite_reward_budget hV hc hstep N x
    have hv := M.iter_nonneg hV0 N x
    linarith
  exact ⟨summable_of_sum_range_le hn hb,Real.tsum_le_of_sum_range_le hn hb⟩
def markedStepLaw (x : S) : Measure (S × ℝ) := (M.step x).prod (expMeasure (M.rate x))
instance markedProbability (x : S) : IsProbabilityMeasure (M.markedStepLaw x) := by
  have : IsProbabilityMeasure (expMeasure (M.rate x)) := isProbabilityMeasure_expMeasure (M.rate_pos x)
  unfold markedStepLaw
  infer_instance
def markedKernel : Kernel S (S × ℝ) where
  toFun := M.markedStepLaw
  measurable' := measurable_of_countable _
instance markedMarkov : IsMarkovKernel M.markedKernel where
  isProbabilityMeasure x := M.markedProbability x
def pathKernel (n : ℕ) : Kernel (Finset.Iic n → S × ℝ) (S × ℝ) :=
  M.markedKernel.comap (fun h => (h ⟨n, FiniteBranching.lastIndex_mem n⟩).1)
    (FiniteBranching.lastState_measurable S n)
instance pathMarkov (n : ℕ) : IsMarkovKernel (M.pathKernel n) := by unfold pathKernel; infer_instance
def pathLaw (x : S) : Measure (ℕ → S × ℝ) :=
  Kernel.traj (X := fun _ : ℕ => S × ℝ) M.pathKernel 0 (fun _ => (x,(0 : ℝ)))
instance pathProbability (x : S) : IsProbabilityMeasure (M.pathLaw x) := by unfold pathLaw; infer_instance
theorem pathLaw_step (x : S) (n : ℕ) :
    (M.pathLaw x).map (Preorder.frestrictLe n) ⊗ₘ M.pathKernel n =
      (M.pathLaw x).map (fun w => (Preorder.frestrictLe n w,w (n+1))) := by
  change (Kernel.traj (X := fun _ : ℕ => S × ℝ) M.pathKernel 0 (fun _ => (x,(0 : ℝ)))).map
    (Preorder.frestrictLe n) ⊗ₘ M.pathKernel n = _
  rw [Kernel.traj_map_frestrictLe_apply]
  exact Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)
theorem pathLaw_initial (x : S) : (M.pathLaw x).map (fun w => w 0)=Measure.dirac (x,(0 : ℝ)) := by
  have hh : (M.pathLaw x).map (Preorder.frestrictLe 0)=
      Measure.dirac (fun _ : Finset.Iic 0 => (x,(0 : ℝ))) := by
    change (Kernel.traj (X := fun _ : ℕ => S × ℝ) M.pathKernel 0 (fun _ => (x,(0 : ℝ)))).map
      (Preorder.frestrictLe 0) = _
    rw [Kernel.traj_map_frestrictLe_apply,Kernel.partialTraj_self,Kernel.id_apply]
  have hm : (fun w : ℕ → S × ℝ => w 0)=
      (fun h : Finset.Iic 0 → S × ℝ => h ⟨0,Finset.mem_Iic.mpr le_rfl⟩) ∘ Preorder.frestrictLe 0 := rfl
  rw [hm,← Measure.map_map (by fun_prop) (by fun_prop),hh]
  simp
omit [Countable S] [MeasurableSingletonClass S] in
theorem marked_state_marginal (x : S) : (M.markedStepLaw x).map Prod.fst=M.step x := by
  have : IsProbabilityMeasure (expMeasure (M.rate x)) := isProbabilityMeasure_expMeasure (M.rate_pos x)
  unfold markedStepLaw
  simp
omit [Countable S] [MeasurableSingletonClass S] in
theorem marked_holding_marginal (x : S) : (M.markedStepLaw x).map Prod.snd=expMeasure (M.rate x) := by
  have : IsProbabilityMeasure (expMeasure (M.rate x)) := isProbabilityMeasure_expMeasure (M.rate_pos x)
  unfold markedStepLaw
  simp
theorem pathLaw_lintegral_step (x : S) (n : ℕ)
    (g : (Finset.Iic n → S × ℝ) × (S × ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ w, g (Preorder.frestrictLe n w,w (n+1)) ∂M.pathLaw x) =
      ∫⁻ h, ∫⁻ z, g (h,z) ∂M.pathKernel n h ∂(M.pathLaw x).map (Preorder.frestrictLe n) := by
  calc
    _ = ∫⁻ w, g w ∂(M.pathLaw x).map (fun w => (Preorder.frestrictLe n w,w (n+1))) :=
      (lintegral_map hg (by fun_prop)).symm
    _ = ∫⁻ w, g w ∂((M.pathLaw x).map (Preorder.frestrictLe n) ⊗ₘ M.pathKernel n) := by rw [M.pathLaw_step]
    _ = _ := Measure.lintegral_compProd hg
theorem marked_state_lintegral {f : S → ℝ} (hf : Bounded f)
    (hf0 : ∀ x, 0 ≤ f x) (x : S) :
    (∫⁻ z, ENNReal.ofReal (f z.1) ∂M.markedStepLaw x)=ENNReal.ofReal (M.apply f x) := by
  have he := lintegral_map (μ := M.markedStepLaw x)
    (f := fun y => ENNReal.ofReal (f y)) ((measurable_of_countable f).ennreal_ofReal) measurable_fst
  rw [M.marked_state_marginal] at he
  rw [← he]
  exact (ofReal_integral_eq_lintegral_ofReal (M.bounded_integrable hf x)
    (Filter.Eventually.of_forall hf0)).symm
theorem pathLaw_state_lintegral {f : S → ℝ} (hf : Bounded f)
    (hf0 : ∀ x, 0 ≤ f x) (x : S) (n : ℕ) :
    (∫⁻ w, ENNReal.ofReal (f (w n).1) ∂M.pathLaw x)=ENNReal.ofReal (M.iter n f x) := by
  induction n generalizing f with
  | zero =>
    have he := lintegral_map (μ := M.pathLaw x)
      (f := fun z : S × ℝ => ENNReal.ofReal (f z.1)) (by
        have hh := measurable_of_countable f
        fun_prop) (measurable_pi_apply 0)
    rw [M.pathLaw_initial] at he
    simpa [iter] using he.symm
  | succ n ih =>
    let g : (Finset.Iic n → S × ℝ) × (S × ℝ) → ℝ≥0∞ := fun z => ENNReal.ofReal (f z.2.1)
    have hg : Measurable g := by have hh := measurable_of_countable f; unfold g; fun_prop
    have hs := M.pathLaw_lintegral_step x n g hg
    have hi : ∀ h, (∫⁻ z, g (h,z) ∂M.pathKernel n h)=
        ENNReal.ofReal (M.apply f (h ⟨n,Finset.mem_Iic.mpr le_rfl⟩).1) := by
      intro h
      exact M.marked_state_lintegral hf hf0 _
    simp_rw [hi] at hs
    have hm : Measurable (fun h : Finset.Iic n → S × ℝ =>
        ENNReal.ofReal (M.apply f (h ⟨n,Finset.mem_Iic.mpr le_rfl⟩).1)) := by
      have hh := measurable_of_countable (M.apply f)
      fun_prop
    rw [lintegral_map hm (by fun_prop)] at hs
    change (∫⁻ w, ENNReal.ofReal (f (w (n+1)).1) ∂M.pathLaw x)=
      (∫⁻ w, ENNReal.ofReal (M.apply f (w n).1) ∂M.pathLaw x) at hs
    rw [hs,ih (M.apply_bounded hf) (M.apply_nonneg hf0),M.iter_succ_right]
omit [Countable S] [MeasurableSingletonClass S] in
theorem marked_holding_lintegral (x : S) :
    (∫⁻ z, ENNReal.ofReal (max 0 z.2) ∂M.markedStepLaw x)=ENNReal.ofReal (1/M.rate x) := by
  have he := lintegral_map (μ := M.markedStepLaw x)
    (f := fun t : ℝ => ENNReal.ofReal (max 0 t)) (by fun_prop) measurable_snd
  rw [M.marked_holding_marginal] at he
  rw [← he]
  exact DividingCompartments.FiniteBranching.exponential_holding_lintegral _ (M.rate_pos x)
omit [Countable S] [MeasurableSingletonClass S] in
theorem bounded_div_rate {f : S → ℝ} (hf : Bounded f) : Bounded (fun x => f x/M.rate x) := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨C,hC,fun x => ?_⟩
  rw [abs_div,abs_of_pos (M.rate_pos x)]
  exact (div_le_iff₀ (M.rate_pos x)).mpr ((hf x).trans (by nlinarith [M.rate_lower x]))
theorem pathLaw_clock_term {f : S → ℝ} (hf : Bounded f) (hf0 : ∀ x, 0 ≤ f x)
    (x : S) (n : ℕ) :
    (∫⁻ w, ENNReal.ofReal (f (w n).1)*ENNReal.ofReal (max 0 (w (n+1)).2) ∂M.pathLaw x)=
      ENNReal.ofReal (M.iter n (fun y => f y/M.rate y) x) := by
  let g : (Finset.Iic n → S × ℝ) × (S × ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (f (z.1 ⟨n,Finset.mem_Iic.mpr le_rfl⟩).1)*ENNReal.ofReal (max 0 z.2.2)
  have hg : Measurable g := by have hh := measurable_of_countable f; unfold g; fun_prop
  have hs := M.pathLaw_lintegral_step x n g hg
  have hi : ∀ h, (∫⁻ z, g (h,z) ∂M.pathKernel n h)=
      ENNReal.ofReal (f (h ⟨n,Finset.mem_Iic.mpr le_rfl⟩).1/
        M.rate (h ⟨n,Finset.mem_Iic.mpr le_rfl⟩).1) := by
    intro h
    change (∫⁻ z, ENNReal.ofReal (f (h ⟨n,Finset.mem_Iic.mpr le_rfl⟩).1)*
      ENNReal.ofReal (max 0 z.2) ∂M.markedStepLaw (h ⟨n,Finset.mem_Iic.mpr le_rfl⟩).1)=_
    rw [lintegral_const_mul _ (by fun_prop),M.marked_holding_lintegral,
      ← ENNReal.ofReal_mul (hf0 _)]
    congr 1
    ring
  simp_rw [hi] at hs
  have hm : Measurable (fun h : Finset.Iic n → S × ℝ =>
      ENNReal.ofReal (f (h ⟨n,Finset.mem_Iic.mpr le_rfl⟩).1/
        M.rate (h ⟨n,Finset.mem_Iic.mpr le_rfl⟩).1)) := by
    have hh := measurable_of_countable (fun y => f y/M.rate y)
    fun_prop
  rw [lintegral_map hm (by fun_prop)] at hs
  change (∫⁻ w, ENNReal.ofReal (f (w n).1)*ENNReal.ofReal (max 0 (w (n+1)).2) ∂M.pathLaw x)=
    (∫⁻ w, ENNReal.ofReal (f (w n).1/M.rate (w n).1) ∂M.pathLaw x) at hs
  rw [hs,M.pathLaw_state_lintegral (M.bounded_div_rate hf) (fun y => div_nonneg (hf0 y) (M.rate_pos y).le)]
def occupation (f : S → ℝ) (w : ℕ → S × ℝ) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (f (w n).1)*ENNReal.ofReal (max 0 (w (n+1)).2)
theorem occupation_expectation {f : S → ℝ} (hf : Bounded f) (hf0 : ∀ x, 0 ≤ f x)
    (x : S) (hs : Summable (fun n => M.iter n (fun y => f y/M.rate y) x)) :
    (∫⁻ w, occupation f w ∂M.pathLaw x)=
      ENNReal.ofReal (∑' n, M.iter n (fun y => f y/M.rate y) x) := by
  unfold occupation
  rw [lintegral_tsum (fun n => by have hh := measurable_of_countable f; fun_prop)]
  simp_rw [M.pathLaw_clock_term hf hf0]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun n => M.iter_nonneg (fun y => div_nonneg (hf0 y) (M.rate_pos y).le) n x) hs).symm
theorem occupation_budget {V : S → ℝ} (hV : Bounded V) (hV0 : ∀ x, 0 ≤ V x)
    {k : ℝ} (hk : 0 < k) (hstep : ∀ x, M.apply V x+k*(V x/M.rate x) ≤ V x)
    (x : S) : (∫⁻ w, occupation V w ∂M.pathLaw x) ≤ ENNReal.ofReal (V x/k) := by
  have hU : Bounded (fun y => V y/k) := by
    obtain ⟨C,hC,hV⟩ := hV
    refine ⟨C/k,div_nonneg hC hk.le,fun y => ?_⟩
    rw [abs_div,abs_of_pos hk]
    exact div_le_div_of_nonneg_right (hV y) hk.le
  have hU0 : ∀ y, 0 ≤ V y/k := fun y => div_nonneg (hV0 y) hk.le
  have hc := M.bounded_div_rate hV
  have hc0 : ∀ y, 0 ≤ V y/M.rate y := fun y => div_nonneg (hV0 y) (M.rate_pos y).le
  have hh : ∀ y, M.apply (fun z => V z/k) y+V y/M.rate y ≤ V y/k := by
    intro y
    have he : M.apply (fun z => V z/k) y=M.apply V y/k := integral_div k V
    rw [he]
    apply (le_div_iff₀ hk).mpr
    rw [add_mul,div_mul_cancel₀ _ hk.ne']
    nlinarith [hstep y]
  obtain ⟨hs,hb⟩ := M.reward_series_bound hU hc hU0 hc0 hh x
  rw [M.occupation_expectation hV hV0 x hs]
  exact ENNReal.ofReal_le_ofReal hb
end Model
end
end DividingCompartments.MarkovRenewal
