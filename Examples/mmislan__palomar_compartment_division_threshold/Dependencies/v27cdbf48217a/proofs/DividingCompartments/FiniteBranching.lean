module
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
set_option warningAsError true
@[expose] public section
/-!
State-dependent finite-row Markov-renewal foundation. Adapted from the existing
PositiveRecurrence.JumpChainFoster source SHA256 74a6c572d2ed0c4d30a9e5b28a95fa74473e2642b52ca97a3588474755231e1e.
Every row uses Fin(arity x); there is no uniform action-count bound. The source
generator adapter is a separate obligation. All path and clock theorems below
must pass strict compilation before being used.
-/
namespace DividingCompartments.FiniteBranching
open scoped BigOperators ENNReal
open Filter Topology
noncomputable section
attribute [local instance] Classical.propDecidable
variable {S : Type*}
/-- The terminal coordinate of a finite trajectory prefix. -/
theorem lastIndex_mem (n : ℕ) : n ∈ Finset.Iic n := Finset.mem_Iic.mpr le_rfl
/-- Shared measurability witness for both marked path constructions. -/
theorem lastState_measurable (S : Type*) [MeasurableSpace S] (n : ℕ) :
    Measurable (fun h : Finset.Iic n → S × ℝ => (h ⟨n, lastIndex_mem n⟩).1) :=
  measurable_fst.comp (measurable_pi_apply _)
/-- A finite-branching substochastic transition operator. -/
structure Transfer (S : Type*) where
  arity : S → ℕ
  weight : (x : S) → Fin (arity x) → ℝ
  next : (x : S) → Fin (arity x) → S
  weight_nonneg : ∀ x i, 0 ≤ weight x i
  row_le_one : ∀ x, ∑ i, weight x i ≤ 1
namespace Transfer
variable (T : Transfer S)
def apply (f : S → ℝ) (x : S) : ℝ := ∑ i, T.weight x i * f (T.next x i)
def iter (T : Transfer S) : ℕ → (S → ℝ) → S → ℝ
  | 0, f => f
  | n + 1, f => T.apply (T.iter n f)
theorem apply_mono {f g : S → ℝ} (h : ∀ x, f x ≤ g x) :
    ∀ x, T.apply f x ≤ T.apply g x := by
  intro x
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h _) (T.weight_nonneg x i)
theorem apply_nonneg {f : S → ℝ} (h : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ T.apply f x := by
  intro x
  exact Finset.sum_nonneg fun i _ => mul_nonneg (T.weight_nonneg x i) (h _)
theorem apply_add (f g : S → ℝ) :
    T.apply (fun x => f x + g x) = fun x => T.apply f x + T.apply g x := by
  funext x
  simp [apply, mul_add, Finset.sum_add_distrib]
theorem iter_mono {f g : S → ℝ} (h : ∀ x, f x ≤ g x) (n : ℕ) :
    ∀ x, T.iter n f x ≤ T.iter n g x := by
  induction n with
  | zero => exact h
  | succ n ih => exact T.apply_mono ih
theorem iter_nonneg {f : S → ℝ} (h : ∀ x, 0 ≤ f x) (n : ℕ) :
    ∀ x, 0 ≤ T.iter n f x := by
  induction n with
  | zero => exact h
  | succ n ih => exact T.apply_nonneg ih
theorem iter_add (f g : S → ℝ) (n : ℕ) :
    T.iter n (fun x => f x + g x) = fun x => T.iter n f x + T.iter n g x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iter, ih, apply_add]
theorem iter_succ_right (f : S → ℝ) (n : ℕ) :
    T.iter (n + 1) f = T.iter n (T.apply f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change T.apply (T.iter (n + 1) f) = T.apply (T.iter n (T.apply f))
    rw [ih]
theorem finite_reward_budget {V c : S → ℝ}
    (hstep : ∀ x, T.apply V x + c x ≤ V x) (N : ℕ) (x : S) :
    T.iter N V x + ∑ n ∈ Finset.range N, T.iter n c x ≤ V x := by
  induction N with
  | zero => simp [iter]
  | succ N ih =>
    have h := T.iter_mono hstep N x
    rw [T.iter_add, ← T.iter_succ_right] at h
    rw [Finset.sum_range_succ]
    linarith
end Transfer
/-- Literal finite channel rates; channels may share a successor. -/
structure FiniteRateModel (S : Type*) where
  arity : S → ℕ
  rate : (x : S) → Fin (arity x) → ℝ
  next : (x : S) → Fin (arity x) → S
  rate_nonneg : ∀ x i, 0 ≤ rate x i
  total_pos : ∀ x, 0 < ∑ i, rate x i
namespace FiniteRateModel
variable (M : FiniteRateModel S)
def total (x : S) : ℝ := ∑ i, M.rate x i
theorem total_positive (x : S) : 0 < M.total x := M.total_pos x
def jumpWeight (x : S) (i : Fin (M.arity x)) : ℝ := M.rate x i / M.total x
theorem jumpWeight_nonneg (x : S) (i : Fin (M.arity x)) : 0 ≤ M.jumpWeight x i :=
  div_nonneg (M.rate_nonneg x i) (M.total_positive x).le
theorem jumpWeight_sum (x : S) : ∑ i, M.jumpWeight x i = 1 := by
  simp only [jumpWeight, ← Finset.sum_div]
  change M.total x / M.total x = 1
  exact div_self (M.total_positive x).ne'
noncomputable def jumpPMF (x : S) : PMF (Fin (M.arity x)) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (M.jumpWeight x i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => M.jumpWeight_nonneg x i), M.jumpWeight_sum]
    simp)
def jumpTransfer : Transfer S where
  arity := M.arity
  weight := M.jumpWeight
  next := M.next
  weight_nonneg := M.jumpWeight_nonneg
  row_le_one x := (M.jumpWeight_sum x).le
def killedTransfer (K : Set S) : Transfer S := by
  classical
  exact {
    arity := M.arity
    weight := fun x i => if x ∈ K then 0 else M.jumpWeight x i
    next := M.next
    weight_nonneg := fun x i => by split_ifs; exact le_rfl; exact M.jumpWeight_nonneg x i
    row_le_one := fun x => by
      by_cases hx : x ∈ K
      · simp [hx]
      · simpa [hx] using (M.jumpWeight_sum x).le }
/-- The physical mean of the exponential holding time, paid only before the hit. -/
def holdingReward (K : Set S) (x : S) : ℝ := by
  classical
  exact if x ∈ K then 0 else 1 / M.total x
theorem holdingReward_nonneg (K : Set S) (x : S) : 0 ≤ M.holdingReward K x := by
  classical
  unfold holdingReward
  split_ifs
  · exact le_rfl
  · exact (one_div_pos.mpr (M.total_positive x)).le
section PathLaw
open MeasureTheory ProbabilityTheory Preorder
variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
def jumpStatePMF (x : S) : PMF S := (M.jumpPMF x).map (M.next x)
/-- The next count state and the holding time are conditionally independent.
The holding is stored with its destination, so coordinate `n+1` contains the
duration spent at the state in coordinate `n`. -/
def markedStepLaw (x : S) : Measure (S × ℝ) :=
  (M.jumpStatePMF x).toMeasure.prod (expMeasure (M.total x))
instance markedStepLaw_probability (x : S) : IsProbabilityMeasure (M.markedStepLaw x) := by
  have : IsProbabilityMeasure (expMeasure (M.total x)) :=
    isProbabilityMeasure_expMeasure (M.total_positive x)
  unfold markedStepLaw
  infer_instance
def markedKernel : Kernel S (S × ℝ) where
  toFun := M.markedStepLaw
  measurable' := measurable_of_countable _
instance markedKernel_markov : IsMarkovKernel M.markedKernel where
  isProbabilityMeasure x := M.markedStepLaw_probability x
def pathKernel (n : ℕ) : Kernel (Finset.Iic n → S × ℝ) (S × ℝ) :=
  M.markedKernel.comap (fun h => (h ⟨n, lastIndex_mem n⟩).1) (lastState_measurable S n)
instance pathKernel_markov (n : ℕ) : IsMarkovKernel (M.pathKernel n) := by
  unfold pathKernel
  infer_instance
/-- An actual probability measure on infinite state/holding trajectories,
constructed by Ionescu--Tulcea from the literal rates and exponential law. -/
def pathLaw (x : S) : Measure (ℕ → S × ℝ) :=
  Kernel.traj (X := fun _ : ℕ => S × ℝ) M.pathKernel 0 (fun _ => (x, (0 : ℝ)))
instance pathLaw_probability (x : S) : IsProbabilityMeasure (M.pathLaw x) := by
  unfold pathLaw
  infer_instance
/-- The full history/next-step law agrees with the constructed transition kernel. -/
theorem pathLaw_step (x : S) (n : ℕ) :
    (M.pathLaw x).map (frestrictLe n) ⊗ₘ M.pathKernel n =
      (M.pathLaw x).map (fun ω => (frestrictLe n ω, ω (n + 1))) := by
  change (Kernel.traj (X := fun _ : ℕ => S × ℝ) M.pathKernel 0 (fun _ => (x, (0 : ℝ)))).map (frestrictLe n) ⊗ₘ
    M.pathKernel n = _
  rw [Kernel.traj_map_frestrictLe_apply]
  exact Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)
theorem pathLaw_initial (x : S) :
    (M.pathLaw x).map (fun ω => ω 0) = Measure.dirac (x, (0 : ℝ)) := by
  have hh : (M.pathLaw x).map (frestrictLe 0) =
      Measure.dirac (fun _ : Finset.Iic 0 => (x, (0 : ℝ))) := by
    change (Kernel.traj (X := fun _ : ℕ => S × ℝ) M.pathKernel 0 (fun _ => (x, (0 : ℝ)))).map (frestrictLe 0) = _
    rw [Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]
  have hm : (fun ω : ℕ → S × ℝ => ω 0) =
      (fun h : Finset.Iic 0 → S × ℝ => h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘ frestrictLe 0 := rfl
  rw [hm, ← Measure.map_map (by fun_prop) (by fun_prop), hh]
  simp
omit [Countable S] [MeasurableSingletonClass S] in
theorem markedStepLaw_holding_marginal (x : S) :
    (M.markedStepLaw x).map Prod.snd = expMeasure (M.total x) := by
  have : IsProbabilityMeasure (expMeasure (M.total x)) :=
    isProbabilityMeasure_expMeasure (M.total_positive x)
  unfold markedStepLaw
  simp
omit [Countable S] [MeasurableSingletonClass S] in
theorem markedStepLaw_state_marginal (x : S) :
    (M.markedStepLaw x).map Prod.fst = (M.jumpStatePMF x).toMeasure := by
  have : IsProbabilityMeasure (expMeasure (M.total x)) :=
    isProbabilityMeasure_expMeasure (M.total_positive x)
  unfold markedStepLaw
  simp
end PathLaw
end FiniteRateModel
open MeasureTheory ProbabilityTheory Set
/-- The actual exponential holding law has the mean used in the Green series. -/
theorem exponential_holding_mean (r : ℝ) (hr : 0 < r) :
    (∫ t : ℝ, t ∂expMeasure r) = 1 / r := by
  change (∫ t : ℝ, t ∂volume.withDensity (exponentialPDF r)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF r)
    ((measurable_exponentialPDFReal r).ennreal_ofReal)
    (Filter.Eventually.of_forall fun t => by simp [exponentialPDF])]
  have hpdf : ∀ t : ℝ, (exponentialPDF r t).toReal =
      if 0 ≤ t then r * Real.exp (-(r * t)) else 0 := by
    intro t
    rw [exponentialPDF_eq, ENNReal.toReal_ofReal]
    split_ifs
    · exact mul_nonneg hr.le (Real.exp_pos _).le
    · exact le_rfl
  simp_rw [hpdf, smul_eq_mul]
  have heq : (fun t : ℝ => (if 0 ≤ t then r * Real.exp (-(r * t)) else 0) * t) =
      (Ici 0).indicator (fun t => r * (t * Real.exp (-(r * t)))) := by
    funext t
    by_cases ht : 0 ≤ t
    · simp [ht]; ring
    · simp [ht]
  rw [heq, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul]
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
  norm_num [Real.Gamma_two] at hg
  rw [hg]
  field_simp
theorem exponential_nonnegative_ae (r : ℝ) : ∀ᵐ t ∂expMeasure r, 0 ≤ t := by
  apply ae_iff.mpr
  simp only [not_le]
  change expMeasure r (Iio 0) = 0
  change (volume.withDensity (exponentialPDF r)) (Iio 0) = 0
  rw [withDensity_apply (exponentialPDF r) measurableSet_Iio]
  exact lintegral_exponentialPDF_of_nonpos le_rfl
namespace FiniteRateModel
open Preorder
variable (M : FiniteRateModel S)
variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
end FiniteRateModel
namespace FiniteRateModel
open Preorder
variable (M : FiniteRateModel S)
variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
end FiniteRateModel
namespace FiniteRateModel
variable (M : FiniteRateModel S)
variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
end FiniteRateModel
namespace Transfer
variable (T : Transfer S)
def applyENN (f : S → ℝ≥0∞) (x : S) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (T.weight x i) * f (T.next x i)
def iterENN (T : Transfer S) : ℕ → (S → ℝ≥0∞) → S → ℝ≥0∞
  | 0, f => f
  | n + 1, f => T.applyENN (T.iterENN n f)
theorem applyENN_ofReal (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) :
    T.applyENN (fun x => ENNReal.ofReal (f x)) = fun x => ENNReal.ofReal (T.apply f x) := by
  funext x
  unfold applyENN apply
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (T.weight_nonneg x i) (hf _))]
  congr 1
  funext i
  exact (ENNReal.ofReal_mul (T.weight_nonneg x i)).symm
theorem iterENN_ofReal (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    T.iterENN n (fun x => ENNReal.ofReal (f x)) = fun x => ENNReal.ofReal (T.iter n f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterENN, iter, ih]
    exact T.applyENN_ofReal _ (T.iter_nonneg hf n)
theorem iterENN_succ_right (f : S → ℝ≥0∞) (n : ℕ) :
    T.iterENN (n + 1) f = T.iterENN n (T.applyENN f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change T.applyENN (T.iterENN (n + 1) f) = T.applyENN (T.iterENN n (T.applyENN f))
    rw [ih]
end Transfer
def outsideFactor (K : Set S) (x : S) : ℝ≥0∞ := if x ∈ K then 0 else 1
def alivePrefix (K : Set S) (n : ℕ) (ω : ℕ → S × ℝ) : ℝ≥0∞ :=
  ∏ k : Fin n, outsideFactor K (ω k.val).1
def aliveHistory (K : Set S) (n : ℕ) (h : Finset.Iic n → S × ℝ) : ℝ≥0∞ :=
  ∏ k : Fin n, outsideFactor K (h ⟨k.val, Finset.mem_Iic.mpr (Nat.le_of_lt k.isLt)⟩).1
theorem alivePrefix_succ (K : Set S) (n : ℕ) (ω : ℕ → S × ℝ) :
    alivePrefix K (n + 1) ω = alivePrefix K n ω * outsideFactor K (ω n).1 := by
  unfold alivePrefix
  rw [Fin.prod_univ_castSucc]
  rfl
theorem aliveHistory_restrict (K : Set S) (n : ℕ) (ω : ℕ → S × ℝ) :
    aliveHistory K n (Preorder.frestrictLe n ω) = alivePrefix K n ω := rfl
theorem exponential_holding_lintegral (r : ℝ) (hr : 0 < r) :
    (∫⁻ t : ℝ, ENNReal.ofReal (max 0 t) ∂expMeasure r) = ENNReal.ofReal (1 / r) := by
  have hi : Integrable (fun t : ℝ => t) (expMeasure r) :=
    Integrable.of_integral_ne_zero (by rw [exponential_holding_mean r hr]; positivity)
  have he := ofReal_integral_eq_lintegral_ofReal hi (exponential_nonnegative_ae r)
  rw [exponential_holding_mean r hr] at he
  have hclip : ∀ t : ℝ, ENNReal.ofReal (max 0 t) = ENNReal.ofReal t := by
    intro t
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
    exact max_eq_right (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal t from bot_le)
  simp_rw [hclip]
  exact he.symm
namespace FiniteRateModel
open Preorder
variable (M : FiniteRateModel S)
variable [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
theorem jumpState_lintegral (x : S) (f : S → ℝ≥0∞) :
    (∫⁻ y, f y ∂(M.jumpStatePMF x).toMeasure) = M.jumpTransfer.applyENN f x := by
  let : MeasurableSpace (Fin (M.arity x)) := ⊤
  have hm : Measurable (M.next x) := measurable_of_finite _
  unfold jumpStatePMF
  rw [← PMF.toMeasure_map (M.next x) (M.jumpPMF x) hm,
    lintegral_map (measurable_of_countable f) hm, lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    jumpPMF, PMF.ofFintype_apply, Transfer.applyENN, jumpTransfer]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
theorem marked_state_lintegral (x : S) (f : S → ℝ≥0∞) :
    (∫⁻ z : S × ℝ, f z.1 ∂M.markedStepLaw x) = M.jumpTransfer.applyENN f x := by
  rw [← lintegral_map (measurable_of_countable f) measurable_fst, M.markedStepLaw_state_marginal,
    M.jumpState_lintegral]
omit [Countable S] [MeasurableSingletonClass S] in
theorem marked_holding_lintegral (x : S) :
    (∫⁻ z : S × ℝ, ENNReal.ofReal (max 0 z.2) ∂M.markedStepLaw x) =
      ENNReal.ofReal (1 / M.total x) := by
  have he := lintegral_map (μ := M.markedStepLaw x)
    (f := fun t : ℝ => ENNReal.ofReal (max 0 t))
    (g := fun z : S × ℝ => z.2) (by fun_prop) measurable_snd
  rw [M.markedStepLaw_holding_marginal] at he
  rw [← he]
  exact exponential_holding_lintegral _ (M.total_positive x)
omit [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem killed_applyENN (K : Set S) (f : S → ℝ≥0∞) (x : S) :
    (M.killedTransfer K).applyENN f x = outsideFactor K x * M.jumpTransfer.applyENN f x := by
  by_cases hx : x ∈ K
  · simp [Transfer.applyENN, killedTransfer, outsideFactor, jumpTransfer, hx]
  · simp [Transfer.applyENN, killedTransfer, outsideFactor, jumpTransfer, hx]
    rfl
theorem pathLaw_lintegral_step (x : S) (n : ℕ)
    (g : (Finset.Iic n → S × ℝ) × (S × ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, g (frestrictLe n ω, ω (n + 1)) ∂M.pathLaw x) =
      ∫⁻ h, ∫⁻ z, g (h, z) ∂M.pathKernel n h ∂(M.pathLaw x).map (frestrictLe n) := by
  calc
    _ = ∫⁻ w, g w ∂(M.pathLaw x).map (fun ω => (frestrictLe n ω, ω (n + 1))) :=
      (lintegral_map hg (by fun_prop)).symm
    _ = ∫⁻ w, g w ∂((M.pathLaw x).map (frestrictLe n) ⊗ₘ M.pathKernel n) := by rw [M.pathLaw_step]
    _ = _ := Measure.lintegral_compProd hg
/-- Identification of the entire killed transfer tree with the actual path law,
for arbitrary nonnegative observables, including unbounded ones. -/
theorem pathLaw_killed_lintegral (x : S) (K : Set S) (n : ℕ) (f : S → ℝ≥0∞) :
    (∫⁻ ω, alivePrefix K n ω * f (ω n).1 ∂M.pathLaw x) =
      (M.killedTransfer K).iterENN n f x := by
  induction n generalizing f with
  | zero =>
    simp only [alivePrefix, Fin.prod_univ_zero, one_mul, Transfer.iterENN]
    have he := lintegral_map (μ := M.pathLaw x) (f := fun z : S × ℝ => f z.1)
      ((measurable_of_countable f).comp measurable_fst) (measurable_pi_apply 0)
    rw [M.pathLaw_initial] at he
    simpa using he.symm
  | succ n ih =>
    have hout : Measurable (outsideFactor K) := measurable_of_countable _
    let g : (Finset.Iic n → S × ℝ) × (S × ℝ) → ℝ≥0∞ := fun w =>
      aliveHistory K n w.1 * outsideFactor K (w.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1 * f w.2.1
    have hg : Measurable g := by
      have hf := measurable_of_countable f
      unfold g aliveHistory
      fun_prop
    have hs := M.pathLaw_lintegral_step x n g hg
    have hinner : ∀ h, (∫⁻ z, g (h, z) ∂M.pathKernel n h) =
        aliveHistory K n h * (M.killedTransfer K).applyENN f (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1 := by
      intro h
      change (∫⁻ z : S × ℝ, (aliveHistory K n h *
        outsideFactor K (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1) * f z.1
        ∂M.markedStepLaw (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1) = _
      rw [lintegral_const_mul (μ := M.markedStepLaw (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1)
        (f := fun z : S × ℝ => f z.1)
        (aliveHistory K n h * outsideFactor K (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1)
        ((measurable_of_countable f).comp measurable_fst),
        M.marked_state_lintegral, M.killed_applyENN]
      exact mul_assoc _ _ _
    simp_rw [hinner] at hs
    have heq : (fun ω : ℕ → S × ℝ => g (frestrictLe n ω, ω (n + 1))) =
        (fun ω => alivePrefix K (n + 1) ω * f (ω (n + 1)).1) := by
      funext ω
      dsimp [g]
      rw [aliveHistory_restrict, alivePrefix_succ]
    rw [heq] at hs
    have hm : Measurable (fun h : Finset.Iic n → S × ℝ => aliveHistory K n h *
        (M.killedTransfer K).applyENN f (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1) := by
      have hf := measurable_of_countable ((M.killedTransfer K).applyENN f)
      unfold aliveHistory
      fun_prop
    rw [lintegral_map hm (by fun_prop)] at hs
    simp only [aliveHistory_restrict, frestrictLe_apply] at hs
    rw [hs, ih, Transfer.iterENN_succ_right]
theorem pathLaw_clock_term (x : S) (K : Set S) (n : ℕ) :
    (∫⁻ ω, alivePrefix K (n + 1) ω * ENNReal.ofReal (max 0 (ω (n + 1)).2) ∂M.pathLaw x) =
      ENNReal.ofReal ((M.killedTransfer K).iter n (M.holdingReward K) x) := by
  have hout : Measurable (outsideFactor K) := measurable_of_countable _
  let g : (Finset.Iic n → S × ℝ) × (S × ℝ) → ℝ≥0∞ := fun w =>
    aliveHistory K n w.1 * outsideFactor K (w.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1 *
      ENNReal.ofReal (max 0 w.2.2)
  have hg : Measurable g := by unfold g aliveHistory; fun_prop
  have hs := M.pathLaw_lintegral_step x n g hg
  have hinner : ∀ h, (∫⁻ z, g (h, z) ∂M.pathKernel n h) = aliveHistory K n h *
      ENNReal.ofReal (M.holdingReward K (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1) := by
    intro h
    change (∫⁻ z : S × ℝ, (aliveHistory K n h *
      outsideFactor K (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1) * ENNReal.ofReal (max 0 z.2)
      ∂M.markedStepLaw (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1) = _
    rw [lintegral_const_mul _ (by fun_prop), M.marked_holding_lintegral, mul_assoc]
    congr 1
    by_cases hh : (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1 ∈ K <;> simp [outsideFactor, holdingReward, hh]
  simp_rw [hinner] at hs
  have heq : (fun ω : ℕ → S × ℝ => g (frestrictLe n ω, ω (n + 1))) =
      (fun ω => alivePrefix K (n + 1) ω * ENNReal.ofReal (max 0 (ω (n + 1)).2)) := by
    funext ω
    dsimp [g]
    rw [aliveHistory_restrict, alivePrefix_succ]
  rw [heq] at hs
  have hm : Measurable (fun h : Finset.Iic n → S × ℝ => aliveHistory K n h *
      ENNReal.ofReal (M.holdingReward K (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1)) := by
    have hf := measurable_of_countable (M.holdingReward K)
    unfold aliveHistory
    fun_prop
  rw [lintegral_map hm (by fun_prop)] at hs
  simp only [aliveHistory_restrict, frestrictLe_apply] at hs
  rw [hs]
  calc
    _ = (M.killedTransfer K).iterENN n
        (fun y => ENNReal.ofReal (M.holdingReward K y)) x :=
      M.pathLaw_killed_lintegral x K n (fun y => ENNReal.ofReal (M.holdingReward K y))
    _ = _ := congrFun ((M.killedTransfer K).iterENN_ofReal
      (M.holdingReward K) (M.holdingReward_nonneg K) n) x
end FiniteRateModel
end
end DividingCompartments.FiniteBranching
