/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/HaarSpectrum.lean
-/
/-
# The spectral measure of a Haar-distributed unitary (density stage E6.5b)

Let `E` be self-adjoint with `spectrum E ⊆ [0, 2π]`, so that `u := e^{iE}` is a unitary
with `E = −i Log u`, and let `ζ` be a vector for which the "moments" vanish,
`⟪ζ, e^{ikE} ζ⟫ = 0` for every nonzero integer `k` (HJX Lemma 2.2: this is what
`λ(2^{-n})` does to `Ω̂` in the crossed product, where `e^{ikE} = λ(k2^{-n})`).

The only consequence needed downstream is a **uniform tail estimate for the spectral
measure `ν = ν_{E,ζ}` near the branch cut**: for `0 < δ ≤ 1`,

    ν((δ, 2π−δ)ᶜ) ≤ 4 ‖ζ‖² δ ,

with a constant that does not depend on `E`. It follows from the Fejér majorant
`Q_N := 4(N+1)^{-2}|∑_{k≤N} e^{ikθ}|²`: this is a nonnegative trigonometric polynomial
which is `≥ 1` on `|θ| ≤ 1/N` (because `cos x ≥ 1 − x²/2 ≥ 1/2` there) and whose
`ν`-integral is `4‖ζ‖²/(N+1)` (because the vectors `e^{ikE}ζ` are orthonormal up to the
factor `‖ζ‖`).

Combined with `‖·‖`-approximation of the identity function by trigonometric polynomials
away from the cut, this gives `‖Eζ − P(u)ζ‖` small with `P` independent of `E`.
-/
module
public import Mathlib
public import Examples.vidick__MIPRE_formalization.Dependencies.v9048ba8ac1bf.MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.CentralExp
public import Examples.vidick__MIPRE_formalization.Dependencies.v9048ba8ac1bf.MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.UnitaryLog
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true
@[expose] public section
namespace CommutingRepetition
namespace VN
namespace Modular
open scoped InnerProductSpace ComplexConjugate Real
open Filter Topology MeasureTheory BorelCalc
set_option linter.unusedSectionVars false
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
/-! ## Finite sums in the complex Borel calculus -/
theorem cbdd_finset_sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → ℂ} (hG : ∀ i, CBdd (G i)) :
    CBdd fun t => ∑ i ∈ s, G i t := by
  classical
  induction s using Finset.induction with
  | empty => simpa using CBdd.const (0 : ℂ)
  | insert a s ha ih =>
      have e : (fun t => ∑ i ∈ insert a s, G i t) = G a + fun t => ∑ i ∈ s, G i t := by
        funext t; rw [Finset.sum_insert ha]; rfl
      rw [e]; exact (hG a).add ih
theorem cbfc_finset_sum (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) {ι : Type*} (s : Finset ι)
    {G : ι → ℝ → ℂ} (hG : ∀ i, CBdd (G i)) :
    cbfc E hE (fun t => ∑ i ∈ s, G i t) = ∑ i ∈ s, cbfc E hE (G i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [cbfc_const E hE (0 : ℂ)]
  | insert a s ha ih =>
      have e : (fun t => ∑ i ∈ insert a s, G i t) = G a + fun t => ∑ i ∈ s, G i t := by
        funext t; rw [Finset.sum_insert ha]; rfl
      rw [e, cbfc_add E hE (hG a) (cbdd_finset_sum s hG), ih, Finset.sum_insert ha]
/-! ## The Dirichlet kernel and the Fejér majorant -/
/-- `D_N(θ) = ∑_{k ≤ N} e^{ikθ}`. -/
noncomputable def dirK (N : ℕ) (t : ℝ) : ℂ := ∑ k ∈ Finset.range (N + 1), eitf (k : ℝ) t
theorem cbdd_dirK (N : ℕ) : CBdd (dirK N) :=
  cbdd_finset_sum _ fun k => cbdd_eitf (k : ℝ)
theorem cbfc_dirK (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) (N : ℕ) :
    cbfc E hE (dirK N) = ∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ) :=
  cbfc_finset_sum E hE _ fun k => cbdd_eitf (k : ℝ)
theorem re_eitf (t l : ℝ) : (eitf t l).re = Real.cos (t * l) := by
  unfold eitf; exact Complex.exp_ofReal_mul_I_re _
/-- On `|t| ≤ 1/N` the Dirichlet kernel is at least `(N+1)/2`. -/
theorem norm_dirK_ge {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : |t| ≤ 1 / N) :
    ((N : ℝ) + 1) / 2 ≤ ‖dirK N t‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcos : ∀ k ∈ Finset.range (N + 1), (1 : ℝ) / 2 ≤ Real.cos ((k : ℝ) * t) := by
    intro k hk
    have hkN : (k : ℝ) ≤ N := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : |(k : ℝ) * t| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      calc (k : ℝ) * |t| ≤ (N : ℝ) * (1 / N) :=
            mul_le_mul hkN ht (abs_nonneg t) (Nat.cast_nonneg N)
        _ = 1 := by field_simp
    have h2 : ((k : ℝ) * t) ^ 2 ≤ 1 := by
      nlinarith [(abs_le.mp h1).1, (abs_le.mp h1).2]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := (k : ℝ) * t)]
  have hre : ((N : ℝ) + 1) / 2 ≤ (dirK N t).re := by
    have e : (dirK N t).re = ∑ k ∈ Finset.range (N + 1), Real.cos ((k : ℝ) * t) := by
      rw [dirK, Complex.re_sum]
      exact Finset.sum_congr rfl fun k _ => re_eitf _ _
    rw [e]
    calc ((N : ℝ) + 1) / 2 = ∑ _k ∈ Finset.range (N + 1), (1 : ℝ) / 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := Finset.sum_le_sum hcos
  exact hre.trans (Complex.re_le_norm _)
/-- The Fejér majorant `Q_N = 4(N+1)^{-2}|D_N|²`. -/
noncomputable def fejerMaj (N : ℕ) (t : ℝ) : ℝ := 4 / ((N : ℝ) + 1) ^ 2 * ‖dirK N t‖ ^ 2
theorem bdd_fejerMaj (N : ℕ) : Bdd (fejerMaj N) := by
  have h := ((cbdd_dirK (N := N)).norm_sq).const_mul (4 / ((N : ℝ) + 1) ^ 2)
  exact h
theorem fejerMaj_nonneg (N : ℕ) (t : ℝ) : 0 ≤ fejerMaj N t := by
  unfold fejerMaj; positivity
theorem one_le_fejerMaj {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : |t| ≤ 1 / N) :
    1 ≤ fejerMaj N t := by
  have h := norm_dirK_ge hN ht
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h2 : (((N : ℝ) + 1) / 2) ^ 2 ≤ ‖dirK N t‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  have key : 4 / ((N : ℝ) + 1) ^ 2 * (((N : ℝ) + 1) / 2) ^ 2 = 1 := by field_simp; ring
  rw [fejerMaj]
  calc (1 : ℝ) = 4 / ((N : ℝ) + 1) ^ 2 * (((N : ℝ) + 1) / 2) ^ 2 := key.symm
    _ ≤ 4 / ((N : ℝ) + 1) ^ 2 * ‖dirK N t‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
theorem eitf_add_two_pi (k : ℕ) (t : ℝ) : eitf (k : ℝ) (t + 2 * π) = eitf (k : ℝ) t := by
  unfold eitf
  have e : (((k : ℝ) * (t + 2 * π) : ℝ) : ℂ) * Complex.I
      = (((k : ℝ) * t : ℝ) : ℂ) * Complex.I + (k : ℤ) * (2 * π * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem dirK_add_two_pi (N : ℕ) (t : ℝ) : dirK N (t + 2 * π) = dirK N t :=
  Finset.sum_congr rfl fun k _ => eitf_add_two_pi k t
theorem fejerMaj_add_two_pi (N : ℕ) (t : ℝ) : fejerMaj N (t + 2 * π) = fejerMaj N t := by
  rw [fejerMaj, fejerMaj, dirK_add_two_pi]
/-! ## Haar-distributed vectors -/
section Haar
variable {E : 𝓗 →L[ℂ] 𝓗} (hE : IsSelfAdjoint E) (ζ : 𝓗)
/-- `ζ` is **Haar distributed** for `E`: the Fourier moments `⟪ζ, e^{ikE}ζ⟫` vanish for
every nonzero integer `k` (HJX Lemma 2.2). -/
def IsHaarVec : Prop := ∀ k : ℤ, k ≠ 0 → ⟪ζ, eit E hE (k : ℝ) ζ⟫_ℂ = 0
theorem inner_eit_eit (h : IsHaarVec hE ζ) (j k : ℤ) :
    ⟪eit E hE (j : ℝ) ζ, eit E hE (k : ℝ) ζ⟫_ℂ = if j = k then ⟪ζ, ζ⟫_ℂ else 0 := by
  have e : ⟪eit E hE (j : ℝ) ζ, eit E hE (k : ℝ) ζ⟫_ℂ
      = ⟪ζ, eit E hE ((k - j : ℤ) : ℝ) ζ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      eit_star hE, ← mul_apply_eq_comp, ← eit_add hE]
    congr 2
    push_cast
    ring
  rw [e]
  by_cases hjk : j = k
  · rw [if_pos hjk, hjk, sub_self]
    simp only [Int.cast_zero]
    rw [eit_zero hE, one_apply_eq_self]
  · rw [if_neg hjk]
    exact h _ (sub_ne_zero.mpr fun hh => hjk hh.symm)
theorem inner_eit_eit_nat (h : IsHaarVec hE ζ) (j k : ℕ) :
    ⟪eit E hE (j : ℝ) ζ, eit E hE (k : ℝ) ζ⟫_ℂ = if j = k then ⟪ζ, ζ⟫_ℂ else 0 := by
  have e1 : ((j : ℕ) : ℝ) = (((j : ℕ) : ℤ) : ℝ) := by push_cast; ring
  have e2 : ((k : ℕ) : ℝ) = (((k : ℕ) : ℤ) : ℝ) := by push_cast; ring
  rw [e1, e2, inner_eit_eit hE ζ h]
  by_cases hjk : j = k
  · rw [if_pos hjk, if_pos (by exact_mod_cast hjk)]
  · rw [if_neg hjk, if_neg (by exact_mod_cast hjk)]
theorem norm_sum_eit_sq (h : IsHaarVec hE ζ) (N : ℕ) :
    ‖(∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ)) ζ‖ ^ 2 = ((N : ℝ) + 1) * ‖ζ‖ ^ 2 := by
  have happ : (∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ)) ζ
      = ∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ) ζ := by
    simp
  set v := ∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ) ζ with hv
  have key : ⟪v, v⟫_ℂ = ((((N : ℝ) + 1 : ℝ)) : ℂ) * ⟪ζ, ζ⟫_ℂ := by
    calc ⟪v, v⟫_ℂ = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
            ⟪eit E hE (j : ℝ) ζ, eit E hE (k : ℝ) ζ⟫_ℂ := by
          rw [hv, sum_inner]
          exact Finset.sum_congr rfl fun j _ => inner_sum _ _ _
      _ = ∑ _j ∈ Finset.range (N + 1), ⟪ζ, ζ⟫_ℂ := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.sum_congr rfl fun k _ => inner_eit_eit_nat hE ζ h j k,
            Finset.sum_ite_eq (Finset.range (N + 1)) j fun _ => ⟪ζ, ζ⟫_ℂ, if_pos hj]
      _ = ((((N : ℝ) + 1 : ℝ)) : ℂ) * ⟪ζ, ζ⟫_ℂ := by
          rw [Finset.sum_const, Finset.card_range]
          push_cast
          ring
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul] at hre
  rw [happ, ← inner_self_eq_norm_sq (𝕜 := ℂ) v, ← inner_self_eq_norm_sq (𝕜 := ℂ) ζ]
  exact hre
theorem integral_fejerMaj (h : IsHaarVec hE ζ) (N : ℕ) :
    ∫ t, fejerMaj N t ∂(ν E hE ζ) = 4 * ‖ζ‖ ^ 2 / ((N : ℝ) + 1) := by
  have h1 : ∫ t, ‖dirK N t‖ ^ 2 ∂(ν E hE ζ) = ((N : ℝ) + 1) * ‖ζ‖ ^ 2 := by
    rw [← norm_sq_cbfc E hE (cbdd_dirK (N := N)) ζ, cbfc_dirK, norm_sum_eit_sq hE ζ h N]
  have h2 : ∫ t, fejerMaj N t ∂(ν E hE ζ)
      = 4 / ((N : ℝ) + 1) ^ 2 * ∫ t, ‖dirK N t‖ ^ 2 ∂(ν E hE ζ) := by
    rw [← integral_const_mul]
    rfl
  rw [h2, h1]
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  field_simp
/-- The spectral measure is concentrated on `[0, 2π]`. -/
theorem ν_compl_Icc (hspec : spectrum ℝ E ⊆ Set.Icc 0 (2 * π)) :
    ν E hE ζ (Set.Icc (0 : ℝ) (2 * π))ᶜ = 0 :=
  measure_mono_null (Set.compl_subset_compl.mpr hspec) (ν_compl_spectrum E hE ζ)
/-- **The uniform tail estimate** near the branch cut: `ν((δ, 2π−δ)ᶜ) ≤ 4‖ζ‖²δ`, with a
constant independent of `E`. -/
theorem measureReal_compl_Icc_le (h : IsHaarVec hE ζ)
    (hspec : spectrum ℝ E ⊆ Set.Icc 0 (2 * π)) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (ν E hE ζ).real (Set.Icc δ (2 * π - δ))ᶜ ≤ 4 * ‖ζ‖ ^ 2 * δ := by
  set N := ⌊1 / δ⌋₊ with hNdef
  have hinv : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hinv)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hδN : δ ≤ 1 / N := by
    have h1 : (N : ℝ) ≤ 1 / δ := Nat.floor_le (le_trans zero_le_one hinv)
    rw [le_div_iff₀ hN0]
    rw [le_div_iff₀ hδ0] at h1
    linarith
  have hNδ : 4 * ‖ζ‖ ^ 2 / ((N : ℝ) + 1) ≤ 4 * ‖ζ‖ ^ 2 * δ := by
    have h1 : (1 : ℝ) / δ < (N : ℝ) + 1 := Nat.lt_floor_add_one (1 / δ)
    have h2 : (1 : ℝ) / ((N : ℝ) + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ0] at h1
      linarith
    calc 4 * ‖ζ‖ ^ 2 / ((N : ℝ) + 1) = 4 * ‖ζ‖ ^ 2 * (1 / ((N : ℝ) + 1)) := by ring
      _ ≤ 4 * ‖ζ‖ ^ 2 * δ := by
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- the a.e. pointwise majorization
  have hae : ∀ᵐ t ∂(ν E hE ζ),
      (Set.Icc δ (2 * π - δ))ᶜ.indicator (1 : ℝ → ℝ) t ≤ fejerMaj N t := by
    have hmem : ∀ᵐ t ∂(ν E hE ζ), t ∈ Set.Icc (0 : ℝ) (2 * π) :=
      MeasureTheory.mem_ae_iff.mpr (ν_compl_Icc hE ζ hspec)
    filter_upwards [hmem] with t ht
    by_cases hin : t ∈ Set.Icc δ (2 * π - δ)
    · rw [Set.indicator_of_notMem (by simpa using hin)]
      exact fejerMaj_nonneg N t
    · rw [Set.indicator_of_mem (Set.mem_compl hin), Pi.one_apply]
      simp only [Set.mem_Icc, not_and_or, not_le] at hin
      rcases hin with hlt | hgt
      · refine one_le_fejerMaj hN1 ?_
        rw [abs_of_nonneg ht.1]
        exact le_trans hlt.le hδN
      · have e := fejerMaj_add_two_pi N (t - 2 * π)
        rw [sub_add_cancel] at e
        rw [e]
        refine one_le_fejerMaj hN1 ?_
        rw [abs_of_nonpos (by linarith [ht.2])]
        have : 2 * π - t < δ := by linarith
        exact le_trans (by linarith) hδN
  calc (ν E hE ζ).real (Set.Icc δ (2 * π - δ))ᶜ
      = ∫ t, (Set.Icc δ (2 * π - δ))ᶜ.indicator (1 : ℝ → ℝ) t ∂(ν E hE ζ) :=
        (integral_indicator_one measurableSet_Icc.compl).symm
    _ ≤ ∫ t, fejerMaj N t ∂(ν E hE ζ) :=
        integral_mono_ae ((Bdd.indicator measurableSet_Icc.compl).integrable _)
          ((bdd_fejerMaj N).integrable _) hae
    _ = 4 * ‖ζ‖ ^ 2 / ((N : ℝ) + 1) := integral_fejerMaj hE ζ h N
    _ ≤ 4 * ‖ζ‖ ^ 2 * δ := hNδ
/-! ## From the tail estimate to an operator estimate -/
end Haar
section Trig
section RampFacts
end RampFacts
end Trig
section ExpSeries
end ExpSeries
end Modular
end VN
end CommutingRepetition
end
