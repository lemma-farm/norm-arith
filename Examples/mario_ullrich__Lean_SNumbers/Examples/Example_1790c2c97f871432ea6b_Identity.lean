/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Examples.mario_ullrich__Lean_SNumbers.Dependencies.vfe65697966c2.SNumbers.Approximation
import Examples.mario_ullrich__Lean_SNumbers.Dependencies.vfe65697966c2.SNumbers.Examples.ExHelpers
import Mathlib.Analysis.MeanInequalities
/-!
# Example: s-numbers of the identity embedding `ℓ^q_m → ℓ^p_m`

The identity map `id : ℓ^q_m → ℓ^p_m` between finite-dimensional sequence spaces
with **different** exponents (`p ≤ q`). Its s-numbers are a classical example
(Pietsch, *Eigenvalues and s-numbers*, §11.11).

This is the **unit-diagonal** case of the diagonal operators, and it is kept
self-contained: it depends only on the core s-number theory and the shared
helpers, not on any diagonal machinery. (The general diagonal operator, for all
pairs of exponents, is `SNumbers.Examples.DiagonalMatrices`, which builds on
this file.)

This file develops the case `1 ≤ p ≤ q < ∞`:

* `piLp_norm_restrict_le` / `piLp_norm_le_card_rpow_mul` — the cross-exponent
  norm comparison `‖f‖_p ≤ (card s)^{1/p-1/q} · ‖f‖_q` (via the
  power-mean inequality `Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg`);
* `idEmbed` and `norm_idEmbed` — the embedding and its operator norm
  `‖id‖ = m^{1/p-1/q}` (sharp, attained at the all-ones vector);
* `approximationNumber_idEmbed_le` — the upper bound `aₙ(id) ≤ (m-n)^{1/p-1/q}`
  (hence `sₙ(id) ≤ (m-n)^{1/p-1/q}` for every s-number, via `sₙ ≤ aₙ`);
* `approximationNumber_idEmbed_eq` — the exact value `aₙ(id) = (m-n)^{1/p-1/q}`,
  via the geometric input `exists_norm_ratio_ge_idEmbed` (the classical
  Gelfand-width lower bound, Pietsch §11.11): every subspace of dimension `≥ m-n`
  contains a vector with `p`/`q`-norm ratio `≥ (m-n)^{1/p-1/q}`, proved from the
  flatness / extreme-point lemma `exists_flat_vector` of
  `SNumbers.Examples.ExHelpers`.
-/
universe u
open scoped ENNReal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
/-- **Cross-exponent norm comparison, restricted to a finite support.** For
`1 ≤ p ≤ q` (with `q ≠ ∞`) and `f` supported on a finite set `s`,
`‖f‖_p ≤ (card s)^{1/p - 1/q} · ‖f‖_q`. The power-mean inequality, applied over
the support `s`. -/
lemma piLp_norm_restrict_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) (s : Finset (Fin m)) (f : Fin m → 𝕜)
    (hf : ∀ i ∉ s, f i = 0) :
    ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜))‖
      ≤ (s.card : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
        ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜))‖ := by
  have hpf : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hP : 0 < p.toReal := toReal_pos_of_ne_top hpf
  have hQ : 0 < q.toReal := toReal_pos_of_ne_top hq
  have hPQ : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  set P := p.toReal
  set Q := q.toReal
  rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hQ]
  -- Restrict both sums to the support `s` (the other terms vanish).
  rw [← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
        rw [show (WithLp.toLp p f) i = f i from rfl, hf i hi, norm_zero, Real.zero_rpow hP.ne']),
    ← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
        rw [show (WithLp.toLp q f) i = f i from rfl, hf i hi, norm_zero, Real.zero_rpow hQ.ne'])]
  set SP : ℝ := ∑ i ∈ s, ‖(WithLp.toLp p f) i‖ ^ P with hSP_def
  set SQ : ℝ := ∑ i ∈ s, ‖(WithLp.toLp q f) i‖ ^ Q with hSQ_def
  have hSP : 0 ≤ SP := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hSQ : 0 ≤ SQ := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hr : 1 ≤ Q / P := (one_le_div hP).mpr hPQ
  have hPQe : P * (Q / P) = Q := by field_simp
  -- Power-mean over `s`: `SP^(Q/P) ≤ (card s)^(Q/P - 1) * SQ`.
  have key : SP ^ (Q / P) ≤ (s.card : ℝ) ^ (Q / P - 1) * SQ := by
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := s) (f := fun i => ‖(WithLp.toLp p f) i‖ ^ P)
      hr (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
    rw [hSP_def, hSQ_def]
    refine h.trans_eq ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Real.rpow_mul (norm_nonneg _), hPQe]
  -- Raise to the power `1/Q` and simplify the exponents.
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hSP _) key
    (le_of_lt (by positivity : (0 : ℝ) < 1 / Q))
  rw [Real.mul_rpow (by positivity) hSQ, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (s.card:ℝ)),
    ← Real.rpow_mul hSP] at h2
  have e1 : Q / P * (1 / Q) = 1 / P := by field_simp
  have e2 : (Q / P - 1) * (1 / Q) = 1 / P - 1 / Q := by field_simp
  rwa [e1, e2] at h2
noncomputable def idEmbed (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    PiLp q (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (WithLp.ofLp x)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }
@[simp] lemma idEmbed_apply {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (x : PiLp q (fun _ : Fin m => 𝕜)) (i : Fin m) : (idEmbed p q x) i = x i := rfl
private lemma card_filter_ge (n : ℕ) (hn : n ≤ m) :
    (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < n)).card = m - n := by
  have hlt : (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n)).card = n := by
    rw [show (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n))
          = Finset.univ.image (Fin.castLE hn) from ?_,
      Finset.card_image_of_injective _ (Fin.castLE_injective hn), Finset.card_univ,
      Fintype.card_fin]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi; exact ⟨⟨(i : ℕ), hi⟩, by simp⟩
    · rintro ⟨j, rfl⟩; simp only [Fin.val_castLE]; exact j.isLt
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (p := fun i : Fin m => (i : ℕ) < n)
  rw [hlt, Finset.card_univ, Fintype.card_fin] at hsum
  omega
/-- **Upper bound.** The `n`-th approximation number of `id : ℓ^q_m → ℓ^p_m`
(`p ≤ q`) is at most `(m-n)^{1/p-1/q}`. -/
theorem approximationNumber_idEmbed_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n ≤ m) :
    approximationNumber (idEmbed (𝕜 := 𝕜) (m := m) p q) n
      ≤ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by
  -- The rank-`≤ n` approximant `L = id ∘ Pₙ`, written `B ∘ id_{ℓ^q_n} ∘ A`.
  set A : PiLp q (fun _ : Fin m => 𝕜) →L[𝕜] PiLp q (fun _ : Fin n => 𝕜) :=
    projFin hn with hA
  set B : PiLp q (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
    (idEmbed p q).comp padFin with hB
  set L := B.comp ((ContinuousLinearMap.id 𝕜 (PiLp q (fun _ : Fin n => 𝕜))).comp A) with hL
  have hLrank : L.rank ≤ (n : Cardinal) :=
    (ContinuousLinearMap.rank_comp_comp_le A _ B).trans_eq (rank_id_piLp n)
  -- The residual zeros the first `n` coordinates.
  have hres : ∀ x : PiLp q (fun _ : Fin m => 𝕜), (idEmbed (𝕜 := 𝕜) (m := m) p q - L) x
      = WithLp.toLp p (fun i : Fin m => if (i : ℕ) < n then 0 else (WithLp.ofLp x) i) := by
    intro x; ext i
    simp only [hL, hA, hB, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, PiLp.sub_apply, idEmbed_apply]
    rw [padFin_projFin_apply]
    by_cases hi : (i : ℕ) < n <;> simp [hi]
  have hbound : ‖idEmbed (𝕜 := 𝕜) (m := m) p q - L‖
      ≤ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by
    refine opNorm_le_bound _ (by positivity) fun x => ?_
    rw [hres x]
    set g : Fin m → 𝕜 := fun i => if (i : ℕ) < n then 0 else (WithLp.ofLp x) i with hg
    have hsupp : ∀ i ∉ Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < n), g i = 0 := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      simp [hg, hi]
    have hmono : ‖(WithLp.toLp q g : PiLp q (fun _ : Fin m => 𝕜))‖ ≤ ‖x‖ :=
      piLp_norm_mono fun i => by
        simp only [hg]; split_ifs with h <;> simp
    calc ‖(WithLp.toLp p g : PiLp p (fun _ : Fin m => 𝕜))‖
        ≤ ((Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < n)).card : ℝ)
            ^ (1 / p.toReal - 1 / q.toReal) * ‖(WithLp.toLp q g : PiLp q (fun _ : Fin m => 𝕜))‖ :=
          piLp_norm_restrict_le hpq hq _ g hsupp
      _ = ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal)
            * ‖(WithLp.toLp q g : PiLp q (fun _ : Fin m => 𝕜))‖ := by rw [card_filter_ge n hn]
      _ ≤ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖x‖ := by gcongr
  exact (approximationNumber_le_norm_sub hLrank).trans hbound
/-! ## Stage 3 — the lower bound `(m-n)^{1/p-1/q} ≤ aₙ(id)`

For any rank-`≤ n` operator `L`, its kernel has dimension `≥ m - n`, and
`(id - L)` agrees with `id` there. The crux is a **classical geometric fact**
(Pietsch, *Eigenvalues and s-numbers*, §11.11; the Gelfand-width lower bound):
every subspace of dimension `≥ m - n` contains a vector whose `p`-norm is at
least `(m-n)^{1/p-1/q}` times its `q`-norm. It comes from the flatness lemma
`exists_flat_vector` (an extreme-point argument, in
`SNumbers.Examples.ExHelpers`) combined with the interpolation estimate
`norm_ratio_of_flat` below. -/
