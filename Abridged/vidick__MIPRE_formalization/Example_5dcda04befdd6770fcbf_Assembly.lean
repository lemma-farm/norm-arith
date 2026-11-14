module

public import Mathlib

-- ==== Examples.vidick__MIPRE_formalization.Dependencies.v080721d0fac7.MIPRE.Background.Orthonormalization.Orthogonalization.PhiNorm ====
public section
/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/PhiNorm.lean
-/
/-
# The seminorm `‖·‖_φ` of a positive functional, and its triangle inequality

For a positive linear functional `φ` on `H →L[ℂ] H` the paper
(M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*,
arXiv:2103.14126v2, Section 1) writes `‖b‖_φ = √(φ (b* b))`, and the assembly
step (`PLAN.md` §1, step **F3**) applies its triangle inequality to *tuples*
`(b_i)_{i ∈ ι}`, i.e. to the norm of `PiLp 2` over the GNS space:

`‖(b_i)‖_φ = √(∑ i, φ (b_i* b_i))`.

This file defines the square of that quantity, `phiNormSq φ b`, as a real
number, and proves what the three-term estimate of step **F3** needs:

* `norm_map_star_mul_le` / `sq_norm_map_star_mul_le`: the Cauchy–Schwarz
  inequality for a positive functional, obtained from Mathlib's GNS
  construction (`PositiveLinearMap.PreGNS`), which turns `x, y ↦ φ (x* y)`
  into an honest (semi-definite) inner product;
* `phiNormSq_nonneg`, `phiNormSq_add_le`: the triangle inequality
  `√(phiNormSq φ (b + c)) ≤ √(phiNormSq φ b) + √(phiNormSq φ c)`;
* `phiNormSq_add_add_lt`: the three-term corollary
  `phiNormSq φ b ≤ ε`, `phiNormSq φ c ≤ ε`, `phiNormSq φ d < ε`
  imply `phiNormSq φ (b + c + d) < 9 ε`, which is exactly the shape in which
  the constant `9` of Theorem 1.2 is produced.

Positivity of `φ` is kept as a bare hypothesis
`hφ : ∀ z, 0 ≤ φ (star z * z)` (with the `ComplexOrder` order on `ℂ`) rather
than bundled, so that the lemmas apply verbatim to the functional underlying a
normal state.
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true
@[expose] public section
namespace Orthogonalization
open scoped ComplexOrder BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-! ### Cauchy–Schwarz for a positive functional -/
section CauchySchwarz
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}

end CauchySchwarz
/-! ### The squared seminorm of a tuple -/
/-- The square of the seminorm `‖(b_i)‖_φ = √(∑ i, φ (b_i* b_i))` of a tuple of
operators, as a *real* number (the values `φ (b_i* b_i)` are real by
positivity of `φ`; no positivity hypothesis is needed for the definition since
we take real parts). -/
noncomputable def phiNormSq (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) {ι : Type*} [Fintype ι]
    (b : ι → H →L[ℂ] H) : ℝ :=
  ∑ i, (φ (star (b i) * b i)).re
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} {ι : Type*} [Fintype ι]

end Orthogonalization
end

end

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_5dcda04befdd6770fcbf_Assembly ====
/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Assembly.lean
-/
/-
# Assembly of the orthogonalized PVM (step **F3**)

This file carries out the last step of the proof of Theorem 1.2 in the finite
case (M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*,
arXiv:2103.14126v2, Section 3, lines 247–271 of `manuscript/arXiv2103.14126v2.tex`;
`PLAN.md` §1, step **F3**).

The input is the isometry data of `Orthogonalization/IsometryData.lean`: reading
the partial isometry `u ∈ M_n(M)` of Lemma 3.2 block by block gives operators
`w_i = (e_{1i} ⊗ 1) u` on `H` satisfying

* (W1) `∑ i, w_i* w_i = 1`,
* (W2) `w_i w_j* = δ_{ij} q_i`,
* (W3) `w_i √y = q_i √a_i` where `y = ∑ j, q_j a_j`.

The paper's PVM is `p_i = u* t_i u` with `t_i = e_{ii} ⊗ q_i`, which in this
block notation is exactly `p_i = w_i* w_i` (`assembledPVM`). We prove:

* `IsometryData.q_mul_w`: `q_i w_i = w_i`;
* `assembledPVM_isStarProjection`, `sum_assembledPVM`: `(p_i)` is a PVM;
* `sqrt_mul_assembledPVM_mul_sqrt`: the paper's `|x| p_i |x| = q_i a_i`;
* `assembled_bound`: the three-term estimate
  `φ (∑ i, |a_i − p_i|²) < 9 ε`, from `φ (∑ a_i²) > 1 − ε` and
  `φ (∑ q_i a_i) ≥ 1 − ε`.

The estimate is proved through `assembled_bound_core`, which abstracts the
square root `|x|` into a plain operator `s` subject to the three properties the
argument actually uses (`0 ≤ s ≤ 1`, `s² = y`, `s p_i s = q_i a_i`); this keeps
the (long) inequality bookkeeping free of `CFC.sqrt`.

Nothing in this file is a statement of the paper; it is proof-side machinery for
`Orthogonalization/Basic.lean`.
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true
@[expose] public section
namespace Orthogonalization
open scoped ComplexOrder BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-! ### The assembled projections -/
section Assembled
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a q w : ι → H →L[ℂ] H}
end Assembled
/-! ### Operator identities and inequalities for the three terms -/
section Terms
variable {r x s z : H →L[ℂ] H}

end Terms
/-! ### The `φ`-step -/

/-! ### The three-term estimate -/
section Bound
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
set_option linter.unusedVariables false in
/-- **The core of step F3.** The paper's estimate, with the square root
`|x| = √(∑ j, q_j a_j)` abstracted into an operator `s` subject only to the
properties the argument uses: `0 ≤ s ≤ 1`, `s² = ∑ j, q_j a_j` and
`s p_i s = q_i a_i`.

The proof decomposes `a_i - p_i = b_i + d_i + c_i` with
`b_i = (1 - q_i) a_i`, `d_i = p_i s - p_i`, `c_i = q_i a_i - p_i s`
and bounds `‖b‖_φ² ≤ ε`, `‖d‖_φ² ≤ ε`, `‖c‖_φ² < ε`; three applications of the
triangle inequality (`phiNormSq_add_add_lt`) then give the constant `9`. -/
theorem assembled_bound_core (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ : ∀ x : H →L[ℂ] H, 0 ≤ φ (star x * x)) (hφ1 : φ 1 = 1)
    (a q p : ι → H →L[ℂ] H) (s : H →L[ℂ] H)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hq : ∀ i, IsStarProjection (q i)) (hqa : ∀ i, Commute (q i) (a i))
    (hp : ∀ i, IsStarProjection (p i)) (hpsum : ∑ i, p i = 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hss : s * s = ∑ j, q j * a j)
    (hsp : ∀ i, s * p i * s = q i * a i)
    (ε : ℝ) (hε : 1 - ε < (φ (∑ i, a i * a i)).re)
    (hlarge : 1 - ε ≤ (φ (∑ i, q i * a i)).re) 
    (h_Orthogonalization_IsStarProjection_mul_le_mul_of_commute : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] {r : H →L[ℂ] H},
      IsStarProjection r → ∀ {u v : H →L[ℂ] H}, u ≤ v → Commute r (v - u) → r * u ≤ r * v)
    (h_Orthogonalization_phiNormSq_add_add_lt : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} {ι : Type u_2} [inst_3 : Fintype ι],
      (∀ (z : H →L[ℂ] H), 0 ≤ (φ : (H →L[ℂ] H) → ℂ) (Star.star z * z)) →
        ∀ {b c d : ι → H →L[ℂ] H} {ε : ℝ},
          0 < ε →
            Orthogonalization.phiNormSq φ b ≤ ε →
              Orthogonalization.phiNormSq φ c ≤ ε →
                Orthogonalization.phiNormSq φ d < ε → Orthogonalization.phiNormSq φ (b + c + d) < 9 * ε)
    (h_Orthogonalization_conj_one_sub_sq_eq : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {s z p : H →L[ℂ] H},
      p * p = p → s * p * s = z → s * p * (1 - s * s) * (p * s) = z - z * z)
    (h_Orthogonalization_re_le_re_of_le : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ},
      (∀ (z : H →L[ℂ] H), 0 ≤ (φ : (H →L[ℂ] H) → ℂ) (Star.star z * z)) →
        ∀ {x y : H →L[ℂ] H}, x ≤ y → ((φ : (H →L[ℂ] H) → ℂ) x).re ≤ ((φ : (H →L[ℂ] H) → ℂ) y).re)
    (h_Orthogonalization_IsStarProjection_mul_le_of_commute : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] {q b : H →L[ℂ] H}, IsStarProjection q → 0 ≤ b → Commute q b → q * b ≤ b)
    (h_Orthogonalization_phiNormSq_eq_re_map_sum : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} {ι : Type u_2} [inst_3 : Fintype ι]
      (b : ι → H →L[ℂ] H),
      Orthogonalization.phiNormSq φ b = ((φ : (H →L[ℂ] H) → ℂ) (∑ i : ι, Star.star (b i) * b i)).re)
    (h_Orthogonalization_star_mul_self_sub_one_mul : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] {s : H →L[ℂ] H},
      Star.star s = s →
        ∀ (x : H →L[ℂ] H),
          Star.star ((s - 1) * x) * ((s - 1) * x) = Star.star x * ((1 - s) * (1 - s)) * x)
    (h_Orthogonalization_phiNormSq_le_re_map_of_le : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ},
      (∀ (z : H →L[ℂ] H), 0 ≤ (φ : (H →L[ℂ] H) → ℂ) (Star.star z * z)) →
        ∀ {ι : Type u_2} [inst_3 : Fintype ι] {b : ι → H →L[ℂ] H} {x : H →L[ℂ] H},
          ∑ i : ι, Star.star (b i) * b i ≤ x →
            Orthogonalization.phiNormSq φ b ≤ ((φ : (H →L[ℂ] H) → ℂ) x).re)
    (h_Orthogonalization_star_mul_self_proj_mul_sub_self : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] {s p : H →L[ℂ] H},
      IsStarProjection p → Star.star s = s → Star.star (p * s - p) * (p * s - p) = (1 - s) * p * (1 - s))
    (h_Orthogonalization_sq_le_self_of_le_one : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [CompleteSpace H]
      {x : H →L[ℂ] H}, 0 ≤ x → x ≤ 1 → x * x ≤ x)
    (h_Orthogonalization_conj_le_conj : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] {x y : H →L[ℂ] H},
      x ≤ y → ∀ (c : H →L[ℂ] H), Star.star c * x * c ≤ Star.star c * y * c)
    (h_Orthogonalization_star_mul_self_proj_mul : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] {r x : H →L[ℂ] H},
      IsStarProjection r → IsSelfAdjoint x → Commute r x → Star.star (r * x) * (r * x) = r * (x * x))
    (h_Orthogonalization_proj_mul_sub_sq : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] {x qq : H →L[ℂ] H},
      IsStarProjection qq → Commute qq x → qq * x - qq * x * (qq * x) = qq * (x - x * x))
    (h_Orthogonalization_one_sub_sq_le_one_sub_sq_ : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [CompleteSpace H]
      {s : H →L[ℂ] H}, 0 ≤ s → s ≤ 1 → (1 - s) * (1 - s) ≤ 1 - s * s)
    :
    (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  -- Elementary consequences of the hypotheses.
  have hone : (φ (1 : H →L[ℂ] H)).re = 1 := by rw [hφ1]; simp
  have hsa : star s = s := IsSelfAdjoint.of_nonneg hs0
  have ha_le_one : ∀ i, a i ≤ 1 := by
    intro i
    rw [← ha1]
    exact Finset.single_le_sum (f := a) (fun j _ => ha0 j) (Finset.mem_univ i)
  have haa : ∀ i, a i * a i ≤ a i := fun i => h_Orthogonalization_sq_le_self_of_le_one (ha0 i) (ha_le_one i)
  have hsum_aa_le : ∑ i, a i * a i ≤ 1 := by
    rw [← ha1]; exact Finset.sum_le_sum fun i _ => haa i
  have hbound_aa : (φ (∑ i, a i * a i)).re ≤ 1 := by
    have h := h_Orthogonalization_re_le_re_of_le hφ hsum_aa_le
    rwa [hone] at h
  have hε0 : 0 < ε := by linarith
  -- Values of `φ` on the two operators that appear as bounds.
  have hval_y : (φ (1 - ∑ i, q i * a i)).re = 1 - (φ (∑ i, q i * a i)).re := by
    rw [map_sub, Complex.sub_re, hone]
  have hval_aa : (φ (1 - ∑ i, a i * a i)).re = 1 - (φ (∑ i, a i * a i)).re := by
    rw [map_sub, Complex.sub_re, hone]
  -- The first term `b_i = (1 - q_i) a_i`.
  have hb_op : ∀ i, star ((1 - q i) * a i) * ((1 - q i) * a i) ≤ (1 - q i) * a i := by
    intro i
    have hr : IsStarProjection (1 - q i) := (hq i).one_sub
    have hcr : Commute (1 - q i) (a i) := (Commute.one_left (a i)).sub_left (hqa i)
    rw [h_Orthogonalization_star_mul_self_proj_mul hr (IsSelfAdjoint.of_nonneg (ha0 i)) hcr]
    exact h_Orthogonalization_IsStarProjection_mul_le_mul_of_commute hr (haa i)
      (hcr.sub_right (hcr.mul_right hcr))
  have hb_sum : ∑ i, (1 - q i) * a i = 1 - ∑ i, q i * a i := by
    simp only [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib, ha1]
  have hb : phiNormSq φ (fun i => (1 - q i) * a i) ≤ ε := by
    have hstep : ∑ i, star ((1 - q i) * a i) * ((1 - q i) * a i) ≤ 1 - ∑ i, q i * a i := by
      rw [← hb_sum]
      exact Finset.sum_le_sum fun i _ => hb_op i
    have h := h_Orthogonalization_phiNormSq_le_re_map_of_le (φ := φ) hφ (b := fun i => (1 - q i) * a i) hstep
    rw [hval_y] at h
    linarith
  -- The third term `d_i = p_i s - p_i`.
  have hd : phiNormSq φ (fun i => p i * s - p i) ≤ ε := by
    have hsum : ∑ i, (1 - s) * p i * (1 - s) = (1 - s) * (1 - s) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hpsum, mul_one]
    have hle : (1 - s) * (1 - s) ≤ 1 - ∑ j, q j * a j := by
      have h := h_Orthogonalization_one_sub_sq_le_one_sub_sq_ hs0 hs1
      rwa [hss] at h
    have hstep : ∑ i, star (p i * s - p i) * (p i * s - p i) ≤ 1 - ∑ j, q j * a j := by
      calc ∑ i, star (p i * s - p i) * (p i * s - p i)
          = ∑ i, (1 - s) * p i * (1 - s) :=
            Finset.sum_congr rfl fun i _ => h_Orthogonalization_star_mul_self_proj_mul_sub_self (hp i) hsa
        _ = (1 - s) * (1 - s) := hsum
        _ ≤ 1 - ∑ j, q j * a j := hle
    have h := h_Orthogonalization_phiNormSq_le_re_map_of_le (φ := φ) hφ (b := fun i => p i * s - p i) hstep
    rw [hval_y] at h
    linarith
  -- The second term `c_i = q_i a_i - p_i s`.
  have hc : phiNormSq φ (fun i => q i * a i - p i * s) < ε := by
    have hc_op : ∀ i, star (q i * a i - p i * s) * (q i * a i - p i * s) ≤ a i - a i * a i := by
      intro i
      have hci : q i * a i - p i * s = (s - 1) * (p i * s) := by
        rw [← hsp i]; noncomm_ring
      have hstar_ps : star (p i * s) = s * p i := by
        rw [star_mul, hsa, (hp i).isSelfAdjoint.star_eq]
      have h1 : star (q i * a i - p i * s) * (q i * a i - p i * s)
          = star (p i * s) * ((1 - s) * (1 - s)) * (p i * s) := by
        rw [hci, h_Orthogonalization_star_mul_self_sub_one_mul hsa]
      have h2 : star (p i * s) * ((1 - s) * (1 - s)) * (p i * s)
          ≤ star (p i * s) * (1 - s * s) * (p i * s) :=
        h_Orthogonalization_conj_le_conj (h_Orthogonalization_one_sub_sq_le_one_sub_sq_ hs0 hs1) (p i * s)
      have h3 : star (p i * s) * (1 - s * s) * (p i * s) = q i * a i - q i * a i * (q i * a i) := by
        rw [hstar_ps]
        exact h_Orthogonalization_conj_one_sub_sq_eq (hp i).isIdempotentElem.eq (hsp i)
      have h4 : q i * a i - q i * a i * (q i * a i) = q i * (a i - a i * a i) :=
        h_Orthogonalization_proj_mul_sub_sq (hq i) (hqa i)
      have h5 : q i * (a i - a i * a i) ≤ a i - a i * a i :=
        h_Orthogonalization_IsStarProjection_mul_le_of_commute (hq i) (sub_nonneg.mpr (haa i))
          ((hqa i).sub_right ((hqa i).mul_right (hqa i)))
      calc star (q i * a i - p i * s) * (q i * a i - p i * s)
          = star (p i * s) * ((1 - s) * (1 - s)) * (p i * s) := h1
        _ ≤ star (p i * s) * (1 - s * s) * (p i * s) := h2
        _ = q i * a i - q i * a i * (q i * a i) := h3
        _ = q i * (a i - a i * a i) := h4
        _ ≤ a i - a i * a i := h5
    have hc_sum : ∑ i, (a i - a i * a i) = 1 - ∑ i, a i * a i := by
      rw [Finset.sum_sub_distrib, ha1]
    have hstep : ∑ i, star (q i * a i - p i * s) * (q i * a i - p i * s) ≤ 1 - ∑ i, a i * a i := by
      rw [← hc_sum]
      exact Finset.sum_le_sum fun i _ => hc_op i
    have h := h_Orthogonalization_phiNormSq_le_re_map_of_le (φ := φ) hφ (b := fun i => q i * a i - p i * s) hstep
    rw [hval_aa] at h
    linarith
  -- Assemble: `a_i - p_i = b_i + d_i + c_i` and apply the triangle inequality.
  have hgoal : (φ (∑ i, star (a i - p i) * (a i - p i))).re
      = phiNormSq φ (fun i => a i - p i) := (h_Orthogonalization_phiNormSq_eq_re_map_sum _).symm
  rw [hgoal]
  have hfun : (fun i => a i - p i)
      = (fun i => (1 - q i) * a i) + (fun i => p i * s - p i)
        + (fun i => q i * a i - p i * s) := by
    funext i
    simp only [Pi.add_apply]
    noncomm_ring
  rw [hfun]
  exact h_Orthogonalization_phiNormSq_add_add_lt hφ hε0 hb hd hc
end Bound
end Orthogonalization
end
