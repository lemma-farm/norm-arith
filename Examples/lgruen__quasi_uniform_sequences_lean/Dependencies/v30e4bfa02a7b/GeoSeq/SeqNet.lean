/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.GeoSeq.Defs
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FMain
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FBasic
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.DShift
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# GeoSeq stage S1: sequences and nets (`sec:prelim`, the remark after `lem:nie`)

* The block `{y(v) : k q^m ≤ v < (k+1) q^m}` is a digital shift of the prefix `P_m`: for `v < q^m`,
  digit `n` of coordinate `c` of `y(k q^m + v)` is digit `n` of `y(v)` plus a constant that depends
  only on `k, c, n` (`block_shift`; the constant is digit `n` of the point `k` of the sequence with
  the columns shifted by `m`).
* A digital shift maps elementary boxes of each shape bijectively onto boxes of the same shape
  (`cond_shift`, the argument of geo `lem:shift`, `Z3NetF.shift_net`, redone over a general digit
  code `DigitCode R q`: geo's `dshiftPt` is stated over `ℤ/qℤ` only; the geo digit lemmas
  `digSum_digit`, `digSum_recon`, `digSum_div_prefix` are reused).
* Hence every block is a `(0,m,s)`-net iff the prefix is, iff the truncated generator matrices form a
  `(0,m,s)`-net in the sense of geo `lem:nie` (`blockNet0_iff`), and
  `IsSeq0 ↔ ∀ m, IsNet0E (truncGen C m)` (`isSeq0_iff_trunc`).
-/
namespace GeoSeq
open Finset Matrix
variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]
/-! ## Index digits -/
lemma idxDigit_eq_zero (D : DigitCode R q) (v k : ℕ) (h : v / q ^ k % q = 0) :
    idxDigit D v k = 0 := by
  unfold idxDigit
  have : (⟨v / q ^ k % q, Nat.mod_lt _ (NeZero.pos q)⟩ : Fin q) = D.enc 0 :=
    Fin.ext (by show v / q ^ k % q = _; rw [h, D.enc_zero])
  rw [this, Equiv.symm_apply_apply]
omit [NeZero q] in
lemma digit_high (v k : ℕ) (h : v < q ^ k) : v / q ^ k % q = 0 := by
  rw [Nat.div_eq_of_lt h, Nat.zero_mod]
lemma digit_beyond (v k : ℕ) (h : v < k) : v / q ^ k % q = 0 := by
  rcases Nat.lt_or_ge q 2 with hq | hq
  · have : q = 1 := by have := NeZero.pos q; omega
    subst this; exact Nat.mod_one _
  · apply digit_high
    calc v < k := h
      _ < 2 ^ k := Nat.lt_two_pow_self
      _ ≤ q ^ k := Nat.pow_le_pow_left hq k
/-- `seqDigit` may be summed over any range beyond which the index digits vanish. -/
lemma seqDigit_eq_range (D : DigitCode R q) (C : Gen s R) (v : ℕ) (c : Fin s) (n M : ℕ)
    (hM : ∀ k, M ≤ k → idxDigit D v k = 0) :
    seqDigit D C v c n = ∑ k ∈ range M, C c n k * idxDigit D v k := by
  unfold seqDigit
  have key : ∀ A B : ℕ, A ≤ B → (∀ k, A ≤ k → idxDigit D v k = 0) →
      ∑ k ∈ range A, C c n k * idxDigit D v k = ∑ k ∈ range B, C c n k * idxDigit D v k := by
    intro A B hAB hA
    apply Finset.sum_subset (Finset.range_subset_range.mpr hAB)
    intro k _ hk'
    simp only [mem_range, not_lt] at hk'
    rw [hA k hk', mul_zero]
  have h1 : ∀ k, v + 1 ≤ k → idxDigit D v k = 0 :=
    fun k hk => idxDigit_eq_zero D v k (digit_beyond v k (by omega))
  rw [key (v + 1) (max (v + 1) M) (le_max_left _ _) h1,
    key M (max (v + 1) M) (le_max_right _ _) hM]
/-! ## The index of a vector inside a block -/
end GeoSeq
