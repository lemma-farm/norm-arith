module

public import Mathlib

-- ==== Examples.cadamcat__catalan_lean4.Examples.Example_7abe09787a9baee98829_TailBound ====
/-!
# `Catalan.Runge.TailBound`

Part of the Catalan formalization.
-/
@[expose] public section
set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
namespace Catalan.Runge


set_option linter.unusedVariables false in
lemma norm_series_tail_le
    (m : ℕ) (hm : 0 < m) (c : ℕ → ℂ) (z v : ℂ) (hz : ‖z‖ < 1)
    (hc : ∀ k, ‖c k‖ ≤ (Nat.multichoose m k : ℝ))
    (hsum : HasSum (fun k : ℕ => c k * z ^ k) v) 
    (h_Catalan_Runge_multichoose_tail_le : ∀ (m j : ℕ), 0 < m → m.multichoose (m + 1 + j) ≤ (2 * m).choose (m + 1) * (2 * m + 1).multichoose j)
    (h_Catalan_Runge_summable_nat_add_complex : ∀ {f : ℕ → ℂ} (k : ℕ), Summable f → Summable fun (j : ℕ) ↦ f (j + k))
    (h_Catalan_Runge_norm_summable_complex : ∀ {f : ℕ → ℂ}, Summable f → Summable fun (j : ℕ) ↦ ‖f j‖)
    (h_Catalan_Runge_complex_norm_tsum_le : ∀ {f : ℕ → ℂ}, (Summable fun (j : ℕ) ↦ ‖f j‖) → ‖∑' (j : ℕ), f j‖ ≤ ∑' (j : ℕ), ‖f j‖)
    (h_Catalan_Runge_tsum_nat_add_sub_sum_range : ∀ {G : Type} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G]
      [T2Space G] (f : ℕ → G) (k : ℕ) {v : G},
      HasSum f v → ∑' (j : ℕ), f (j + k) = v - ∑ j ∈ Finset.range k, f j)
    :
    ‖v - ∑ k ∈ Finset.range (m + 1), c k * z ^ k‖ ≤
      ((2 * m).choose (m + 1) : ℝ) * ‖z‖ ^ (m + 1) / (1 - ‖z‖) ^ (2 * m + 1) := by
  let r : ℝ := ‖z‖
  let C : ℝ := ((2*m).choose (m+1) : ℝ)
  have hr : r < 1 := hz
  have hr0 : 0 ≤ r := norm_nonneg _
  have htail :=
    h_Catalan_Runge_tsum_nat_add_sub_sum_range (fun k ↦ c k * z ^ k) (m+1) hsum
  have hsTail := h_Catalan_Runge_summable_nat_add_complex (m+1) hsum.summable
  have hnormTail := h_Catalan_Runge_norm_summable_complex hsTail
  have hnorm := h_Catalan_Runge_complex_norm_tsum_le hnormTail
  have hmc2 (j : ℕ) : Nat.multichoose (2*m+1) j =
      (j + 2*m).choose (2*m) := by
    rw [Nat.multichoose_eq]
    have h : 2*m+1+j-1 = 2*m+j := by omega
    rw [h]
    have hs : (2*m+j).choose j = (2*m+j).choose (2*m) := by
      simpa only [Nat.add_comm] using
        (Nat.choose_symm_add (a := 2*m) (b := j)).symm
    rw [hs]
    congr 1
    omega
  have hbound (j : ℕ) :
      ‖c (j + (m+1)) * z ^ (j + (m+1))‖ ≤
        C * r ^ (m+1) * ((j+2*m).choose (2*m) : ℝ) * r^j := by
    have hmc := h_Catalan_Runge_multichoose_tail_le m j hm
    calc
      ‖c (j + (m+1)) * z ^ (j + (m+1))‖ =
          ‖c (j + (m+1))‖ * r ^ (j + (m+1)) := by
            rw [norm_mul, norm_pow]
      _ ≤ (Nat.multichoose m (j + (m+1)) : ℝ) * r ^ (j + (m+1)) := by
            gcongr
            exact hc _
      _ ≤ (C * Nat.multichoose (2*m+1) j : ℝ) * r ^ (j + (m+1)) := by
            have hmc' :
                (Nat.multichoose m (j + (m+1)) : ℝ) ≤
                  C * (Nat.multichoose (2*m+1) j : ℝ) := by
              have hmcN : Nat.multichoose m (j + (m+1)) ≤
                    (2*m).choose (m+1) * Nat.multichoose (2*m+1) j := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmc
              dsimp [C]
              exact_mod_cast hmcN
            gcongr
      _ = C * r ^ (m+1) * ((j+2*m).choose (2*m) : ℝ) * r^j := by
            rw [hmc2]
            rw [pow_add]
            ring
  have hgeo := hasSum_choose_mul_geometric_of_norm_lt_one (k := 2*m) (r := r)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr)
  have hgeoSummable : Summable (fun j : ℕ =>
      ((j+2*m).choose (2*m) : ℝ) * r^j) := by
    exact hgeo.summable
  have hupper : Summable (fun j : ℕ =>
      C * r ^ (m+1) * ((j+2*m).choose (2*m) : ℝ) * r^j) := by
    simpa only [mul_assoc] using hgeoSummable.mul_left (C * r^(m+1))
  have hsumBound := hnorm.trans (hnormTail.tsum_le_tsum hbound hupper)
  have hupperTsum :
      (∑' j : ℕ, C * r ^ (m+1) * ((j+2*m).choose (2*m) : ℝ) * r^j) =
        C * r^(m+1) * (1 / (1-r)^(2*m+1)) := by
    have hts := hgeoSummable.tsum_mul_left (C * r^(m+1))
    rw [hgeo.tsum_eq] at hts
    simpa [mul_assoc] using hts
  rw [hupperTsum] at hsumBound
  have hfinal :
      C * r ^ (m+1) * (1 / (1-r)^(2*m+1)) =
        C * r^(m+1) / (1-r)^(2*m+1) := by
    ring
  rw [hfinal] at hsumBound
  calc
    ‖v - ∑ k ∈ Finset.range (m + 1), c k * z ^ k‖ =
        ‖∑' j : ℕ, c (j + (m+1)) * z ^ (j + (m+1))‖ := by rw [htail]
    _ ≤ C * r ^ (m+1) / (1-r)^(2*m+1) := by simpa [C, r] using hsumBound
    _ = ((2 * m).choose (m + 1) : ℝ) * ‖z‖ ^ (m + 1) /
        (1 - ‖z‖) ^ (2 * m + 1) := by rfl
end Catalan.Runge
