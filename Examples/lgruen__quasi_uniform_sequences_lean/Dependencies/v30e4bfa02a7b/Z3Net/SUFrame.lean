module
public import Mathlib
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.SUPoly
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.SUBoxMinor
set_option autoImplicit false
@[expose] public section
/-!
# Entry U, part 11: the frame box minors (exact confluent-Vandermonde value)

For the frame (places `∞, 0, 1, …, s-2`, rows of coordinate `0` first) and every composition `d`
of `m`, `det = ± ∏_{0 < c' < c} (c - c')^(d_c' d_c)`.

Proof: multiply the box matrix `B` on the right by the matrix `P` of the Newton-type basis
`bas n` of `ℤ[t]_{<m}` indexed like the rows: row/column `n` of coordinate `c = 0` ↔
`Ptot · t^(d_0-1-j)`, of a finite coordinate `c` ↔ `N_c (t - a_c)^j` (`N_c = ∏_{0<c'<c} (t - a_c')^(d_c')`,
`Ptot = ∏_{c' > 0} (t - a_c')^(d_c')`). Then `B P` is lower triangular with diagonal `1` resp.
`N_c(a_c)`, and the columns of `P` are monic of pairwise distinct degrees, so `P` is a column
permutation of an upper unitriangular matrix and `det P = ±1`.
-/
namespace Z3NetU.Proofs
open Polynomial Finset Matrix Z3NetU
noncomputable section
/-! ## Locating rows -/
variable {s m : ℕ} (d : Fin s → ℕ)
/-- Prefix sums `pre c = d_0 + … + d_{c-1}`. -/
def pre (c : ℕ) : ℕ := ((List.ofFn d).take c).sum
lemma pre_le_sum (c : ℕ) : pre d c ≤ ∑ t, d t := by
  unfold pre
  rw [← List.sum_ofFn]
  exact (List.take_sublist _ _).sum_le_sum (fun _ _ => Nat.zero_le _)
variable {d}
lemma pre1_le (hd : ∑ c, d c = m) : pre d 1 ≤ m := by rw [← hd]; exact pre_le_sum d 1
def tauF (hd : ∑ c, d c = m) (n : Fin m) : Fin m :=
  ⟨if (n : ℕ) < pre d 1 then m - 1 - n else n - pre d 1, by have := n.isLt; split_ifs <;> omega⟩
lemma tauF_inj (hd : ∑ c, d c = m) : Function.Injective (tauF hd (d := d)) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [tauF] at h'
  have ha := a.isLt; have hb := b.isLt
  have hp := pre1_le hd (d := d)
  ext
  split_ifs at h' <;> omega
/-- The degree permutation. -/
def tau (hd : ∑ c, d c = m) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (tauF hd) (Finite.injective_iff_bijective.mp (tauF_inj hd))
end
end Z3NetU.Proofs
