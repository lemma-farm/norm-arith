module
public import Mathlib
public import Examples.stalex444__pdt_inflation_model_set_dimension.Dependencies.v5c79d9c442cc.InflationDimension.Defs
public import Examples.stalex444__pdt_inflation_model_set_dimension.Dependencies.v5c79d9c442cc.InflationDimension.Admissibility
public import Examples.stalex444__pdt_inflation_model_set_dimension.Dependencies.v5c79d9c442cc.InflationDimension.Normal
public import Examples.stalex444__pdt_inflation_model_set_dimension.Dependencies.v5c79d9c442cc.InflationDimension.DimOne
@[expose] public section
/-!
# Cyclotomic components: places, the semisimple collapse, and the tilt

Let `A` be an integer matrix whose characteristic polynomial is a power of one cyclotomic
polynomial `Φ_n`, equivalently `Φ_n(A)` is nilpotent. The least physical dimension of an
admissible `A`-invariant cut-and-project scheme on `ℤ^ι` is computed exactly.

* `isLeast_physDims_of_cyclotomic` (the semisimple collapse): if `Φ_n(A) = 0`, i.e. `A` is
  semisimple with `χ_A = Φ_nʳ`, the value is `δ_n`, `1` for `n ≤ 2` and `2` for `n ≥ 3`, whatever
  `r`; in particular `±1` on `ℤ^ι` needs `1` in every rank (`isLeast_physDims_one`,
  `isLeast_physDims_neg_one`).
* `isLeast_physDims_unipotent`, `isLeast_physDims_neg_unipotent` (`n = 1, 2`) and
  `isLeast_physDims_cyclotomic_tilt` (`n ≥ 3`), the tilt: if `Φ_n(A) ≠ 0`, the value is
  `#ι − (dim ker Φ_n(A) − dim (ker Φ_n(A) ∩ im Φ_n(A)))`. The Jordan blocks of size `≥ 2` count in
  full and the blocks of size one cost nothing: the internal space is tilted into the socle of the
  larger blocks.
* `isLeast_physDims_single_cyclotomic`: both cases in one statement.
* `tilt_physDims`, `tilt₃_physDims`: `1 ⊕ J₂(1)` on `ℤ³` needs `2` and `1 ⊕ J₃(1)` on `ℤ⁴`
  needs `3`, with explicit schemes.

Ingredients. A countable family of proper affine subspaces of a finite-dimensional real space
misses a point (Haar measure: `exists_forall_notMem_affine`, `exists_forall_apply_ne`). The
places of `ℚ(ζ_n)` are complex for `n ≥ 3`: every irreducible real factor of `Φ_n` is quadratic
(`natDegree_eq_two_of_dvd_cyclotomic`). Rational vectors are invisible to real factors of `Φ_n`
of smaller degree (`cyclotomic_dvd_of_annihilator`, from the rational annihilator lemma
`KernelSplit.exists_irreducible_dvd_of_real_annihilator`). Density is Kronecker's criterion
(`dense_of_no_integral_functional`). The lower bound reduces to the unipotent map `Aⁿ`
(`finrank_H_add_le_cyclotomic`). The generic invariant subspaces inside a repeated isotypic
component are `exists_scheme_of_cyclotomic` (a plane `span (e, A e)` at one place of `ℚ(ζ_n)`),
`exists_scheme_of_ker_inf_range` (the unipotent tilt) and `exists_internal_of_cyclotomic` (an
equivariant graph tilted into the socle at one place); the physical space of the tilt at a
complex place is the dot-product orthogonal of the same construction for `Aᵀ`.
-/
namespace InflationDimension
open Polynomial Module
open scoped Matrix
noncomputable section
namespace Tilt
/-! ### Generic points -/
section Transport
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Transport
/-! ### The tilt `1 ⊕ J₂(1)` on `ℤ³` -/
section TiltTwo
end TiltTwo
/-! ### The tilt `1 ⊕ J₃(1)` on `ℤ⁴` -/
section TiltThree
end TiltThree
/-! ### Semisimple cyclotomic matrices: `Φ_n(A) = 0` -/
section Cyclotomic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Cyclotomic
/-! ### Unipotent matrices: the tilt in general -/
section Unipotent
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem exists_pow_apply_of_isNilpotent {V : Type*} [AddCommGroup V] [Module ℝ V]
    {f : Module.End ℝ V} (hf : IsNilpotent f) {v : V} (hv : f v ≠ 0) :
    ∃ j : ℕ, f ((f ^ j) v) ≠ 0 ∧ f (f ((f ^ j) v)) = 0 := by
  classical
  obtain ⟨p, hp⟩ := hf
  have hex : ∃ m, (f ^ m) v = 0 := ⟨p, by rw [hp, LinearMap.zero_apply]⟩
  have hm0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h, pow_zero, Module.End.one_apply] at this
    exact hv (by rw [this, map_zero])
  have hm1 : Nat.find hex ≠ 1 := by
    intro h
    have := Nat.find_spec hex
    rw [h, pow_one] at this
    exact hv this
  refine ⟨Nat.find hex - 2, ?_, ?_⟩
  · have h := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rwa [show Nat.find hex - 1 = (Nat.find hex - 2) + 1 by omega, pow_succ',
      Module.End.mul_apply] at h
  · have h := Nat.find_spec hex
    rwa [show Nat.find hex = (Nat.find hex - 2) + 1 + 1 by omega, pow_succ', pow_succ',
      Module.End.mul_apply, Module.End.mul_apply] at h
/-- **A power-bounded unipotent map is the identity.** If `f − 1` is nilpotent and `f` is
power-bounded on an invariant subspace `H`, then `f = 1` on `H`. -/
theorem sub_one_apply_eq_zero_of_bdd {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Module.End ℝ V} (hnil : IsNilpotent (f - 1)) {H : Submodule ℝ V}
    (hH : ∀ v ∈ H, f v ∈ H) {C : ℝ} (hC : ∀ m : ℕ, ∀ v ∈ H, ‖(f ^ m) v‖ ≤ C * ‖v‖) :
    ∀ v ∈ H, (f - 1) v = 0 := by
  intro v hv
  by_contra hne
  obtain ⟨j, hj1, hj2⟩ := exists_pow_apply_of_isNilpotent hnil hne
  set N := f - 1 with hN
  have hNapp : ∀ u, N u = f u - u := fun u => by
    rw [hN, LinearMap.sub_apply, Module.End.one_apply]
  have hNH : ∀ u ∈ H, N u ∈ H := fun u hu => by rw [hNapp]; exact H.sub_mem (hH u hu) hu
  have hpowH : ∀ k : ℕ, ∀ u ∈ H, (N ^ k) u ∈ H := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      rw [pow_succ', Module.End.mul_apply]
      exact hNH _ (ih u hu)
  set w := (N ^ j) v with hw
  have hwH : w ∈ H := hpowH j v hv
  have hf : ∀ u, f u = u + N u := fun u => by rw [hNapp]; abel
  have horbit : ∀ m : ℕ, (f ^ m) w = w + (m : ℝ) • N w := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, hf w, hf (N w), hj2, add_zero]
      push_cast
      module
  have hbound : ∀ m : ℕ, (m : ℝ) * ‖N w‖ ≤ (C + 1) * ‖w‖ := by
    intro m
    have h1 := hC m w hwH
    rw [horbit] at h1
    have h2 : ‖(m : ℝ) • N w‖ ≤ ‖w + (m : ℝ) • N w‖ + ‖w‖ := by
      calc ‖(m : ℝ) • N w‖ = ‖(w + (m : ℝ) • N w) - w‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖w + (m : ℝ) • N w‖ + ‖w‖ := norm_sub_le _ _
    rw [norm_smul, Real.norm_natCast] at h2
    linarith
  have hpos : 0 < ‖N w‖ := norm_pos_iff.mpr hj1
  obtain ⟨m, hm⟩ := exists_nat_gt ((C + 1) * ‖w‖ / ‖N w‖)
  have := hbound m
  rw [div_lt_iff₀ hpos] at hm
  linarith
end Unipotent
section CyclotomicTilt
end CyclotomicTilt
section TiltDuality
end TiltDuality
section ComponentBounds
end ComponentBounds
end Tilt
end
end InflationDimension
