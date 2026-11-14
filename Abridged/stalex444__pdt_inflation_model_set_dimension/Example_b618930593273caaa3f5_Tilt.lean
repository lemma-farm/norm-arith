module

public import Mathlib

-- ==== Examples.stalex444__pdt_inflation_model_set_dimension.Examples.Example_b618930593273caaa3f5_Tilt ====
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
/-- A map of finite order is power-bounded. -/
theorem powerBounded_of_pow_eq_one {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {f : Module.End ℝ V} {n : ℕ} (hn : 0 < n) (hf : f ^ n = 1) :
    ∃ C : ℝ, ∀ k : ℕ, ∀ v : V, ‖(f ^ k) v‖ ≤ C * ‖v‖ := by
  refine ⟨∑ j ∈ Finset.range n, ‖LinearMap.toContinuousLinearMap (f ^ j)‖, fun k v => ?_⟩
  have hk : f ^ k = f ^ (k % n) := by
    conv_lhs => rw [← Nat.div_add_mod k n, pow_add, pow_mul, hf, one_pow, one_mul]
  rw [hk]
  calc ‖(f ^ (k % n)) v‖ = ‖LinearMap.toContinuousLinearMap (f ^ (k % n)) v‖ := rfl
    _ ≤ ‖LinearMap.toContinuousLinearMap (f ^ (k % n))‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (∑ j ∈ Finset.range n, ‖LinearMap.toContinuousLinearMap (f ^ j)‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        exact Finset.single_le_sum (f := fun j => ‖LinearMap.toContinuousLinearMap (f ^ j)‖)
          (fun j _ => norm_nonneg _) (Finset.mem_range.2 (Nat.mod_lt k hn))
end Cyclotomic
section Unipotent
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
