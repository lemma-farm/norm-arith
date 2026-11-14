module

public import Mathlib

-- ==== Examples.stalex444__pdt_inflation_model_set_dimension.Examples.Example_af5d072fb9db658d9244_Normal ====
@[expose] public section
/-!
# Normal form and characterization of invariant splittings, `χ_A` squarefree

Let `A` be an integer matrix whose characteristic polynomial `χ_A` is squarefree over `ℚ`.

* `normal_form`: every `A`-invariant splitting `ℝ^ι = E ⊕ H` is the kernel splitting
  `E = ker q_E(A)`, `H = ker q_H(A)` of the factorization `χ_A = q_E q_H` over `ℝ`, where `q_E`,
  `q_H` are the characteristic polynomials of `A|_E`, `A|_H`.
* `exists_admissible_iff`: the splitting carries an admissible scheme if and only if every root
  of `q_H` lies in the closed unit disk and every irreducible factor of `χ_A` over `ℚ` shares a
  complex root with `q_E`.
* `exists_int_mem_ker`: for every irreducible factor `p` of `χ_A` over `ℚ` (no squarefree
  hypothesis), the lattice `ℤ^ι` meets `ker p(A)` in a nonzero vector: `p(A)` is singular over
  `ℂ` at an eigenvector for a root of `p`, hence singular over `ℚ`, and a rational kernel vector
  is scaled to an integer one.

Necessity of the shared-root condition: a factor `p` sharing no root with `q_E` divides `q_H`,
so the integer vector of `ker p(A)` lies in `H`. Sufficiency: injectivity from the rational
annihilator lemma, density from Kronecker's criterion, and admissibility from the
power-boundedness of `A` on `H`.

The supporting lemmas, in the namespace `InflationDimension.KernelSplit`, are: the dimension lemma
(`finrank_ker_aeval_of_coprime`: for `χ_f = q r` with `q`, `r` monic and coprime, the kernels of
`q(f)` and `r(f)` are complementary and `dim ker q(f) = deg q`), the rational annihilator lemma
(`exists_irreducible_dvd_of_real_annihilator`), injectivity and the absence of integral
functionals for the kernel splitting under the shared-root condition, and power-boundedness on
the kernel of a polynomial with distinct roots in the closed unit disk (Lagrange interpolation of
`z ↦ zⁿ` on the roots).
-/
namespace InflationDimension
open Polynomial Module
open scoped Matrix
noncomputable section
namespace KernelSplit
section General
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
end General
section Power
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

set_option linter.unusedVariables false in
/-- **Power-boundedness on `ker q(f)`** for a real monic `q` whose complex roots are distinct
and lie in the closed unit disk: one constant `C` with `‖fⁿ v‖ ≤ C ‖v‖` for all `n` and all
`v ∈ ker q(f)`. -/
theorem powerBounded_of_nodal (f : Module.End ℝ V) {q : ℝ[X]} (hq : q.Monic) (s : Finset ℂ)
    (hs : ∀ z ∈ s, ‖z‖ ≤ 1) (hqs : q.map (algebraMap ℝ ℂ) = Lagrange.nodal s id) 
    (h_InflationDimension_KernelSplit_coeff_X_pow_modByMonic_nodal_bounded : ∀ (s : Finset ℂ),
      (∀ z ∈ s, ‖z‖ ≤ 1) →
        ∀ (k : ℕ),
          ∃ (K : ℝ), ∀ (n : ℕ), ‖((Polynomial.X ^ n %ₘ Lagrange.nodal s id).coeff : ℕ → ℂ) k‖ ≤ K)
    :
    ∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ LinearMap.ker (aeval f q), ‖(f ^ n) v‖ ≤ C * ‖v‖ := by
  classical
  choose K hK using h_InflationDimension_KernelSplit_coeff_X_pow_modByMonic_nodal_bounded s hs
  set m := q.natDegree with hm
  set B : ℕ → ℝ := fun k => ‖LinearMap.toContinuousLinearMap (f ^ k)‖ with hB
  refine ⟨∑ k ∈ Finset.range m, K k * B k, fun n v hv => ?_⟩
  rw [LinearMap.mem_ker] at hv
  by_cases hq1 : q = 1
  · rw [hq1, map_one, Module.End.one_apply] at hv
    simp [hv]
  set r := (X ^ n : ℝ[X]) %ₘ q with hr
  -- `fⁿ v = r(f) v`
  have hfn : (f ^ n) v = aeval f r v := by
    have hsplit := Polynomial.modByMonic_add_div (X ^ n : ℝ[X]) q
    have h2 : aeval f (X ^ n : ℝ[X]) v = aeval f r v + aeval f (q * ((X ^ n) /ₘ q)) v := by
      conv_lhs => rw [← hsplit]
      rw [map_add, LinearMap.add_apply]
    rw [mul_comm, map_mul, Module.End.mul_apply, hv, map_zero, add_zero] at h2
    rw [← h2, map_pow, aeval_X]
  -- coefficients of `r` are those of the complex remainder
  have hrc : ∀ k, ‖r.coeff k‖ ≤ K k := by
    intro k
    have hmap : r.map (algebraMap ℝ ℂ) = (X ^ n : ℂ[X]) %ₘ Lagrange.nodal s id := by
      rw [hr, Polynomial.map_modByMonic _ hq, hqs, Polynomial.map_pow, Polynomial.map_X]
    have := hK k n
    rw [← hmap, Polynomial.coeff_map] at this
    simpa using this
  have hK0 : ∀ k, 0 ≤ K k := fun k => (norm_nonneg _).trans (hK k 0)
  have hBv : ∀ k, ‖(f ^ k) v‖ ≤ B k * ‖v‖ := by
    intro k
    have := (LinearMap.toContinuousLinearMap (f ^ k)).le_opNorm v
    simpa [hB] using this
  have hlt : r.natDegree < m := Polynomial.natDegree_modByMonic_lt _ hq hq1
  rw [hfn, Polynomial.aeval_eq_sum_range' hlt, LinearMap.sum_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul (hrc k) (hBv k) (norm_nonneg _) (hK0 k)
end Power
section Lattice
end Lattice
end KernelSplit
section Exports
end Exports
end
end InflationDimension
