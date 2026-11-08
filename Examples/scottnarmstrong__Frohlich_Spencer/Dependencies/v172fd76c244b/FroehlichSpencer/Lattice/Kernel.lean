/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.Laplacian
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.Hamiltonian
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Green.Basic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The lattice instance of the generic Green-function setting

On `ℤ^ν` the off-diagonal part of `-Δ` is the kernel `hoppingKernel` (`-1` on each nearest
neighbour).

It is Hermitian, has finite rows with row sums of norms at most `2ν`, and has range one
for the `ℓ¹` distance `latticeL1Dist`.

The finite-volume Hamiltonian is the generic restricted
operator of this kernel with potential `v + 2ν`.

Motivation: Fröhlich–Spencer (1983), (1.1)–(1.9),
Fröhlich–Spencer (1983).
-/
@[expose] public section
open Matrix
namespace FroehlichSpencer
/-- The off-diagonal part of `-Δ` on `ℤ^ν`: `-1` on each nearest neighbour `x ± e_k`. -/
noncomputable def hoppingKernel (ν : ℕ) (x w : Site ν) : ℂ :=
  -∑ k : Fin ν, ((if w = x + Pi.single k (1 : ℤ) then 1 else 0) +
    (if w = x - Pi.single k (1 : ℤ) then 1 else 0))
theorem hoppingKernel_symm (ν : ℕ) (x w : Site ν) :
    hoppingKernel ν w x = star (hoppingKernel ν x w) := by
  classical
  have h1 : ∀ k : Fin ν, (x = w + Pi.single k (1 : ℤ)) ↔ (w = x - Pi.single k (1 : ℤ)) :=
    fun k => by constructor <;> intro h <;> subst h <;> simp
  have h2 : ∀ k : Fin ν, (x = w - Pi.single k (1 : ℤ)) ↔ (w = x + Pi.single k (1 : ℤ)) :=
    fun k => by constructor <;> intro h <;> subst h <;> simp
  unfold hoppingKernel
  simp only [h1, h2, star_neg, star_sum, star_add]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [add_comm]
private theorem norm_ite_add_ite_le (c d : Prop) [Decidable c] [Decidable d] :
    ‖((if c then 1 else 0 : ℂ) + (if d then 1 else 0 : ℂ))‖ ≤
      (if c then (1 : ℝ) else 0) + (if d then (1 : ℝ) else 0) := by
  refine (norm_add_le _ _).trans ?_
  by_cases hc : c <;> by_cases hd : d <;> simp [hc, hd]
theorem sum_norm_hoppingKernel_le (ν : ℕ) (x : Site ν) (s : Finset (Site ν)) :
    ∑ w ∈ s, ‖hoppingKernel ν x w‖ ≤ 2 * ν := by
  classical
  have hle : ∀ w, ‖hoppingKernel ν x w‖ ≤ ∑ k : Fin ν,
      ((if w = x + Pi.single k (1 : ℤ) then (1 : ℝ) else 0) +
        (if w = x - Pi.single k (1 : ℤ) then (1 : ℝ) else 0)) := by
    intro w
    unfold hoppingKernel
    rw [norm_neg]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    exact norm_ite_add_ite_le _ _
  have h1 : ∀ k : Fin ν, ∑ w ∈ s, ((if w = x + Pi.single k (1 : ℤ) then (1 : ℝ) else 0) +
      (if w = x - Pi.single k (1 : ℤ) then (1 : ℝ) else 0)) ≤ 2 := by
    intro k
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    split_ifs <;> norm_num
  refine (Finset.sum_le_sum fun w _ => hle w).trans ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum fun k _ => h1 k).trans ?_
  simp [mul_comm]
theorem hamiltonian_eq_restrictedOp (ν : ℕ) (Λ : Finset (Site ν)) (v : Site ν → ℝ) :
    hamiltonian ν Λ v = Infra.restrictedOp (hoppingKernel ν) (fun x => v x + 2 * (ν : ℝ)) Λ := by
  classical
  ext x y
  have hD : dirichletLaplacian ν Λ x y =
      (∑ k : Fin ν, if y.1 = x.1 + Pi.single k (1 : ℤ) then (1 : ℂ) else 0) +
      star (∑ k : Fin ν, if x.1 = y.1 + Pi.single k (1 : ℤ) then (1 : ℂ) else 0) -
      ((2 * ν : ℕ) : ℂ) * (if x = y then 1 else 0) := by
    unfold dirichletLaplacian
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rfl
  have h1 : ∀ k : Fin ν, (x.1 = y.1 + Pi.single k (1 : ℤ)) ↔
      (y.1 = x.1 - Pi.single k (1 : ℤ)) :=
    fun k => by constructor <;> intro h <;> rw [h] <;> simp
  have hstar : star (∑ k : Fin ν, if x.1 = y.1 + Pi.single k (1 : ℤ) then (1 : ℂ) else 0) =
      ∑ k : Fin ν, if y.1 = x.1 - Pi.single k (1 : ℤ) then (1 : ℂ) else 0 := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [h1]
    split_ifs <;> simp
  simp only [hamiltonian, Matrix.add_apply, Matrix.neg_apply, Matrix.diagonal_apply]
  rw [Infra.restrictedOp_apply]
  simp only [hoppingKernel, hD, hstar, Finset.sum_add_distrib]
  split_ifs <;> push_cast <;> ring
end FroehlichSpencer
