module

public import Mathlib.Algebra.Module.ZLattice.Summable

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_32522ad4c9d34dca0616_LatticeSummability ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Polynomial weights on the integer frequency lattice

The Fourier series construction uses polynomial decay on `Fin d → ℤ`.  This file packages the
elementary lattice summability estimate needed for the four-dimensional finite-window torus.
The proof follows the standard comparison with the full integer lattice inside the real
finite-dimensional space.
-/
@[expose] public section
open Filter
namespace RegularityStructures.Phi43
private noncomputable def smoothVersionLatticePoint {d : ℕ} (n : Fin d → ℤ) :
    Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d))) :=
  ⟨fun i => (n i : ℝ), by
    have hcoord : (fun i => (n i : ℝ)) = ∑ i, n i • Pi.basisFun ℝ (Fin d) i := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hcoord]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))⟩

private theorem smoothVersionLatticePoint_norm_sq_le {d : ℕ} (n : Fin d → ℤ) :
    ‖smoothVersionLatticePoint n‖ ^ 2 ≤ 1 + ∑ i, ((n i : ℝ)) ^ 2 := by
  have hsum : 0 ≤ ∑ i, ((n i : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS : 0 ≤ 1 + ∑ i, ((n i : ℝ)) ^ 2 := by linarith
  have hnorm : ‖smoothVersionLatticePoint n‖ ≤
      Real.sqrt (1 + ∑ i, ((n i : ℝ)) ^ 2) := by
    change ‖(fun i => (n i : ℝ))‖ ≤ Real.sqrt (1 + ∑ i, ((n i : ℝ)) ^ 2)
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs, Real.le_sqrt (abs_nonneg _) hS, sq_abs]
    calc
      ((n i : ℝ)) ^ 2 ≤ ∑ j, ((n j : ℝ)) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg ((n j : ℝ))) (Finset.mem_univ i)
      _ ≤ 1 + ∑ j, ((n j : ℝ)) ^ 2 := by linarith
  calc
    ‖smoothVersionLatticePoint n‖ ^ 2 ≤
        Real.sqrt (1 + ∑ i, ((n i : ℝ)) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = 1 + ∑ i, ((n i : ℝ)) ^ 2 := Real.sq_sqrt hS

end RegularityStructures.Phi43
end
