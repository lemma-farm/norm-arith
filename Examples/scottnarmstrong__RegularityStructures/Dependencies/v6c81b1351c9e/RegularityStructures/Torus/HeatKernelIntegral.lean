/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v6c81b1351c9e.RegularityStructures.Torus.HeatKernelFacts
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The Gaussian periodisation on the three-torus

The normalization and locally uniform convergence of the periodised Gaussian are recorded here. This
is the unfolding of the periodised heat kernel (2.1) of the statement.
-/
public section
open MeasureTheory Real Set Submodule
namespace RegularityStructures
noncomputable def integerLatticeAddEquiv :
    (Fin 3 → ℤ) ≃ (span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup := by
  let e : (Fin 3 → ℤ) →
      (span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup :=
    fun k => ⟨fun i => (k i : ℝ), by
      change (fun i => (k i : ℝ)) ∈ span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))
      rw [Module.Basis.mem_span_iff_repr_mem]
      simp [Pi.basisFun_repr]
      ⟩
  apply Equiv.ofBijective e
  constructor
  · intro k l h
    have h' : (fun i => (k i : ℝ)) = fun i => (l i : ℝ) := congrArg Subtype.val h
    funext i
    exact_mod_cast congrFun h' i
  · intro x
    have hx' : ∀ i, ∃ n : ℤ, x.1 i = (n : ℝ) := by
      have hmem := (Pi.basisFun ℝ (Fin 3)).mem_span_iff_repr_mem ℤ (x : Fin 3 → ℝ)
        |>.mp x.2
      simp [Pi.basisFun_repr] at hmem
      intro i
      rcases hmem i with ⟨n, hn⟩
      exact ⟨n, hn.symm⟩
    choose k hk using hx'
    refine ⟨k, ?_⟩
    apply Subtype.ext
    funext i
    dsimp [e]
    exact (hk i).symm
noncomputable instance integerLatticeCountable :
    Countable (span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup :=
  Countable.of_equiv (Fin 3 → ℤ) integerLatticeAddEquiv
end RegularityStructures
end
