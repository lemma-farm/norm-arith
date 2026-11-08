module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.MatrixSimpleSpectrum
public import Mathlib
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
/-! # Eigenbases and simple-spectrum labels for complex matrices -/
open Matrix Polynomial
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
/-- Every simple-spectrum complex matrix has an eigenbasis with exactly `n`
distinct labels. This finite algebraic selection is not yet a measurable one. -/
theorem matrixSimpleSpectrum_exists_eigenbasis (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ)
    (hs : G.charpoly.Separable) :
    ∃ eig : Fin n → ℂ, ∃ b : Module.Basis (Fin n) ℂ (Fin n → ℂ),
      Function.Injective eig ∧ ∀ i, G *ᵥ b i = eig i • b i := by
  let s := G.charpoly.roots.toFinset
  have hcard : s.card = n := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : Fin n ≃ s := (Fintype.equivFinOfCardEq (show Fintype.card s = n by simpa using hcard)).symm
  let eig : Fin n → ℂ := fun i => e i
  have hinj : Function.Injective eig := Subtype.val_injective.comp e.injective
  have heigen (i : Fin n) : Module.End.HasEigenvalue G.toLin' (eig i) := by
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    rw [Matrix.spectrum_toLin', Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots G.charpoly_monic.ne_zero).mp
      (Multiset.mem_toFinset.mp (e i).property)
  choose r hr using fun i => (heigen i).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent' G.toLin' eig hinj r hr
  let b := basisOfLinearIndependentOfCardEqFinrank' r hli
    (by simp [Module.finrank_fintype_fun_eq_card])
  refine ⟨eig, b, hinj, fun i => ?_⟩
  have hb : ⇑b = r := coe_basisOfLinearIndependentOfCardEqFinrank' r hli _
  rw [congr_fun hb i]
  simpa only [Matrix.toLin'_apply] using (hr i).apply_eq_smul
end
end GinibrePoincare
