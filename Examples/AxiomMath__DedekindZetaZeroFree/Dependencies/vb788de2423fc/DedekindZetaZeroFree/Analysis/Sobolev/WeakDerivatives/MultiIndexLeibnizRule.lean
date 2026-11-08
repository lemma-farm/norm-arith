module
public import Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.vb788de2423fc.DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.WeakSolutions
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace DedekindZetaZeroFree.WeakJets.Raw
open MeasureTheory KPContLocalNorm
open scoped Topology
private theorem first_dirs {n : ℕ} (i : Fin n) : (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex i).directions = [i] := by
  classical
  simp only [MultiIndex.directions, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, apply_ite Fin.val, Fin.val_one,
    Fin.val_zero, List.replicate_one, List.replicate_zero]
  have h : ∀ l : List (Fin n), l.flatMap (fun j => if j = i then [j] else []) = l.filter (· = i) := by
    intro l; induction l with
    | nil => rfl
    | cons j l ih => by_cases hj : j = i <;> simp [hj, ih]
  have hrep : ∀ j : Fin n, List.replicate (if j = i then 1 else 0) j =
      if j = i then [j] else [] := by intro j; split_ifs <;> simp
  simp_rw [hrep]
  rw [h, List.filter_eq]
  simp
end DedekindZetaZeroFree.WeakJets.Raw
end
