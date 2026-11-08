module
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.EntropyCoverage
public import Mathlib
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.Complex.Exponential
public section
noncomputable section
namespace SKConstants
/-- A configuration of `n` Boolean spins. The finite space has `2^n` elements. -/
abbrev Spin (n : ℕ) := Fin n → Bool
/-- Interpret `true` as `+1` and `false` as `-1`. -/
@[expose] def signedSpin {n : ℕ} (x : Spin n) (i : Fin n) : ℝ :=
  if x i then 1 else -1
/-- The completed quadratic spin Hamiltonian `H_W(x) = xᵀ W x / 2`.
No symmetry or probabilistic law for `W` is needed. -/
@[expose] def quadraticHamiltonian {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  (1 / ((2 : ℕ) : ℝ)) * ∑ i, ∑ j, signedSpin x i * W i j * signedSpin x j
/-- The actual finite partition function, with the inverse temperature
permitted to be any real number. -/
@[expose] def gibbsPartition {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ x : Spin n, Real.exp (beta * quadraticHamiltonian W x)
/-- The Gibbs probability of an individual spin configuration. -/
@[expose] def gibbsProbability {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  Real.exp (beta * quadraticHamiltonian W x) / gibbsPartition beta W
theorem gibbsPartition_pos {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : 0 < gibbsPartition beta W := by
  classical
  unfold gibbsPartition
  exact Finset.sum_pos (fun x _ ↦ Real.exp_pos (beta * quadraticHamiltonian W x))
    ⟨fun _ ↦ false, Finset.mem_univ _⟩
theorem gibbsProbability_pos {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    0 < gibbsProbability beta W x := by
  exact div_pos (Real.exp_pos _) (gibbsPartition_pos beta W)
theorem gibbsProbability_sum {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    ∑ x : Spin n, gibbsProbability beta W x = 1 := by
  classical
  unfold gibbsProbability
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (gibbsPartition_pos beta W))
end SKConstants
