module

public import Mathlib
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_1ee93108fd59ab04e3c1_UniformInverseDerivatives ====
@[expose] public section
/-! Degree-independent complex-neighborhood bounds for the actual reciprocal polynomials. -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open Polynomial
section ChebyshevPerturbation
variable {R : Type*} [Ring R] [Algebra ℝ R]
end ChebyshevPerturbation
section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]
end ChebyshevNorm
section PowerSeriesBounds
variable {R I : Type*} [NormedCommRing R] [NormOneClass R] [DecidableEq I]

end PowerSeriesBounds
section ComplexMatrices
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
set_option linter.unusedVariables false in
theorem determinant_series_coefficient_bound (K : Matrix n n (PowerSeries ℂ))
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hK : ∀ i j k, ‖PowerSeries.coeff k (K i j)‖ ≤ B * q ^ k) (k : ℕ) 
    (h_NearlyMinimax_powerSeries_prod_geometric_bound : ∀ {R : Type} {I : Type u_1} [inst : NormedCommRing R] [NormOneClass R] [DecidableEq I]
      (s : Finset I) (f : I → PowerSeries R) (q B : ℝ),
      0 < q →
        0 ≤ B →
          (∀ i ∈ s, ∀ (k : ℕ), ‖(PowerSeries.coeff k : PowerSeries R → R) (f i)‖ ≤ B * q ^ k) →
            ∀ (k : ℕ),
              ‖(PowerSeries.coeff k : PowerSeries R → R) (∏ i ∈ s, f i)‖ ≤
                B ^ s.card * (↑(k + 1) : ℝ) ^ s.card * q ^ k)
    :
    ‖PowerSeries.coeff k K.det‖ ≤
      (Fintype.card (Equiv.Perm n) : ℝ) * B ^ Fintype.card n *
        ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * q ^ k := by
  have hsign (σ : Equiv.Perm n) (P : PowerSeries ℂ) :
      ‖PowerSeries.coeff k (Equiv.Perm.sign σ • P)‖ = ‖PowerSeries.coeff k P‖ := by
    obtain hs | hs := Int.units_eq_one_or (Equiv.Perm.sign σ)
    · rw [hs]; simp
    · rw [hs]; simp [Units.smul_def]
  rw [Matrix.det_apply, map_sum]
  calc
    _ ≤ ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (Equiv.Perm.sign σ • ∏ i, K (σ i) i)‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (∏ i, K (σ i) i)‖ := by
      apply Finset.sum_congr rfl; intro σ hσ; exact hsign σ _
    _ ≤ ∑ _σ : Equiv.Perm n,
        B ^ Fintype.card n * ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * q ^ k := by
      apply Finset.sum_le_sum
      intro σ hσ
      simpa using h_NearlyMinimax_powerSeries_prod_geometric_bound Finset.univ (fun i => K (σ i) i) q B hq hB
        (fun i hi => hK _ _ ) k
    _ = _ := by simp [mul_assoc]
end ComplexMatrices
section ComplexFreeCoordinates
end ComplexFreeCoordinates
section PolynomialBounds
end PolynomialBounds
section CoordinateOperators
end CoordinateOperators
section UniformNeighborhood
end UniformNeighborhood
section ActualDerivatives
end ActualDerivatives
end NearlyMinimax
