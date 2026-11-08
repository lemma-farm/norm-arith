module
public import Mathlib
@[expose] public section
/-!
The combined-index coefficient and tail estimates used in Lemma 5(a).
These generic results are separated from the unproved determinant power-series bridge.
-/
noncomputable section
open scoped BigOperators
namespace RoughRegime.SeriesBounds
def convolution {R : Type*} [NonUnitalNonAssocSemiring R] (f g : ℕ → R) (k : ℕ) : R :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, f ij.1 * g ij.2
theorem convolution_tsum {R : Type*} [NormedRing R] [CompleteSpace R]
    (f g : ℕ → R) (hf : Summable (fun i => ‖f i‖)) (hg : Summable (fun i => ‖g i‖)) :
    ∑' k : ℕ, convolution f g k = (∑' i : ℕ, f i) * ∑' j : ℕ, g j := by
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg).symm
end RoughRegime.SeriesBounds
