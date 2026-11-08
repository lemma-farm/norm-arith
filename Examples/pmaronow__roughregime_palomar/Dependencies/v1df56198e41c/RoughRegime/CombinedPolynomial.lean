module
public import Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.MatrixDeterminant
@[expose] public section
/-! The exact entry polynomials for the matrix-inverse/determinant product in
Lemma 5(a), with all matrix entries represented as independent variables. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.CombinedPolynomial
open MatrixDeterminant MatrixUpper Upper
abbrev Variables {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) :=
  (Fin n0 × Fin n0) ⊕ ((i : Fin N) × (Fin (dims i) × Fin (dims i)))
def inverseVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab : Fin n0 × Fin n0 => (Sum.inl ab : Variables n0 dims))).toRingHom
    (variableKernelSeries lo hi a b)
def determinantVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (i : Fin N) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab : Fin (dims i) × Fin (dims i) => (Sum.inr ⟨i, ab⟩ : Variables n0 dims))).toRingHom
    (variableKernelSeries lo hi (n := Fin (dims i))).det
def combinedVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  inverseVariableSeries n0 dims lo hi a b * ∏ i, determinantVariableSeries n0 dims lo hi i
def combinedCoefficientPolynomial {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (k : ℕ) : MvPolynomial (Variables n0 dims) ℝ :=
  PowerSeries.coeff k (combinedVariableSeries n0 dims lo hi a b)
def truncationEntryPolynomial {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (m : ℕ) : MvPolynomial (Variables n0 dims) ℝ :=
  MvPolynomial.C ((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹) *
    ∑ k ∈ Finset.range (m + 1), combinedCoefficientPolynomial n0 dims lo hi a b k
end RoughRegime.CombinedPolynomial
