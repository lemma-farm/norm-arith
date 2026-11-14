module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Combinatorics.Additive.Energy

-- ==== Examples.TomasOrtega__Sidon.Dependencies.vdfcfa2d4d3b3.Sidon.Analysis.FiniteFourier ====
public section
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
/-!
# Finite Fourier sums on the integers

The positive-exponent convention agrees with `fourier` at period one.
-/
noncomputable section
namespace Sidon
/-- The complex indicator of a finite set of integers. -/
def indicatorFinsupp (s : Finset ℤ) : ℤ →₀ ℂ :=
  Finsupp.indicator s fun _ _ => 1

end Sidon

end
end
end

-- ==== Examples.TomasOrtega__Sidon.Dependencies.vdfcfa2d4d3b3.Sidon.Analysis.Correlation ====
public section
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
/-! # Finite correlations and integer translations -/
noncomputable section
open scoped ComplexConjugate
namespace Sidon
def correlation (f g : ℤ →₀ ℂ) (h : ℤ) : ℂ :=
  f.sum fun x c => c * conj (g (x + h))
end Sidon

end
end
end

-- ==== Examples.TomasOrtega__Sidon.Dependencies.vdfcfa2d4d3b3.Sidon.Analysis.DiscreteFejer ====
public section
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
/-! # The discrete Fejér probability kernel -/
open scoped BigOperators
namespace Sidon
/-- The distribution of the difference of two independent uniform interval points. -/
noncomputable def fejerWeight (H : ℕ) : ℤ →₀ ℝ :=
  ∑ u ∈ Finset.range H, ∑ v ∈ Finset.range H,
    Finsupp.single ((v : ℤ) - u) ((H : ℝ) ^ 2)⁻¹

end Sidon

end
end

-- ==== Examples.TomasOrtega__Sidon.Dependencies.vdfcfa2d4d3b3.Sidon.Basic ====
public section
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
open Set Cardinal
/-- A Sidon set is a set of elements in any additive commutative monoid
    where all pairwise sums are distinct. -/
def IsSidonSet {M : Type*} [AddCommMonoid M] (s : Set M) : Prop :=
  ∀ a b c d, a ∈ s → b ∈ s → c ∈ s → d ∈ s →
  a + b = c + d → ({a, b} : Set M) = ({c, d} : Set M)

end
end

-- ==== Examples.TomasOrtega__Sidon.Examples.Example_5550519de4ac6f339b54_SidonCorrelation ====
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
/-! # Correlation estimates for a Sidon set and its interval model -/
noncomputable section
open scoped ComplexConjugate
namespace Sidon
def correlationError (N : ℕ) (S : Finset ℤ) (H : ℕ) (f g : ℤ →₀ ℂ) : ℝ :=
  (fejerWeight H).sum
    (fun h w => w * |(S.card : ℝ) ^ 2 / N - (correlation f g h).re|)


set_option linter.unusedVariables false in
theorem self_correlationError_le_mass {N H : ℕ} (hH : 0 < H) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) 
    (h_Sidon_fejerWeight_zero : ∀ (H : ℕ), 0 < H → (Sidon.fejerWeight H : ℤ → ℝ) 0 = (↑H : ℝ)⁻¹)
    (h_Sidon_fejerWeight_nonneg : ∀ (H : ℕ) (h : ℤ), 0 ≤ (Sidon.fejerWeight H : ℤ → ℝ) h)
    (h_Sidon_self_correlation_pointwise_error : ∀ {S : Finset ℤ},
      IsSidonSet (↑S : Set ℤ) →
        ∀ (b : ℝ) (h : ℤ),
          |b - (Sidon.correlation (Sidon.indicatorFinsupp S) (Sidon.indicatorFinsupp S) h).re| ≤
            1 + |b - 1| -
                (Sidon.correlation (Sidon.indicatorFinsupp S) (Sidon.indicatorFinsupp S) h).re +
              if h = 0 then 2 * (↑S.card : ℝ) else 0)
    (h_Sidon_sum_fejerWeight : ∀ (H : ℕ), 0 < H → ((Sidon.fejerWeight H).sum fun (x : ℤ) (w : ℝ) ↦ w) = 1)
    :
    correlationError N S H (indicatorFinsupp S) (indicatorFinsupp S) ≤
      1 - (fejerWeight H).sum (fun h w =>
        w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) +
      |(S.card : ℝ) ^ 2 / N - 1| + 2 * (S.card : ℝ) / H := by
  let b : ℝ := (S.card : ℝ) ^ 2 / N
  let m : ℝ := S.card
  have hzero : 0 ∈ (fejerWeight H).support := by
    rw [Finsupp.mem_support_iff, h_Sidon_fejerWeight_zero H hH]
    positivity
  have hdelta : (fejerWeight H).sum
      (fun h w => w * (if h = 0 then 2 * m else 0)) = 2 * m / H := by
    simp only [mul_ite, mul_zero, Finsupp.sum]
    rw [Finset.sum_ite_eq']
    simp only [hzero, if_true, h_Sidon_fejerWeight_zero H hH]
    ring
  calc
    correlationError N S H (indicatorFinsupp S) (indicatorFinsupp S) ≤
        (fejerWeight H).sum (fun h w => w * ((1 + |b - 1|) -
          (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re +
            if h = 0 then 2 * m else 0)) := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_left (h_Sidon_self_correlation_pointwise_error hS b h)
        (h_Sidon_fejerWeight_nonneg H h)
    _ = (1 + |b - 1|) * (fejerWeight H).sum (fun _ w => w) -
        (fejerWeight H).sum (fun h w =>
          w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) +
        (fejerWeight H).sum (fun h w => w * (if h = 0 then 2 * m else 0)) := by
      simp only [Finsupp.sum, mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    _ = _ := by rw [h_Sidon_sum_fejerWeight H hH, hdelta]; dsimp only [b, m]; ring
end Sidon
