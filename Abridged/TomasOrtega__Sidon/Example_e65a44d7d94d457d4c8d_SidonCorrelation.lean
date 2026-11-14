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

-- ==== Examples.TomasOrtega__Sidon.Dependencies.vf8086e9a553a.Sidon.Analysis.FiniteFourier ====
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

-- ==== Examples.TomasOrtega__Sidon.Dependencies.vf8086e9a553a.Sidon.Analysis.Correlation ====
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

-- ==== Examples.TomasOrtega__Sidon.Dependencies.vf8086e9a553a.Sidon.Analysis.DiscreteFejer ====
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

-- ==== Examples.TomasOrtega__Sidon.Dependencies.vf8086e9a553a.Sidon.Basic ====
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

-- ==== Examples.TomasOrtega__Sidon.Dependencies.vf8086e9a553a.Sidon.Combinatorics.Intervals ====
public section
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
/-! # Integer intervals and elementary invariances -/
namespace Sidon
/-- The paper's interval `[N]`, as a finite set of integers. -/
def interval (N : ℕ) : Finset ℤ := Finset.Icc 1 N

end Sidon
namespace IsSidonSet
variable {M : Type*} [AddCommGroup M] {s t : Set M}

end IsSidonSet

end
end

-- ==== Examples.TomasOrtega__Sidon.Examples.Example_e65a44d7d94d457d4c8d_SidonCorrelation ====
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
/-! # Correlation estimates for a Sidon set and its interval model -/
noncomputable section
open scoped ComplexConjugate
namespace Sidon
def intervalModel (N : ℕ) (S : Finset ℤ) : ℤ →₀ ℂ :=
  ((S.card : ℝ) / N) • indicatorFinsupp (interval N)
def correlationError (N : ℕ) (S : Finset ℤ) (H : ℕ) (f g : ℤ →₀ ℂ) : ℝ :=
  (fejerWeight H).sum
    (fun h w => w * |(S.card : ℝ) ^ 2 / N - (correlation f g h).re|)
def boundaryPart (N : ℕ) (S : Finset ℤ) (h : ℤ) : Finset ℤ :=
  S.filter fun x => x + h ∉ interval N


set_option linter.unusedVariables false in
theorem mixed_correlationError_le {N H : ℕ} {S : Finset ℤ}
    (hH : 0 < H) (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) 
    (h_Sidon_intervalModel_mixed_deficit : ∀ (N : ℕ) (S : Finset ℤ) (h : ℤ),
      |(↑S.card : ℝ) ^ 2 / (↑N : ℝ) -
            (Sidon.correlation (Sidon.indicatorFinsupp S) (Sidon.intervalModel N S) h).re| =
        (↑S.card : ℝ) / (↑N : ℝ) * (↑(Sidon.boundaryPart N S h).card : ℝ))
    (h_Sidon_boundaryPart_card_le : ∀ {N : ℕ} {S : Finset ℤ},
      IsSidonSet (↑S : Set ℤ) →
        S ⊆ Sidon.interval N → ∀ (h : ℤ), (↑(Sidon.boundaryPart N S h).card : ℝ) ≤ 2 * √|(↑h : ℝ)|)
    (h_Sidon_sum_fejerWeight_mul_le : ∀ (H : ℕ),
      0 < H →
        ∀ (F : ℤ → ℝ) (B : ℝ),
          (∀ h ∈ (Sidon.fejerWeight H).support, F h ≤ B) →
            ((Sidon.fejerWeight H).sum fun (h : ℤ) (w : ℝ) ↦ w * F h) ≤ B)
    (h_Sidon_abs_lt_of_mem_support_fejerWeight : ∀ (H : ℕ) {h : ℤ}, h ∈ (Sidon.fejerWeight H).support → |h| < (↑H : ℤ))
    :
    correlationError N S H (indicatorFinsupp S) (intervalModel N S) ≤
      2 * (S.card : ℝ) * Real.sqrt H / N := by
  unfold correlationError
  apply h_Sidon_sum_fejerWeight_mul_le H hH
  intro h hh
  rw [h_Sidon_intervalModel_mixed_deficit]
  have hbound := h_Sidon_boundaryPart_card_le hS hSN h
  have habs : |(h : ℝ)| ≤ (H : ℝ) := by
    exact_mod_cast (h_Sidon_abs_lt_of_mem_support_fejerWeight H hh).le
  have hsqrt := Real.sqrt_le_sqrt habs
  have hcoeff : 0 ≤ (S.card : ℝ) / N := by positivity
  calc
    ((S.card : ℝ) / N) * (boundaryPart N S h).card ≤
        ((S.card : ℝ) / N) * (2 * Real.sqrt |(h : ℝ)|) :=
      mul_le_mul_of_nonneg_left hbound hcoeff
    _ ≤ ((S.card : ℝ) / N) * (2 * Real.sqrt H) := by gcongr
    _ = 2 * (S.card : ℝ) * Real.sqrt H / N := by ring
end Sidon
