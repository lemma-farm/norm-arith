import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Interval
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
/-!
# Deterministic recurrence integration: adaptive descent

This file formalizes the adaptive descent and its purely ordered telescoping
backbone for ABK26 `l.integrate.approx.recurrence`, Steps 3--4.  The argument
uses a single step-back strong induction, an equivalent presentation of the
paper’s adaptive-chain summation.

## References

* ABK26.
-/
namespace Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration
open scoped BigOperators
noncomputable section
namespace Internal
open Real
open Real
open scoped BigOperators
open Real
variable {ν cstar γ E F : ℝ}
theorem bound_by_descent_le {mc m₀ : ℤ} {Φ dd : ℤ → ℝ} (nn : ℤ → ℤ)
    (hbase : ∀ m : ℤ, m ≤ mc → |dd m| ≤ Φ m)
    (hlt : ∀ m : ℤ, mc < m → m ≤ m₀ → nn m < m)
    (hstep : ∀ m : ℤ, mc < m → m ≤ m₀ → |dd (nn m)| ≤ Φ (nn m) →
      |dd m - dd (nn m)| ≤ Φ m - Φ (nn m)) :
    ∀ m : ℤ, m ≤ m₀ → |dd m| ≤ Φ m := by
  suffices H : ∀ k : ℕ, ∀ m : ℤ, m ≤ m₀ → (m - mc).toNat ≤ k → |dd m| ≤ Φ m by
    intro m hm; exact H (m - mc).toNat m hm le_rfl
  intro k
  induction k with
  | zero => intro m _ hm; exact hbase m (by omega)
  | succ k ih =>
      intro m hmm₀ hm
      by_cases hle : m ≤ mc
      · exact hbase m hle
      · push Not at hle
        have hnn_lt : nn m < m := hlt m hle hmm₀
        have hdepth : (nn m - mc).toNat ≤ k := by omega
        have hlow : |dd (nn m)| ≤ Φ (nn m) := ih (nn m) (by omega) hdepth
        have hincr : |dd m - dd (nn m)| ≤ Φ m - Φ (nn m) := hstep m hle hmm₀ hlow
        have htri : |dd m| ≤ |dd m - dd (nn m)| + |dd (nn m)| := by
          have h := abs_sub_le (dd m) (dd (nn m)) 0
          simpa using h
        linarith only [htri, hlow, hincr]
end Internal
end
end Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration
