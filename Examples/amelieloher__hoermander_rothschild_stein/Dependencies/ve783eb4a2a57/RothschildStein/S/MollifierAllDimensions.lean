-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.MollifierLocallyIntegrable
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology ENNReal
namespace RothschildStein.S
variable {n : ℕ}
/-- In zero coordinate dimension ordinary mollification is exactly
the identity (BB Lemma 2.8, p. 72; degenerate carrier). -/
theorem euclideanRegularize_zero_dimension (f : (Fin 0 → ℝ) → ℝ) (ε : ℝ) :
    euclideanRegularize 0 f ε = f := by
  funext x
  unfold euclideanRegularize euclideanJScale
  have hy (z : Fin 0 → ℝ) : ε⁻¹ • (x-z) = z := Subsingleton.elim _ _
  have hf (z : Fin 0 → ℝ) : f z = f x := congrArg f (Subsingleton.elim _ _)
  simp only [pow_zero,inv_one,one_mul,hy,hf,integral_mul_const,
    (euclideanJ_normalized 0).2,one_mul]
/-- Locally integrable inputs have smooth mollifications in all
coordinate dimensions (BB pp. 72–73; degenerate carrier). -/
theorem contDiff_euclideanRegularize_all_dimensions
    {f : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (euclideanRegularize n f ε) := by
  by_cases hn : n = 0
  · subst n
    rw [euclideanRegularize_zero_dimension]
    have he : f = fun _ => f (0 : Fin 0 → ℝ) :=
      funext fun x => congrArg f (Subsingleton.elim _ _)
    rw [he]
    exact contDiff_const
  · exact contDiff_euclideanRegularize_of_locallyIntegrable (Nat.pos_of_ne_zero hn) hf hε
end RothschildStein.S
