module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v081b08e93cc6.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Calculus
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v081b08e93cc6.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coordinate partial derivatives and their norms

All `2d` coordinate directions of phase space `(v, z)` are indexed by `Fin d ⊕ Fin d`
(velocity coordinates on the left, position coordinates on the right). This module records the
squared gradient and Hessian norms used in the smoothing estimates, their comparison with the
operator norms of the Fréchet derivatives,
and the commutation of coordinate partials with weighted convolutions.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
/-- The unit vector of phase space in the coordinate direction `c`. -/
def coordDir : Fin d ⊕ Fin d → EvolutionAmbientState d
  | Sum.inl i => (Pi.single i 1, 0)
  | Sum.inr i => (0, Pi.single i 1)
/-- The partial derivative in the coordinate direction `c`. -/
def coordPartial (c : Fin d ⊕ Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : ℝ :=
  fderiv ℝ F y (coordDir c)
theorem norm_coordDir_le (c : Fin d ⊕ Fin d) : ‖coordDir c‖ ≤ 1 := by
  rcases c with i | i
  · simp only [coordDir, Prod.norm_def, norm_zero]
    refine max_le ?_ zero_le_one
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · simp only [coordDir, Prod.norm_def, norm_zero]
    refine max_le zero_le_one ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
theorem abs_coordPartial_le (c : Fin d ⊕ Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : |coordPartial c F y| ≤ ‖fderiv ℝ F y‖ := by
  have := (fderiv ℝ F y).le_opNorm (coordDir c)
  rw [coordPartial, ← Real.norm_eq_abs]
  exact this.trans (mul_le_of_le_one_right (norm_nonneg _) (norm_coordDir_le c))
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
