module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.KineticAleksandrov.Holder.CovarianceBoundsTrace
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoff
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Native matrix contractions and ellipticity bounds for the Gaussian sign -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Matrix
open scoped BigOperators MatrixOrder
theorem loewner_quadratic_lower {d : ℕ} {A : PDE.Mat d} {lam : ℝ}
    (hl : lam • (1 : PDE.Mat d) ≤ A) (p : PDE.Vec d) :
    lam * PDE.vecNormSq p ≤ PDE.vecDot p (A.mulVec p) := by
  have hp := (Matrix.le_iff.mp hl).dotProduct_mulVec_nonneg p
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hp
  change 0 ≤ PDE.vecDot p (A.mulVec p) - lam * PDE.vecNormSq p at hp
  linarith only [hp]
end HypoellipticAleksandrov.KineticAleksandrov.Holder
