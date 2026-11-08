-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.Homogenization.Ambient.Basic
public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Normed.Lp.PiLp
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Appendix B derivative seminorms

The coordinate derivatives of order `n` are represented by evaluating the
iterated Fréchet derivative on coordinate basis vectors. An ordered list of
coordinate directions presents a multi-index, and the API groups these lists
by their multiplicities. For smooth functions, identifying all orderings of
the same multi-index uses the symmetry of iterated derivatives.
-/
@[expose] public section
noncomputable section
open MeasureTheory
namespace AVenhance.FaaDiBruno
open Homogenization
/-- The `ℓ¹`-normed version of the coordinate space.  It is used internally
to identify the operator norm of a multilinear derivative with the supremum
of its coordinate partials. -/
abbrev VecOne (d : ℕ) := PiLp (1 : ENNReal) (fun _ : Fin d ↦ ℝ)
/-- The canonical linear homeomorphism from the `ℓ¹` copy to `Vec d`. -/
noncomputable def vecOneEquiv (d : ℕ) : VecOne d ≃L[ℝ] Vec d :=
  PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin d ↦ ℝ)
/-- The function `f` viewed on the `ℓ¹` copy of the coordinate space. -/
def liftVecOne {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) : VecOne d → F := f ∘ vecOneEquiv d
noncomputable def vecVolume (d : ℕ) : Measure (Vec d) := by
  letI : MeasureSpace ℝ := Real.measureSpace
  exact Measure.pi (fun _ : Fin d ↦ (volume : Measure ℝ))
def coordinateVectorOne (d : ℕ) (i : Fin d) : VecOne d :=
  PiLp.single (p := 1) (β := fun _ : Fin d ↦ ℝ) i 1
def orderedPartial {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : Vec d → F) (x : Vec d) (I : Fin n → Fin d) : F :=
  iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)
    (fun j ↦ coordinateVectorOne d (I j))
/-- The global supremum of the derivative in the multi-index represented by
`I`. For continuous derivatives this is the pointwise representative of the
paper's `L∞` norm. -/
def partialSup {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : Vec d → F) (I : Fin n → Fin d) : ENNReal :=
  letI : MeasureSpace ℝ := Real.measureSpace
  eLpNormEssSup (fun x ↦ orderedPartial n f x I) (vecVolume d)
/-- The order-`n` derivative `L∞` seminorm. -/
def derivativeSup {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : Vec d → F) : ENNReal :=
  ⨆ I : Fin n → Fin d, partialSup n f I
def snorm {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) (n : ℕ) (R : ℝ) : ENNReal :=
  ENNReal.ofReal (((n + 1 : ℝ) ^ 2) / (n.factorial : ℝ)) *
    (ENNReal.ofReal R)⁻¹ ^ n * derivativeSup n f
end AVenhance.FaaDiBruno
end
