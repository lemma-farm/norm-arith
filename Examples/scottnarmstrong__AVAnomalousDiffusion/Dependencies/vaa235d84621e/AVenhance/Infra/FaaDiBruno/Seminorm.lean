-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Mathlib
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vaa235d84621e.Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
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
@[simp] theorem liftVecOne_toLp {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : Vec d → F) (x : Vec d) :
    liftVecOne f (WithLp.toLp 1 x) = f x := by
  simp [liftVecOne, vecOneEquiv, PiLp.coe_continuousLinearEquiv]
/-- Product Lebesgue measure on the coordinate realization `Vec d`. -/
noncomputable def vecVolume (d : ℕ) : Measure (Vec d) := by
  letI : MeasureSpace ℝ := Real.measureSpace
  exact Measure.pi (fun _ : Fin d ↦ (volume : Measure ℝ))
/-- The coordinate basis vector associated to `i : Fin d`. -/
def coordinateVector (d : ℕ) (i : Fin d) : Vec d := Pi.single i 1
/-- The coordinate vector in the `ℓ¹` copy. -/
def coordinateVectorOne (d : ℕ) (i : Fin d) : VecOne d :=
  PiLp.single (p := 1) (β := fun _ : Fin d ↦ ℝ) i 1
@[simp] theorem coordinateVectorOne_apply {d : ℕ} (i j : Fin d) :
    coordinateVectorOne d i j = if j = i then 1 else 0 := by
  simp [coordinateVectorOne]
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
/-- The essential supremum of the operator norm of the derivative on the
`ℓ¹` copy of the coordinate domain. -/
def operatorDerivativeSup {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : Vec d → F) : ENNReal :=
  eLpNormEssSup
    (fun x : Vec d ↦ ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖)
    (vecVolume d)
def snorm {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) (n : ℕ) (R : ℝ) : ENNReal :=
  ENNReal.ofReal (((n + 1 : ℝ) ^ 2) / (n.factorial : ℝ)) *
    (ENNReal.ofReal R)⁻¹ ^ n * derivativeSup n f
/-- Smoothness is preserved when the domain is viewed with the equivalent
`ℓ¹` product norm. -/
theorem contDiff_liftVecOne {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} {f : Vec d → F} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (liftVecOne f) := by
  simpa [liftVecOne] using
    (hf.comp_continuousLinearMap (g := (vecOneEquiv d : VecOne d →L[ℝ] Vec d)))
end AVenhance.FaaDiBruno
end
