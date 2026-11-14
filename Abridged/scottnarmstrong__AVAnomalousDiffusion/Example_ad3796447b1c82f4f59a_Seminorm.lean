module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Normed.Lp.PiLp

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v2a8f46acfe93.Homogenization.Ambient.Basic ====
public section
-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open scoped BigOperators
namespace Homogenization
abbrev Vec (d : ℕ) := Fin d → ℝ

end Homogenization

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_ad3796447b1c82f4f59a_Seminorm ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
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

/-- Product Lebesgue measure on the coordinate realization `Vec d`. -/
noncomputable def vecVolume (d : ℕ) : Measure (Vec d) := by
  letI : MeasureSpace ℝ := Real.measureSpace
  exact Measure.pi (fun _ : Fin d ↦ (volume : Measure ℝ))

/-- The coordinate vector in the `ℓ¹` copy. -/
def coordinateVectorOne (d : ℕ) (i : Fin d) : VecOne d :=
  PiLp.single (p := 1) (β := fun _ : Fin d ↦ ℝ) i 1

/-- On the `ℓ¹` copy of `Vec d`, the operator norm of a multilinear map is
bounded by its largest value on tuples of coordinate vectors. -/
axiom Seminorm.coordinateTupleNonempty (d n : ℕ) [Nonempty (Fin d)] :
    (Finset.univ : Finset (Fin n → Fin d)).Nonempty
def coordinateEvaluationSup {d n : ℕ} [Nonempty (Fin d)] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ VecOne d) F) : ℝ :=
  Finset.univ.sup' (Seminorm.coordinateTupleNonempty d n)
    (fun I ↦ ‖T (fun j ↦ coordinateVectorOne d (I j))‖)
axiom norm_continuousMultilinearMap_le_coordinateEvaluationSup
    {d n : ℕ} [Nonempty (Fin d)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ VecOne d) F) :
    ‖T‖ ≤ coordinateEvaluationSup T
/-- The order-`n` coordinate partial of `f`, with the coordinate directions
listed in `I`. This is an iterated Fréchet derivative evaluated on basis
vectors. -/
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


theorem operatorDerivative_ae_le_derivativeSup {d n : ℕ} [Nonempty (Fin d)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Vec d → F) :
    ∀ᵐ x ∂vecVolume d,
      ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖ₑ ≤ derivativeSup n f := by
  let μ := vecVolume d
  have hcoord : ∀ᵐ x ∂μ, ∀ I : Fin n → Fin d,
      ‖orderedPartial n f x I‖ₑ ≤ derivativeSup n f := by
    apply ae_all_iff.2
    intro I
    have hI : partialSup n f I ≤ derivativeSup n f :=
      le_iSup_of_le I le_rfl
    have hae : ∀ᵐ x ∂μ,
        ‖orderedPartial n f x I‖ₑ ≤ partialSup n f I := by
      simpa [partialSup, eLpNormEssSup_eq_essSup_enorm] using
        (ae_le_essSup
          (f := fun x : Vec d ↦ ‖orderedPartial n f x I‖ₑ) (μ := μ))
    exact hae.mono fun x hx ↦ hx.trans hI
  have hOp : ∀ᵐ x ∂μ,
      ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖ₑ ≤ derivativeSup n f := by
    filter_upwards [hcoord] with x hx
    by_cases htop : derivativeSup n f = ⊤
    · simp [htop]
    · let T := iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)
      have hcoordReal : ∀ I : Fin n → Fin d,
          ‖T (fun j ↦ coordinateVectorOne d (I j))‖ ≤ (derivativeSup n f).toReal := by
        intro I
        have hbound : ENNReal.ofReal ‖orderedPartial n f x I‖ ≤ derivativeSup n f := by
          simpa [Real.enorm_eq_ofReal_abs] using hx I
        rw [ENNReal.ofReal_le_iff_le_toReal htop] at hbound
        simpa [T, orderedPartial] using hbound
      have hsup : coordinateEvaluationSup T ≤ (derivativeSup n f).toReal := by
        unfold coordinateEvaluationSup
        refine Finset.sup'_le (Seminorm.coordinateTupleNonempty d n) _ ?_
        intro I hI
        exact hcoordReal I
      have hop := norm_continuousMultilinearMap_le_coordinateEvaluationSup T
      have hopen : ENNReal.ofReal ‖T‖ ≤ derivativeSup n f := by
        rw [ENNReal.ofReal_le_iff_le_toReal htop]
        exact hop.trans hsup
      simpa [T] using hopen
  simpa [μ] using hOp

end AVenhance.FaaDiBruno
end
