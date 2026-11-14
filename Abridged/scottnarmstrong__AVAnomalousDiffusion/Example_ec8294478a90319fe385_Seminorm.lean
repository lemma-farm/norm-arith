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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_ec8294478a90319fe385_Seminorm ====
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

/-- The `ℓ¹`-normed version of the coordinate space.  It is used internally
to identify the operator norm of a multilinear derivative with the supremum
of its coordinate partials. -/
abbrev VecOne (d : ℕ) := PiLp (1 : ENNReal) (fun _ : Fin d ↦ ℝ)

/-- The coordinate vector in the `ℓ¹` copy. -/
def coordinateVectorOne (d : ℕ) (i : Fin d) : VecOne d :=
  PiLp.single (p := 1) (β := fun _ : Fin d ↦ ℝ) i 1
@[simp] axiom coordinateVectorOne_apply {d : ℕ} (i j : Fin d) :
    coordinateVectorOne d i j = if j = i then 1 else 0

/-- On the `ℓ¹` copy of `Vec d`, the operator norm of a multilinear map is
bounded by its largest value on tuples of coordinate vectors. -/
axiom Seminorm.coordinateTupleNonempty (d n : ℕ) [Nonempty (Fin d)] :
    (Finset.univ : Finset (Fin n → Fin d)).Nonempty
def coordinateEvaluationSup {d n : ℕ} [Nonempty (Fin d)] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ VecOne d) F) : ℝ :=
  Finset.univ.sup' (Seminorm.coordinateTupleNonempty d n)
    (fun I ↦ ‖T (fun j ↦ coordinateVectorOne d (I j))‖)
theorem norm_continuousMultilinearMap_le_coordinateEvaluationSup
    {d n : ℕ} [Nonempty (Fin d)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ VecOne d) F) :
    ‖T‖ ≤ coordinateEvaluationSup T := by
  induction n with
  | zero =>
      classical
      refine ContinuousMultilinearMap.opNorm_le_bound
        (M := coordinateEvaluationSup T) ?_ fun m ↦ ?_
      · unfold coordinateEvaluationSup
        let I : Fin 0 → Fin d := fun j ↦ Fin.elim0 j
        exact le_trans (norm_nonneg _) <| Finset.le_sup'
          (fun J ↦ ‖T (fun j ↦ coordinateVectorOne d (J j))‖) (Finset.mem_univ I)
      let I : Fin 0 → Fin d := fun j ↦ Fin.elim0 j
      have hm : m = fun j ↦ coordinateVectorOne d (I j) := by
        funext j
        exact Fin.elim0 j
      rw [hm]
      have hI : ‖T (fun j ↦ coordinateVectorOne d (I j))‖ ≤ coordinateEvaluationSup T :=
        Finset.le_sup' (fun J ↦ ‖T (fun j ↦ coordinateVectorOne d (J j))‖)
          (Finset.mem_univ I)
      simpa using hI
  | succ n ih =>
      classical
      let C := coordinateEvaluationSup T
      have hC : 0 ≤ C := by
        unfold C coordinateEvaluationSup
        let I₀ : Fin (n + 1) → Fin d := fun _ ↦ Classical.choice ‹Nonempty (Fin d)›
        exact le_trans (norm_nonneg _) <| Finset.le_sup'
          (fun J ↦ ‖T (fun j ↦ coordinateVectorOne d (J j))‖)
          (Finset.mem_univ I₀)
      have hBasis (i : Fin d) :
          ‖T.curryLeft (coordinateVectorOne d i)‖ ≤ C := by
        calc
          ‖T.curryLeft (coordinateVectorOne d i)‖ ≤
            coordinateEvaluationSup (T.curryLeft (coordinateVectorOne d i)) := ih _
          _ ≤ C := by
            unfold C coordinateEvaluationSup
            refine Finset.sup'_le (Seminorm.coordinateTupleNonempty d n)
              (fun I ↦ ‖T.curryLeft (coordinateVectorOne d i)
                (fun j ↦ coordinateVectorOne d (I j))‖) fun I hI ↦ ?_
            have htuple :
                (fun j : Fin (n + 1) ↦
                  coordinateVectorOne d (Fin.cons (α := fun _ : Fin (n + 1) ↦ Fin d) i I j)) =
                  Fin.cons (coordinateVectorOne d i)
                    (fun j ↦ coordinateVectorOne d (I j)) := by
              funext j
              refine Fin.cases ?_ ?_ j
              · simp
              · intro j
                simp
            rw [ContinuousMultilinearMap.curryLeft_apply, ← htuple]
            exact le_rfl.trans <|
              Finset.le_sup' (fun J ↦ ‖T (fun j ↦ coordinateVectorOne d (J j))‖)
                (Finset.mem_univ (Fin.cons i I))
      have hrepr (x : VecOne d) :
          x = ∑ i : Fin d, x i • coordinateVectorOne d i := by
        ext j
        simp [coordinateVectorOne_apply]
      have hmap (x : VecOne d) :
          ‖T.curryLeft x‖ ≤ C * ‖x‖ := by
        calc
          ‖T.curryLeft x‖ =
              ‖T.curryLeft (∑ i : Fin d, x i • coordinateVectorOne d i)‖ := by
                exact congrArg (fun z ↦ ‖T.curryLeft z‖) (hrepr x)
          _ = ‖∑ i : Fin d, x i • T.curryLeft (coordinateVectorOne d i)‖ := by
                congr 1
                simp
          _ ≤
              ∑ i : Fin d, ‖x i • T.curryLeft (coordinateVectorOne d i)‖ := norm_sum_le _ _
          _ ≤ ∑ i : Fin d, ‖x i‖ * C := by
            refine Finset.sum_le_sum fun i hi ↦ ?_
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left (hBasis i) (norm_nonneg _)
          _ = C * ‖x‖ := by
            calc
              _ = (∑ i : Fin d, ‖x i‖) * C := by rw [← Finset.sum_mul]
              _ = C * ‖x‖ := by rw [PiLp.norm_eq_of_L1]; ring
      calc
        ‖T‖ = ‖T.curryLeft‖ := T.curryLeft_norm.symm
        _ ≤ C := T.curryLeft.opNorm_le_bound hC hmap
        _ = coordinateEvaluationSup T := rfl

end AVenhance.FaaDiBruno
end
