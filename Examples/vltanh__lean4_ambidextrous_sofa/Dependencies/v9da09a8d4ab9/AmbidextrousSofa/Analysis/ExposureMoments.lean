module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.ErosionVariation
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Literal source masses and the translation balance

Every mass in this file is the Lebesgue measure of the actual selected
source set of a finite min/max expression. Integrating all wall velocities
gives a finite weighted sum of these masses. Horizontal translation then
gives the exact signed endpoint balance. No limiting niche graph or
identification of a weak limit with graph arclength is used.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
namespace WallExpr
variable {ι : Type*}
def sourceMass (e : WallExpr ι) (a b : ι → ℝ) (l r : ℝ) (j : ι) : ℝ :=
  volume.real (Ioc l r ∩ e.sourceSet a b j)
theorem intervalIntegrable_sourceDensity [Fintype ι] (e : WallExpr ι)
    (a b w : ι → ℝ) (l r : ℝ) :
    IntervalIntegrable (e.sourceDensity a b w) volume l r :=
  intervalIntegrable_const.mono_fun' (e.measurable_sourceDensity a b w).aestronglyMeasurable
    (.of_forall fun _ => Finset.single_le_sum (f := fun i => |w i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ _))
/-- The finite source partition integrates to ordinary physical horizontal
lengths, with no differentiability assertion built into those lengths. -/
theorem integral_sourceDensity_eq_sum [Fintype ι] (e : WallExpr ι)
    (a b w : ι → ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in l..r, e.sourceDensity a b w x) =
      ∑ j, e.sourceMass a b l r j * w j := by
  classical
  have hsum x : e.sourceDensity a b w x = ∑ j, (e.sourceSet a b j).indicator (fun _ => w j) x := by
    simp [sourceDensity, sourceSet, indicator_apply]
  simp_rw [intervalIntegral.integral_of_le hlr, hsum]
  rw [integral_finsetSum _ fun j _ => ((integrableOn_const measure_Ioc_lt_top.ne).indicator
    (e.measurableSet_sourceSet a b j)).integrable]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [setIntegral_indicator (e.measurableSet_sourceSet a b j), setIntegral_const, smul_eq_mul]
  rfl
end WallExpr
/-- Total wall variation, using the two charged exterior source masses
and the central source masses. The two expressions can have different
finite source types. -/
def finiteSourceVariation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b : ι → ℝ) (c d : κ → ℝ)
    (l r : ℝ) (w : ι → ℝ) (v : κ → ℝ) : ℝ :=
  (∑ i, (outer.sourceMass a b l (l + (r - l) / 4) i +
    outer.sourceMass a b (r - (r - l) / 4) r i) * w i) -
      ∑ j, inner.sourceMass c d (l + (r - l) / 4) (r - (r - l) / 4) j * v j
theorem finiteSourceVariation_eq_integrals {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b w : ι → ℝ) (c d v : κ → ℝ)
    {l r : ℝ} (hlr : l ≤ r) :
    finiteSourceVariation outer inner a b c d l r w v =
      (∫ x in l..(l + (r - l) / 4), outer.sourceDensity a b w x) +
        (∫ x in (r - (r - l) / 4)..r, outer.sourceDensity a b w x) -
        ∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), inner.sourceDensity c d v x := by
  rw [outer.integral_sourceDensity_eq_sum a b w (by linarith),
    outer.integral_sourceDensity_eq_sum a b w (by linarith),
    inner.integral_sourceDensity_eq_sum c d v (by linarith)]
  simp only [finiteSourceVariation, add_mul, Finset.sum_add_distrib]
theorem finiteSourceVariation_add {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b : ι → ℝ) (c d : κ → ℝ)
    (l r : ℝ) (w w' : ι → ℝ) (v v' : κ → ℝ) :
    finiteSourceVariation outer inner a b c d l r (fun i => w i + w' i)
        (fun j => v j + v' j) =
      finiteSourceVariation outer inner a b c d l r w v +
        finiteSourceVariation outer inner a b c d l r w' v' := by
  simp only [finiteSourceVariation, mul_add, Finset.sum_add_distrib]
  ring
theorem finiteSourceVariation_neg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b : ι → ℝ) (c d : κ → ℝ)
    (l r : ℝ) (w : ι → ℝ) (v : κ → ℝ) :
    finiteSourceVariation outer inner a b c d l r (fun i => -w i) (fun j => -v j) =
      -finiteSourceVariation outer inner a b c d l r w v := by
  simp only [finiteSourceVariation, mul_neg, Finset.sum_neg_distrib]
  ring
end AmbidextrousSofa
