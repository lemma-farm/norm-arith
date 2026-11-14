module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v7b3498f0da44.SubdiffusiveProcess.ResponseMoments.Forms ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Carriers for the comparison of two candidate energies

Subsection `mfd:sec-compare` 
 argues with two candidate local energies `E`, `F` through
their energy measures `Γ_E(u,v)`, `Γ_F(u,v)`.  This file introduces the two
carriers that the statements of that subsection need and nothing more.

* `SubdiffusiveProcess.ResponseMoments.LocalEnergy V X` is a symmetric bilinear energy *measure*
  `gam u v s` on a real vector space `V` of admissible functions, with values
  in `ℝ`, monotone and nonnegative on the diagonal.  Its form is
  `form u v = gam u v Set.univ`.  Strong locality, closedness and the
  Dirichlet property are *not* assumed: only the algebra used in
  `mfd:lem-diff`, `lem_common`, `mfd:lem-relvar`, `mfd:prop-conc` and
  `mfd:thm-prop`.
* `SubdiffusiveProcess.ResponseMoments.DomainedEnergy H X` adds the domain `dom : Submodule ℝ H`, which the
  two statements that compare unequal domains (`mfd:prop-density`,
  `mfd:thm-C0`) need.

Nothing in this file asserts a conclusion of the paper.
-/
open MeasureTheory Set
noncomputable section
namespace SubdiffusiveProcess
namespace ResponseMoments

namespace LocalEnergy
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {X : Type*} [MeasurableSpace X]
end LocalEnergy

namespace DomainedEnergy
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {X : Type*} [MeasurableSpace X]
end DomainedEnergy
def ramp (a b x : ℝ) : ℝ := min 1 (max 0 ((x - a) / (b - a)))
end ResponseMoments
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_dab4fd58047f73da7b86_Elementary ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Response moment elementary estimates

Small deterministic facts used by the resampling and comparison chain of
`mfd:sec-resampling`.

* the ramp `χ_{a,b}` of `mfd:sec-resampling` and its two endpoint values;
* `(x+y)^2 ≤ 2x^2 + 2y^2`, `mfd:sec-resampling`;
* the geometric sums used for the all-chain tail, `mfd:sec-resampling`;
* the Efron--Stein sum of `mfd:sec-resampling`.
-/
open Finset Filter Topology
noncomputable section
namespace SubdiffusiveProcess
namespace ResponseMoments
theorem abs_ramp_sub_ramp_le {a b x y : ℝ} (hab : a < b) :
    |ramp a b x - ramp a b y| ≤ |x - y| / (b - a) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hmin : |min 1 (max 0 ((x - a) / (b - a))) - min 1 (max 0 ((y - a) / (b - a)))|
      ≤ |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))| := by
    have h := abs_min_sub_min_le_max (1:ℝ) (max 0 ((x - a) / (b - a))) 1
      (max 0 ((y - a) / (b - a)))
    have heq : max |(1:ℝ) - 1| |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))|
        = |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))| := by
      simp
    rwa [heq] at h
  have hmax : |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))|
      ≤ |(x - a) / (b - a) - (y - a) / (b - a)| := by
    have h := abs_max_sub_max_le_max (0:ℝ) ((x - a) / (b - a)) 0 ((y - a) / (b - a))
    have heq : max |(0:ℝ) - 0| |(x - a) / (b - a) - (y - a) / (b - a)|
        = |(x - a) / (b - a) - (y - a) / (b - a)| := by
      simp
    rwa [heq] at h
  have huv : (x - a) / (b - a) - (y - a) / (b - a) = (x - y) / (b - a) := by
    rw [← sub_div]; ring
  have habs : |(x - a) / (b - a) - (y - a) / (b - a)| = |x - y| / (b - a) := by
    rw [huv, abs_div, abs_of_pos hba]
  calc |ramp a b x - ramp a b y|
      = |min 1 (max 0 ((x - a) / (b - a))) - min 1 (max 0 ((y - a) / (b - a)))| := rfl
    _ ≤ |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))| := hmin
    _ ≤ |(x - a) / (b - a) - (y - a) / (b - a)| := hmax
    _ = |x - y| / (b - a) := habs
end ResponseMoments
end SubdiffusiveProcess
