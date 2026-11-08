-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Holder
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Doubling
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Integration.Slice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Average
set_option autoImplicit false
set_option warningAsError true
/-!
# Campanato oscillations on parabolic cylinders

The `L^p` oscillation of a function on a parabolic cylinder, the Campanato
bound it satisfies on a region, the tail constant of the dyadic geometric
series, and the comparison of the average of `|f|` on a subset with the
average on the ambient set.  The oscillations use genuine space-time averages.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
private instance parabolicVolumeIsLocallyFinite :
    IsLocallyFiniteMeasure (volume : Measure ParabolicPoint) :=
  { finiteAtNhds := fun p =>
      ⟨@Metric.ball ParabolicPoint parabolicPseudoMetricSpace p 1,
        @Metric.ball_mem_nhds ParabolicPoint parabolicPseudoMetricSpace p 1 one_pos,
        volume_parabolicBall_lt_top one_pos⟩ }
end CKN.Foundation.Parabolic
