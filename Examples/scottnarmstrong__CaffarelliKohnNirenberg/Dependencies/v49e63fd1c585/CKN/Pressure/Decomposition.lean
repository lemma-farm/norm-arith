-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.SliceIdentity
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.LeibnizLaplacian
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Setting.Cutoff
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Harmonic.NewtonianRepresentation
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
def pressureUTensor (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (z : ParabolicPoint) (i j : Fin 3) : ℝ :=
  -u z i * (u z j - c z.2 j)
end CKN
