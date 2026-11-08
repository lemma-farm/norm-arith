-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationExtensionPairingCylinder
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationWholeSpace
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PotentialDecayPotentials
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PotentialDecayGrowthSum
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.PotentialLocalLp
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.PotentialLocalLpMeasure
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.PotentialLocalLpExponents
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientPotential
set_option autoImplicit false
set_option warningAsError true
/-! # The first-order identification of the slice first pressure potential

The local decomposition `eq:pk` writes the first pressure term as the double
Riesz transform `p₁ = -R_iR_j(η U_{ij})`, a second-order object.  Display (3.5)
of the pressure-gradient section instead needs the first-order form.  In the
Lean convention
`pressureNewtonianDerivativePotential i g = −(∂ᵢN * g)`, the divergence-form
source is
`Vᵢ = −∂ⱼ(η Uᵢⱼ) = +∂ⱼ(η uᵢ(uⱼ − ⟨uⱼ⟩))`.

Both sides pair with `Δψ` against the same second-order source `η U_{ij}`: the
left by the distributional identity of the pressure decomposition, the right by
the adjoint of the first-order Newtonian derivative potential using the
displayed divergence-form source.  Their difference is therefore weakly
harmonic on `ℝ³`, and the whole-space Liouville theorem with local `L^{3/2}`
linear growth identifies them almost everywhere.
-/
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
open CKN.Foundation.Euclidean
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4
