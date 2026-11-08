-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.LpExtensionPairingKernel
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.LpExtensionPairingPotential
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.LpExtensionPairingDensity
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.LpExtensionPairingSmooth
set_option autoImplicit false
set_option warningAsError true
/-! # Pairing the first derivative potential with the completed operator

The first Newtonian derivative potential `Pᵢ(G) = ∂ᵢN * G` and the completed
`L^(6/5)` second-derivative operator `Tᵢⱼ` are adjoint to one another in the
distributional sense: for compactly supported `L^(6/5)` data `G` and smooth
compactly supported `ψ`,

`∫ Pᵢ(G) ∂ⱼψ = ∫ Tᵢⱼ(G) ψ`.

The sign is positive: the completed operator is the unnegated second derivative
of the Newtonian potential, so the pairing selects `-Tᵢⱼ(G)` as the weak
derivative `∂ⱼPᵢ(G)`.

The proof moves both derivatives onto the test function.  On smooth compactly
supported data the completed operator is the classical Hessian
`∂ᵢ∂ⱼ(N * G)`, and two classical integrations by parts turn the left side into
`∫ G · (N * ∂ᵢ∂ⱼψ)`.  Both sides of the resulting identity are continuous
linear functionals of `G ∈ L^(6/5)`: the left through the operator norm bound
of the extension and Hölder against `ψ ∈ L⁶`, the right through Hölder against
the Newtonian potential `N * ∂ᵢ∂ⱼψ ∈ L⁶`.  Density of smooth compactly
supported classes in `L^(6/5)` closes the argument.
-/
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN
end CKN.Foundation.Euclidean
