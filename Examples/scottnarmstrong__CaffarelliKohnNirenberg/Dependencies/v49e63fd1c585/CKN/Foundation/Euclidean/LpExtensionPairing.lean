-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.LpExtensionPairingHeat
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.HessianL2
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.DerivativeAdjoint
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Heat.IntegralBounds
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Real.Pi.Bounds
set_option autoImplicit false
set_option warningAsError true
/-! # The first-order Newtonian adjoint and the smooth pairing

The singular identity `∫ ∂ᵢN(x - y) ∂ⱼψ(x) dx = -∫ N(x - y) ∂ᵢ∂ⱼψ(x) dx` is
obtained by heat subordination: at each positive time the Gaussian kernel is
smooth, so the identity is the ordinary compactly supported integration by
parts, and the time integral of the Gaussian family reproduces the Newtonian
kernel and its first derivative.  Fubini in the time variable is legitimate
because the test function has compact support.

Combining this with the Fubini pairing for potentials and with two classical
integrations by parts gives, for smooth compactly supported data `G`,

`∫ Pᵢ(G) ∂ⱼψ = ∫ ∂ᵢ∂ⱼ(N * G) ψ`,

which is the smooth case of the distributional adjointness used for the
`L^(6/5)` Calderón--Zygmund endpoint.
-/
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN
end CKN.Foundation.Euclidean
