-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.RestrictedInterpolationAE
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.RawCZBridge
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.PowerNormTransport
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.RieszSecondStrong
set_option autoImplicit false
set_option warningAsError true
/-! # Interpolation of the actual raw L² operator

The completed L² operator supplies measurability, a.e. sublinearity, and
the strong endpoint. Only its restricted weak estimate remains an analytic
input to the intermediate-exponent estimate.
-/
open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame
end CKN.Core.Endgame
