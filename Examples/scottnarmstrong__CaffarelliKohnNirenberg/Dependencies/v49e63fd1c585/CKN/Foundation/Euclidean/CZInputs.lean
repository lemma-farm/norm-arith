-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.RieszSecondStrong
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.RieszSecondOperator
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.InterpolationRestricted
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.LpExtension
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.RestrictedInterpolationAE
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.RawCZBridge
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step3.PressureDecay
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradient
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Identification
set_option autoImplicit false
set_option warningAsError true
/-!
# Consumer-facing Calderón--Zygmund bounds

The endpoint assembly is conditional only on the two endpoint estimates.  The
declarations here put its `3 / 2` and `6 / 5` specializations into the norm
conventions used by the pressure consumers.  The pressure identification is
kept as an explicit a.e. input until the distributional identification and
the endpoint estimates are available together.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN
open CKN.Foundation.Parabolic
