-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Iteration.Arithmetic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step2.Interpolation
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step3.PressureDecay
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Statements.Theta
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step3
open CKN
/-! The source-scale assembly below is the interface between the analytic
estimates and the elementary combination theorem.  The pressure estimate is
kept as a display-shaped input until the pressure decomposition estimates are
available at solution level. -/
end CKN.Core.Step3
