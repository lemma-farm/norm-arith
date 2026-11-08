-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Caccioppoli.Caccioppoli
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step3.PressureDecayTShape
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step3.ThetaDecay
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step3
open CKN
/-! The final provider-shaped export of the one-step theta estimate.  The two
remaining analytic producers are kept at their solution-level, arbitrary-scale
shapes; the unconditional annular estimates and Caccioppoli estimate are
discharged in the body. -/
end CKN.Core.Step3
