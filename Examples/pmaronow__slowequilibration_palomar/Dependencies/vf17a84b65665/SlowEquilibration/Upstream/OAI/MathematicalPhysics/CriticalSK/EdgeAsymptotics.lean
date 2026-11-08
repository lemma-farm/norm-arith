-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Lean module/public-import adaptation).
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.Upstream.OAI.MathematicalPhysics.CriticalSK.GOESpectrum
set_option autoImplicit false
@[expose] public section
namespace OAI
noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open scoped BigOperators NNReal
open scoped BigOperators
open scoped BigOperators InnerProductSpace
open Module
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
namespace CriticalSK
open scoped Topology
open scoped Topology
end CriticalSK
end
end OAI
