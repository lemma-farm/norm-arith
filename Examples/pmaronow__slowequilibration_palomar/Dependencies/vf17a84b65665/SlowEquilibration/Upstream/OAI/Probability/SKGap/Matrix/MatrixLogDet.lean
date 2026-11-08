-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Lean module/public-import adaptation).
module
public import Mathlib
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.Upstream.OAI.Probability.SKGap.Model
set_option autoImplicit false
@[expose] public section
namespace OAI
section
noncomputable section
namespace SKGap.LogDet
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end SKGap.LogDet
end
end
end OAI
