-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Lean module/public-import adaptation).
module
public import Mathlib
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.Upstream.OAI.Probability.SKGap.Matrix.MatrixLogDet
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.Upstream.OAI.Probability.SKGap.Localization.FrobeniusSq
set_option autoImplicit false
@[expose] public section
namespace OAI
section
noncomputable section
namespace SKGap.LogDet
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def regularizedGram (γ : ℝ) (M : Matrix ι ι ℝ) := Mᵀ*M+γ • 1
end SKGap.LogDet
end
end
section
noncomputable section
namespace SKGap.LogDet
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end SKGap.LogDet
end
end
end OAI
