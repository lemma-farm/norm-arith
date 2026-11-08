/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], bound for 𝓔₂ (§5.3).  Statement consumed by
Zeta23/PrimeSideA/Ends.lean.
Substrate: Zeta23/PrimeSideA/EndsWeighted.lean; 1-D estimates N1/N2 from
Zeta23/PrimeSideA/EndsNu.lean.
-/
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.veff4e711c6f1.Zeta23.PrimeSideA.EndsNu
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
namespace Zeta23
namespace PrimeSide
section Assembly
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}
end Assembly
section Bounds
variable (cϱ lam : ℝ)
end Bounds
end PrimeSide
end Zeta23
