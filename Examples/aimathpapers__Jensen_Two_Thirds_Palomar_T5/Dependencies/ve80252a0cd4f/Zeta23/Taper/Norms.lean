/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.ve80252a0cd4f.Zeta23.Taper.Basic
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
namespace Zeta23
namespace Taper
section Norms
variable {ϱ : ℝ → ℝ} {L w : ℝ}
end Norms
/-! ### [eq:abdef]: "`1 − 2w/L ≤ b ≤ a ≤ 1`" -/
section AB
variable {ϱ : ℝ → ℝ} {L w : ℝ}
end AB
end Taper
end Zeta23
