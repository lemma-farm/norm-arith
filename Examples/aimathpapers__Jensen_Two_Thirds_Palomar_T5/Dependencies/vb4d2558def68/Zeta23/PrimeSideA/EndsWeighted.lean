/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PrimeSideA/EndsWeighted.lean

Substrate for the 𝓔₂ bound [lem:ends], shared with EndsNu.lean (the
1-D estimates N1/N2): log⁺/√ facts, pointwise ν-bounds from NuBound, integrability of the
ψ-weighted ν integrals, and the grid-domination lemmas reducing Σ_{k<d} ψ(τ−τ_k) to
Σ_{j<d} ψ(Δ + jh), Δ = dist(τ, I).
-/
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.vb4d2558def68.Zeta23.PrimeSideA.EndsCore
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
namespace Zeta23
namespace PrimeSide
section Prelim
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}
end Prelim
section Weighted
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}
end Weighted
section Grid
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}
end Grid
end PrimeSide
end Zeta23
