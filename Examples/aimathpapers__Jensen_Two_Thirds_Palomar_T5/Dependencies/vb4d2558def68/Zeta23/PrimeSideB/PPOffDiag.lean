/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
  Bracketed labels ([prop:cross], [eq:Msplit], …) and section numbers (§5.4, …) refer to that paper.
-/
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.vb4d2558def68.Zeta23.PrimeSideB.PPKernel
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# [prop:PP] — the off-diagonal term 𝒪₁ (§5.4)

Consumed by `Zeta23/PrimeSideB/PP.lean` .  Everything needed is in
`Zeta23/PrimeSideB/PPKernel.lean`:
* `sub_mul_Aminus_eq` : for θ = y−y' ≠ 0,  θ·A⁻(y,y') = explicit combination of 8 terms
    trig(θ·cT)·M(y or y'),  trig ∈ {sin,cos}, c ∈ {1,2}, M ∈ {Cp,Sp,Cm,Sm} (half-line moments of Φ²);
* `abs_Cp_le` … `abs_Sm_le` : |M(y)| ≤ ∫Φ²;
* `MV_real` : |Σ_{n≠m} u_n v_m trig(c(y_n−y_m))/(y_n−y_m)| ≤ C·√(Σ2n u_n²)·√(Σ2n v_n²)  (H-MV + [eq:deltan]);
* `MV_size_le` : with {u,v} = {a, a·w}, |w| ≤ W:  that bound ≤ 2·C·W·Σ_{n≤X}Λ(n)².
So: split the sum below into the 8 MV-shaped sums (after dividing `sub_mul_Aminus_eq` by θ = log n − log m,
nonzero for n ≠ m ≥ 1 by injectivity of log), bound each by 2·C·(∫Φ²)·ΣΛ², total 16·C·(∫Φ²)·ΣΛ².
(Then PP.lean uses [eq:cheb1] ΣΛ(n)² ≪ X log X = XL and ∫Φ² = 2πbL ≤ 2πL to get 𝒪₁ ≪ L²X.)
-/
noncomputable section
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
namespace Zeta23
namespace PrimeSide
end PrimeSide
end Zeta23
