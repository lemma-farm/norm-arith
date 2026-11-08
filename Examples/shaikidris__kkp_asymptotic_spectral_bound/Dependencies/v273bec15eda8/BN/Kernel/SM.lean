/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.Kernel.Data
@[expose] public section
/-!
# Sherman–Morrison formula for `𝒦`

The rank-one update `𝒦 = (𝒜 + VVᵀ/γ)⁻¹` expands as
`𝒜⁻¹ - e₀ e₀ᵀ / (γ + a₀)`, using `𝒜⁻¹ V = e₀` and `V 0 = a₀`.
-/
namespace BN
open Matrix
open scoped Matrix
noncomputable section
variable {k : ℕ} (t : Fin k → ℝ) (q : Fin k → ℝ)
end
end BN
