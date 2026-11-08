module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.va8d8f04859e6.LeanLab.HeathBrown1985.PrimePowers
public import Examples.sthubbar__goldbach_lean.Dependencies.va8d8f04859e6.LeanLab.HeathBrown1985.Sigma1
/-!
P0096 Heath-Brown 1985, pages 56 to 58, the end of section 3 and section 4: Theorem 1 from
the bound for Σ₃ on page 56 and the main term on page 57.
STATED: `BoundSigma3`, page 56, `Σ₃² ≪ x⁴ L¹³ Q⁻¹`; `MainTerm4`, page 57, the asymptotic 4.1
combined with the case `t = 2` of 2.2, `Σ_m |Σ_{n ≤ x} Λ_Q(n) Λ(m - n) - x 𝔖(m)| ≪ x² L⁴ Q⁻¹`.
PROVED here: 3.9, `Σ ≪ x² Q^{-1/2} L⁸`, from 3.2, the Σ₂ bound and `BoundSigma3`;
`theorem1_of`, Theorem 1 from `BoundSigma3`, `MainTerm4` and Siegel-Walfisz 1.1, with
`B = 2C + 16` and the prime power error from PrimePowers.lean.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
end LeanLab.HeathBrown1985
