module
public import Examples.sthubbar__goldbach_lean.Dependencies.vb526e0fdac5e.LeanLab.Halupczok2012.U1439Combin
public import Examples.sthubbar__goldbach_lean.Dependencies.vb526e0fdac5e.LeanLab.Halupczok2012.NonCoprime
/-!
# P0077 Halupczok 2012, Theorem 2 reduced to Theorem 5 and the main term step, unit U-1439

AI wrote the Lean code, Claude, run 20261021T1603Z-28836. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

The paper proves Theorem 2 by writing the ternary sum as `∑_{p₁} log p₁ · binSum(n - p₁)` and
splitting `binSum(n - p₁) - T(n,q,a) Y₁ Y₂ / …` into

* the BINARY PART `∑_q |∑_{p₁ ≡ a (q)} log p₁ (binSum(n - p₁) - 𝔖(n - p₁) Y₂)|`, bounded from
  the Perelli-Pintz mean square, the paper's Theorem 5, and its Lemma 1; and
* the MAIN TERM PART `∑_q |∑_{p₁ ≡ a (q)} log p₁ 𝔖(n - p₁) - 𝔗(n,q,a) Y₁|`, bounded from the
  Perelli-Pintz-Salerno short interval Bombieri-Vinogradov theorem, the paper's Theorem 3, and
  the singular series computation with the Chinese remainder theorem.

Here:

* `binaryPart`: the binary part is `≪ Y₁ Y₂ L^{-A}`. PROVED CONDITIONAL ON `Theorem5` only.
  The paper's Lemma 1 is NOT needed: in Theorem 2, `Q ≪ Y₁ X₁^{-1/2} L^{-B}` gives `Q² ≪ Y₁`,
  so the elementary divisor moment `divisor_moment` and Cauchy-Schwarz suffice.
* `theorem2_of_inputs : Theorem5 → MainTermMV → Theorem2`. CONDITIONAL ON both.
* `theorem2Zeroed_of_inputs`: the F-0008 repair, the all-`q` form with `T0`, CONDITIONAL ON the
  same two inputs instead of the paper's Theorem 2.

`MainTermMV` is still the paper's own main term step, its displays after (10); its standard
input is `Theorem3`, Perelli-Pintz-Salerno, stated below; `U1457SingSeries` derives
`MainTermMV` from `Theorem3` and the singular series facts proved in `U1462Tails`.
The lab's `PNTPort.BV.BombieriVinogradov` is for `ψ(x; q, a)` over `[1, x]`; it does not give
intervals of length `Y₁ = X₁^{3/5+ε}`, so it cannot replace `Theorem3`.
-/
@[expose] public section
namespace LeanLab.Halupczok2012
open Finset
/-! ### The cited inputs -/
end LeanLab.Halupczok2012
