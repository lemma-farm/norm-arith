module
public import Examples.sthubbar__goldbach_lean.Dependencies.v6400253cb469.LeanLab.Halupczok2012.U1460SingSeriesProof
/-!
# P0077 Halupczok 2012, `SingSeriesApprox` reduced to two explicit tail inequalities, U-1460

AI wrote the Lean code, Claude, run 20261022T0003Z-15508. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

`SingSeriesTails` fixes the choice in `SingSeriesApprox`: `Z` is the set of squarefree
`s ≤ min(L^D, X₁)`, and `g_s = gW n (primeFactors s)`, the Ramanujan weight with the 2 adic
factor. It asserts only the two inequalities, TAIL and EULER, for this explicit choice.

* `abs_gW_le_one`: `|gW n t m| ≤ 1`. PROVED.
* `gS_periodic`: `g_s` is `s`-periodic for squarefree `s`. PROVED.
* `singSeriesApprox_of_tails : SingSeriesTails → SingSeriesApprox`. PROVED.
* `theorem2Zeroed_of_tails`: the F-0008 repair CONDITIONAL ON `Theorem3`, `Theorem5` and
  `SingSeriesTails`.
-/
@[expose] public section
namespace LeanLab.Halupczok2012
open Finset
end LeanLab.Halupczok2012
