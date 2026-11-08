module
public import Examples.sthubbar__goldbach_lean.Dependencies.vb526e0fdac5e.LeanLab.Halupczok2012.U1462Pointwise
/-!
# P0077 Halupczok 2012, `SingSeriesTails` PROVED, unit U-1462

AI wrote the Lean code, Claude, run 20261022T0403Z-7595. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

* `tail_sum_sq_le`: the TAIL sum, squared, is at most
  `log² n · z^{-2σ} Kc³ (Y₁ + n^{2σ}) · (Y₁ (1 + log N)³ + N²)`; by Cauchy-Schwarz over `q`,
  `sum_q_abs_sq_le` and `divisor_moment` of U-1439, `tail_pointwise` and `sum_Hs_sq_le`.
* `euler_sum_le`: the EULER sum is at most `Y₁ z^{-σ} Kc² (1 + log N)`; by `euler_pointwise` and
  `sum_Hs_div_totient_le`.
* `singSeriesTails_holds : SingSeriesTails`. PROVED, no cited input, with `σ = 1/12` and
  `D = 12 (A + 3)`.
* `singSeriesApprox_holds : SingSeriesApprox`. PROVED.
* `theorem2Zeroed_U1462`: the F-0008 repair CONDITIONAL ON `Theorem3` and `Theorem5` only.
-/
@[expose] public section
namespace LeanLab.Halupczok2012
open Finset Filter Topology
end LeanLab.Halupczok2012
