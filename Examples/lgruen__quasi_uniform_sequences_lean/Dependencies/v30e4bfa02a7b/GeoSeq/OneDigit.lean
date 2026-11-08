/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.GeoSeq.Defs
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# GeoSeq stage S0 proofs: the one-digit certificate (`rem:onedigit`) and the arithmetic core of
`thm:WF`

* `gapNum1_zero`, `gapNum1_eq`: closed form of `f_1(e, σ)` over `ℤ/qℤ` (the difference
  `val(r + σ) - val(r)` takes exactly the values `val σ` and `val σ - q` for `σ ≠ 0`).
* `rem:onedigit`: `F1_one_neg` (`f_1(1, -A) = 1 - (A+1)/q`), `F1_one_one` (`f_1(1, 1) = 0`),
  `F1_neg` (`f_1(-1, σ) = f_1(1, -σ)`), and `F1_zero_half` (`f_1(0, ±1/2) = (p-3)/(2p)`).
* `WF_coord1`: the coordinate-1 part of the proof of `thm:WF`, for every prime `p ≥ 5`: with the
  frozen responses `O_1^{(l)} = 0`, `X_{1←0}^{(l)} = ±1/2` of `lem:WFlaw`, every step
  `e ∈ {-1,0,1}² ∖ {0}` has `f_1(e_1, σ_1) ≥ (p-3)/(2p)`; `WF_LB1` adds the coordinate-0 term.
* `gapNum_one`: the general `gapNum` at depth `j = 1` is `gapNum1`.
* `WF_coord1_p7`: the same finite statement at `p = 7` by kernel `decide` (independent check).
-/
namespace GeoSeq
open Finset
end GeoSeq
