module
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FDsep
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FTsk
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FRemK
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Entry F, stage 6: `prop:4DK2`, the design `A♯` in dimension four

* `As_residual_core`: the places `(0, -1, ∞, 1)` are admissible over `ℤ[1/10]` and `(λ', U')` of
  `app:designs` solves the residual problem of `A♯`; the identities are checked in `ℚ` through
  the injective map `ℤ[1/10] → ℚ`;
* `As_unit_core`, `As_net_core`: `cor:tsk`;
* `As_sep_core`: `lem:Ss` with the bound `BAs q`; for `7 ≤ q ≤ 21` (`gcd(q, 10) = 1`) every
  step is checked in the kernel, for `q ≥ 23` the backward coordinates of every step give a
  quadratic in `q - 23` with nonnegative coefficients (checked in the kernel).
-/
namespace Z3NetF.Proofs.As
open Finset Z3NetF
end Z3NetF.Proofs.As
