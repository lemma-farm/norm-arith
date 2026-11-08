module
public import Mathlib
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.SUNet
set_option autoImplicit false
@[expose] public section
/-!
# Entry U, part 4: Theorem U(1) — `U_net`

* `ivOK_zmod`: for admissible `q` (prime factors `≥ s - 1`), `iv i = i⁻¹` inverts `1, …, s-2` in
  `ℤ/qℤ` (no reduction to primes is needed: Lemma T_s holds over every ring in which the place
  differences are units).
* `isNet0_of_kernel`: Niederreiter's counting argument for `s` coordinates — if a vector whose
  first `d c` digits vanish in every coordinate is zero, the point set is a `(0,m,s)`-net.
-/
namespace Z3NetU.Proofs
open Polynomial Finset Matrix Z3NetU
noncomputable section
end
end Z3NetU.Proofs
