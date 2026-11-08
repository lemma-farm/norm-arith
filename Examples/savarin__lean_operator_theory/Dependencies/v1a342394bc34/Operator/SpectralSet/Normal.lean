/-
# Polynomials in a normal element — the sup-norm bound

For a normal element `a` of a C*-algebra and a compact set `K ⊇ σ(a)`,
`‖p(a)‖ ≤ sup_{z ∈ K} ‖p(z)‖` for every polynomial `p`: `p(a)` is normal, so its norm is its
spectral radius, and `σ(p(a)) = p(σ(a)) ⊆ p(K)` by the spectral mapping theorem.

## Main declarations

* `norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval` — the same bound under the
  weaker hypothesis that the single element `p(a)` is normal.
* `norm_aeval_le_polynomialSupNorm_of_isStarNormal` — the bound above, in any C*-algebra.

Consumers: unitaries with `K` the closed unit disk (`Crouzeix/VonNeumann.lean`), and normal
operators on a Hilbert space with `K = closure W(A)` (`Crouzeix/Palencia.lean`).
-/
import Mathlib
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.VonNeumann
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Polynomial
