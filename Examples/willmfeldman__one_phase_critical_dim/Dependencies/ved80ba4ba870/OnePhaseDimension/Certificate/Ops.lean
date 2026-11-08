/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module
public import Examples.willmfeldman__one_phase_critical_dim.Dependencies.ved80ba4ba870.OnePhaseDimension.Certificate.Eval
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Soundness of the operations on graph keys

For every operation of the certificate engine we prove that it acts on values as intended:

* `Key.eval_sortAll`, `Key.eval_swapX`, `Key.eval_normalize`: sorting and the exchange of the
  two copies of `X` do not change the value (sorting uses the symmetry of `A` and `X`);
* `Key.eval_reduce`, `Key.eval_canon`: the trace reductions `tr A⁰ = 5`, `tr A = 0`,
  `tr A² = 1` and the vanishing of traces of `X` hold on admissible data;
* `Key.eval_permSlots`: renaming the free slots;
* `Key.eval_mul`: the tensor product evaluates to the product of the values;
* `Key.eval_contract`: contraction of two free slots is the sum over a common index;
* `Key.bounded_normalize`: normalization preserves the bound on the packed digits;
* `Poly.eval_merge`, `Poly.eval_mergeAll`, `Key.eval_term`: the polynomial operations.

All statements are on the data `CertData`; where symmetry of `A` and `X` or the trace
reductions are used, the data is assumed `CertData.Admissible`.
-/
@[expose] public section
namespace OnePhaseDimension.Certificate
open Finset
/-! ### Relabelling copies of `X` -/
namespace Key
end Key
/-! ### Products -/
namespace Key
end Key
/-! ### Contraction -/
theorem sum_comm₃ (H : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ a, ∑ b, ∑ c, H a b c = ∑ b, ∑ c, ∑ a, H a b c := by
  rw [Finset.sum_comm]
  exact sum_congr rfl fun b _ => Finset.sum_comm
namespace Key
end Key
/-! ### Boundedness of packed digits -/
namespace Key
end Key
/-! ### Polynomials -/
namespace Poly
end Poly
end OnePhaseDimension.Certificate
