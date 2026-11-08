module
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.FNie
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Entry F, part 3: graph forms with depths `K`, `lem:box` and the gauge moves

* `graphGenK_apply`: the entries of a graph-form generator matrix at column `pre K e + l`.
* `graphForm_of_box` (paper, `sec:prelim`): an invertible `K`-box makes any digital point set a
  graph form.
* `box_minor_self`: the `K`-box of a graph form is the identity.
* `box_minor` (`lem:box`): after reindexing rows and columns (unit rows/selected columns first),
  the box matrix is `[[1, 0], [*, D]]` with `D` the reduced box matrix; the sign is that of a
  permutation that depends only on `K`, `d` and the squaring bijection.
* `gauge_diag`, `gauge_LU`, `gauge_scale3` and the net consequences `gauge_net`, `gauge_net3`.
-/
namespace Z3NetF.Proofs
open Matrix Finset
noncomputable section
variable {R : Type*} {s m : ℕ}
section reduce
variable (K d : Fin s → ℕ)
end reduce
section gauge
variable [CommRing R] (K d : Fin s → ℕ)
end gauge
end
end Z3NetF.Proofs
