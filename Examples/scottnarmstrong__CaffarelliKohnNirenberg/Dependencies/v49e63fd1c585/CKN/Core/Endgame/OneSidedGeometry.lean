-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Topology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option warningAsError true
/-!
# One-sided cylinder covering

The truncated time shift of Step 2 in the proof of `thm:A`. For a cylinder
`𝒞_ϱ(w)` meeting the one-sided cylinder of admissible centres, and a point
`w'` of the intersection, the new centre is
`w'' = (x_{w'}, min {t_w + ϱ², 0})`: the spatial centre of `w'` and the
forward time shift truncated at the top face. It stays among the admissible
centres, and `𝒞_ϱ(w) ∩ {t ≤ 0} ⊆ 𝒞_{2ϱ}(w'')`. The covering itself needs no
upper bound on the radius.
-/
open Set
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Endgame
end CKN.Core.Endgame
