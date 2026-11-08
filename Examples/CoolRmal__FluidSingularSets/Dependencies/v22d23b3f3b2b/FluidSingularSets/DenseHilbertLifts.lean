-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.LinearAlgebra.Isomorphisms
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Extending genuine bounded Hilbert lifts from dense data

Orthogonal projection off the actual operator kernel selects the minimal-norm
lift linearly on the range. Genuine bounded lifts on a dense data subspace
therefore extend to a continuous linear right inverse on the full target.
No closed-range or arbitrary-data preimage premise is used.
-/
@[expose] public section
open Set Filter
open scoped Topology NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FluidSingularSets
section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
private instance kernel_hasOrthogonalProjection (D : E →L[ℝ] F) :
    (D.ker).HasOrthogonalProjection := by
  let K : ClosedSubmodule ℝ E := ⟨D.ker, D.isClosed_ker⟩
  exact inferInstanceAs K.HasOrthogonalProjection
end
end FluidSingularSets
