module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.Herglotz
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.NeumannEigenspace
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.CayleyFactorization
/-!
# The fixed space of the monodromy and Herglotz-compatible traces (Lemma 10.5)

The paper proves `dim ker(V_E - I) ≤ dim ker(A_N - E)` in two steps:

1. (pairing step, proved here) if `V_E v = v`, the observation `f₀ = O_E v = ⟨e₀, W_E(·) v⟩`
   is a Lipschitz closed boundary function orthogonal to the conormal trace `g_a` of every
   Herglotz wave (`observation_mem_compatibleTraces`, from Lemma 4.4 in `Herglotz.lean`);
2. (Cauchy reconstruction, Lemma 4.8) every such compatible boundary function `h` is the
   Dirichlet trace of a unique Helmholtz solution with zero Neumann data, i.e. of a Neumann
   eigenfunction, depending linearly on `h`.

We formalize the space of compatible traces (`compatibleTraces`) and deduce the injective map
from the fixed space into the Neumann eigenspace from any linear reconstruction map that only
kills traces vanishing on `[0, L]` (`fixedSpace_to_neumannEigenspace_of_reconstruction`),
using the injectivity of the observation map (Lemma 10.4).
-/
@[expose] public section
open MeasureTheory Set Filter
open scoped ComplexConjugate Real
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
