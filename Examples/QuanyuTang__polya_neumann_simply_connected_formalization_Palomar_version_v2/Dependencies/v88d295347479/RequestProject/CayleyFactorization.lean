module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.Driven
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.Cayley
/-!
# Factorization through the Cayley transform (Lemma 4.17)

Let `y` be a periodic solution of the driven transport equation `y' = C_E y - (i/√2) g e₀`
(as in Lemma 4.10), `v = y(0)`, and assume `ker (I - V_E) = 0`.  Then
* `O_E^* g` lies in the domain `ran (I - V_E)` of the Cayley transform `K_E`, and
  `K_E O_E^* g = -√2 (I + V_E^*) v`;
* with `h = √2 ⟨e₀, y⟩` the boundary trace, `2 h + i (T_E - T_E^*) g = -O_E K_E O_E^* g`
  on `[0, L]`.

At a Neumann-nonresonant energy the paper identifies `h_a = N(E) g_a` for Herglotz data, so the
second identity is the factorization `A_E g_a = -O_E K_E O_E^* g_a` of Lemma 4.17, with
`A_E = 2 N(E) + i (T_E - T_E^*)`.  The identification `N(E) g_a = h_a` (which needs the
Helmholtz boundary value problem) is not formalized; it is replaced by the trace `h` itself.
-/
@[expose] public section
open MeasureTheory Set
open scoped ComplexConjugate Real
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
end
