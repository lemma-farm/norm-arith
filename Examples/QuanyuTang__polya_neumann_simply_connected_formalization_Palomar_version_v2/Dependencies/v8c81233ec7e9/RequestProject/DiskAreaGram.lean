module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.DiskHarmonicModes
/-!
# The physical area Gram matrix of harmonic disk monomials

The already proved gradient Green identity determines the area Gram
matrix by differentiation of the powers with exponents increased by one.
This is the physical area integral, without an assumed polar integration
formula. It supplies the monomials used for the regular Neumann mass
forcing estimates.
-/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open MeasureTheory Set Metric Real
open scoped ComplexConjugate
end PolyaNeumann
end
