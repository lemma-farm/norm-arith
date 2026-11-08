module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.DiskAreaGram
/-!
# Bessel estimates for physical area moments on the disk

The holomorphic and antiholomorphic monomials form two separate
orthogonal families in the actual area L² space. Their normalization
gives the weighted mass-moment estimate used in the Neumann equation.
The two zero modes are not combined into one orthonormal family.
-/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace
end PolyaNeumann
end
