module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.GramEstimates
public import Mathlib.Analysis.CStarAlgebra.Matrix
@[expose] public section
/-!
# Variational perturbation of the padded positive-two energy

A bound on the quadratic form of the actual difference matrix controls the
square root of the selected positive spectral energy. The proof uses the full
positive spectral lift and applies in dimensions zero and one as well.
This supplies the perturbation step needed by spectral hub separation.
-/
namespace KKPAsymptotic
open Matrix WithLp
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A B E X : Matrix V V ℝ}
open scoped Matrix.Norms.L2Operator
end KKPAsymptotic
