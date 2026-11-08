module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.OrthogonalCompression
@[expose] public section
/-!
# Orthogonal support splitting of the positive-two energy

The hub bipartite block and the residual compression act on orthogonal
subspaces. Their combined positive-two energy is at most the sum of their
separate positive-two energies, proved variationally with the same PSD lift.
-/
namespace KKPAsymptotic
open Matrix
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A B P : Matrix V V ℝ}
end KKPAsymptotic
