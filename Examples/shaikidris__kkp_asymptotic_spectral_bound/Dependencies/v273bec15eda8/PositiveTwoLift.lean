module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.SpectralLift
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.Basic.Spectrum
@[expose] public section
/-!
# The lift of the two largest positive ordered eigenvalues

The selection pads missing dimensions by zero. Its Frobenius mass is exactly
the existing ordered spectral statistic `BN.F`, including empty and singleton
index types. This connects the matrix estimates to the original graph statistic.
-/
namespace KKPAsymptotic
open Matrix
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : Matrix V V ℝ}
end KKPAsymptotic
