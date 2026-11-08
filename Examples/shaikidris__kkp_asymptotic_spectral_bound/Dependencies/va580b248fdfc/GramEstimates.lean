module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.GramInput
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.LowDegreeTransfer
@[expose] public section
/-!
# Rank-two Gram estimates for weighted deletion

These estimates supply the trace normalization and entrywise loss bounds for
the flat Gram step. They hold for actual positive semidefinite matrices;
weighted clique deletion itself is a separate combinatorial obligation.
-/
namespace KKPAsymptotic
open Matrix
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
end KKPAsymptotic
