import Examples.wcook04__plectis_erdos_lean.Dependencies.v5976c22e5df4.ErdosProblems.Erdos1049.SourceRootBlocksR13
import Mathlib
set_option pp.unicode.fun true
/-!
# Actual all-index Omega cancellation for the literal cleared B



At an ell-th primitive root only denominators with ell | j survive.
Their precise values need not be divided by an integer: the global block
identity is valid for an arbitrary function of the cutoff floor. This
avoids a spurious division at a root and also works in positive characteristic
in the finite-field stage. Descent to Z[X] uses a primitive complex root,
the cyclotomic minimal polynomial, coprimality over Q[X], and monic descent.
Distinct cyclotomic polynomials are NOT assumed comaximal over Z[X].
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators
section Field
variable {K : Type*} [Field K]
end Field
end ErdosProblems.Erdos1049.PaperR13
