import Examples.wcook04__plectis_erdos_lean.Dependencies.v5976c22e5df4.ErdosProblems.Erdos1049.QBinomialUnitIdentity
import Mathlib
set_option pp.unicode.fun true
/-! # The missing free-variable finite source transform
The variable z is independent of q.
Consequently the identity can be specialised in any commutative ring,
including a Laurent polynomial ring; it is not limited to z=q^alpha with
alpha a natural number. The proof uses only two finite q-binomial expansions.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Finset
open scoped BigOperators
variable {R : Type*} [CommRing R]
end ErdosProblems.Erdos1049.PaperR12
