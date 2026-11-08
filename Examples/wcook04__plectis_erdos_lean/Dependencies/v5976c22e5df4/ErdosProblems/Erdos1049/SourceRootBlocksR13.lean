import Examples.wcook04__plectis_erdos_lean.Dependencies.v5976c22e5df4.ErdosProblems.Erdos1049.SourceRootCarriesR13
import Mathlib
set_option pp.unicode.fun true
/-!
# Global residue-block cancellation at the literal source indices


A weight depending on floor((2*n+s)/ell) is constant on the nonzero
local residues. This gives cancellation for every such weight, including
the harmonic weight that occurs in the cleared B numerator.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators
section Field
variable {K : Type*} [Field K]
end Field
end ErdosProblems.Erdos1049.PaperR13
