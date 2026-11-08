/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

VENDORED BASE MODULE.  This file is copied verbatim (apart from its import
paths and this header) from the author's Version 2.0 formalization at
https://github.com/DiarHaidary/Nelson-Nguyen-conjecture-upper-bound-palomar
(`SparseFockFormal/MatrixTail.lean`).  The sketch distribution, the Parseval-frame
encoding of `U`, the finite-probability API and the operator-norm/trace
bridge are unchanged between Version 2.0 and Version 3.0 of the manuscript,
so they are reused rather than reproved.
-/
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.vce179a4b20de.SparseStackV3.Base.SparseStackDistribution
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.vce179a4b20de.SparseStackV3.Base.FiniteProbability
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace SparseFock
namespace MatrixTail
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open ParsevalFrame SparseStackModel
universe u_m u_n
open SparseStackDistribution
end
end MatrixTail
end SparseFock
