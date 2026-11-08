-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.Hedberg
set_option autoImplicit false
set_option warningAsError true
/-!
# The order-one Hardy--Littlewood--Sobolev estimate in dimension three

The exponent used by the pressure decomposition is `m = 5/2`, `s = 15`.
The proof is Hedberg's pointwise estimate followed by the strong maximal
estimate.  The a.e. maximal-data hypothesis is exposed so that zero data and
finite truncations can be handled by the consuming pressure lemma.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic
end CKN.Foundation.Euclidean
