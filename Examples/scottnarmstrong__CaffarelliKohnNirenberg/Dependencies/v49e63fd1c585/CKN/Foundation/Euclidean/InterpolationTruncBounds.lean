-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.InterpolationBasic
set_option autoImplicit false
set_option warningAsError true
/-!
# Pointwise truncation bounds

The Marcinkiewicz interpolation argument used for the Caffarelli–Kohn–Nirenberg
program (CKN 1982) controls the two pieces of a function `f` cut at a level
`l > 0` by the single power `|f| ^ p`, for `1 < p < 2`.  This file records the
two elementary pointwise inequalities that make that reduction work, stated for
the `ℝ≥0∞`-valued modulus `absE f x = ENNReal.ofReal |f x|`.

Above the level the first inequality bounds the modulus itself by
`l ^ (1 - p) * |f| ^ p`; below the level the second bounds its square by
`l ^ (2 - p) * |f| ^ p`.  Both are pointwise in `x` and depend only on the
scalar comparison of `|f x|` with `l`; the exponents `l ^ (1 - p)` and
`l ^ (2 - p)` are real powers.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic
end CKN.Foundation.Euclidean
