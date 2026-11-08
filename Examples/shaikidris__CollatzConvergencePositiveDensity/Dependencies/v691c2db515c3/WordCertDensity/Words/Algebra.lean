/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Inverse-prefix word algebra

A word is listed from its root outward. Its affine evaluator maps the final
source back to the root: the first listed letter is the outermost affine map.
These rational identities do not assert integral or positive realization.
-/
@[expose] public section
namespace WordCertDensity
/-- Positive valuations; each consuming API specifies its word orientation. -/
abbrev ValuationWord := List ℕ+
namespace ValuationWord
end ValuationWord
end WordCertDensity
