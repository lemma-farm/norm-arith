-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.Interface.LieWord
public import Mathlib.Analysis.Calculus.VectorField
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace Hormander
open Hormander.Interface
/-- Evaluation of a Lie word on vector fields over an arbitrary real normed space `E`: the same
recursion as `Hormander.Interface.LieWord.eval`, with `Fin N → ℝ` replaced by `E`. -/
def lieWordEval {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Fin (k + 1) → E → E) : LieWord k → E → E
  | .generator i => X i
  | .bracket p q => VectorField.lieBracket ℝ (lieWordEval X p) (lieWordEval X q)
end Hormander
