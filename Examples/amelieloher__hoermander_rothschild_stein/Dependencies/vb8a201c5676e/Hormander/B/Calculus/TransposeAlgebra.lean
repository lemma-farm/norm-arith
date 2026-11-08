-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.vb8a201c5676e.Hormander.B.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace Hormander.B
/-- Transposition reverses a product. -/
theorem bilinearTranspose_comp {N : ℕ} {A At B Bt : Operator N}
    (hA : HasBilinearTranspose A At) (hB : HasBilinearTranspose B Bt) :
    HasBilinearTranspose (A.comp B) (Bt.comp At) := by
  intro u v
  exact (hA (B u) v).trans (hB u (At v))
/-- Commuting through a two-factor product. -/
theorem operatorComm_comp {N : ℕ} (P A B : Operator N) :
    operatorComm P (A.comp B) =
      (operatorComm P A).comp B + A.comp (operatorComm P B) := by
  ext u x
  simp [operatorComm]
end Hormander.B
