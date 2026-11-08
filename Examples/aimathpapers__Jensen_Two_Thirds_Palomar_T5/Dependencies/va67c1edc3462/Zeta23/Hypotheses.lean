/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Hypotheses.lean — the hypothesis ("axiom") boundary.

Canonical text: the paper.

PRINCIPLE: the fields of PaperInputs are PUBLISHED, CLASSICAL inputs,
stated in the paper's own form with the paper's equation labels. Everything the paper itself derives
(lem:poisson, prop:block, prop:tail, [eq:PiPfacts], [eq:Bdef], prop:trace, thm:traces, §6, taper facts
[eq:phinorms]–[eq:psiints], …) is a proof obligation and must NOT be added here. There are NO Lean
axiom declarations anywhere in this project: hypotheses are fields of the Prop-valued structure
PaperInputs, which every headline theorem takes as an explicit argument, so #print axioms stays at
{propext, Classical.choice, Quot.sound} and the trust boundary is exactly this file.

Every field below: docstring = paper label + verbatim paper statement + literature source + any
deviation in shape (∃-constant form unless the constant is load-bearing).
-/
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.va67c1edc3462.Zeta23.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open scoped BigOperators ArithmeticFunction ComplexConjugate ContDiff
open Complex MeasureTheory Set
noncomputable section
namespace Zeta23
/-! ## H-EF — Weil's explicit formula in the paper's spectral form  [prop:EF], [eq:EF], [eq:Wdef] -/
end Zeta23
