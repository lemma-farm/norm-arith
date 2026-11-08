/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.PDE.TorusLift
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth functions are dense in `C(T³, ℝ)`

The functions on `T³` with smooth periodic lift form a subalgebra of `C(T³, ℝ)`
(`smoothSubalgebra`). It contains the coordinate functions `cos 2πxᵢ` and `sin 2πxᵢ`, which
separate the points of `T³`, so it is dense by the Stone–Weierstrass theorem
(`exists_smooth_near`).
-/
open scoped ContDiff
public section
namespace RegularityStructures.PDE
open Real Set
end RegularityStructures.PDE
end
@[expose] public noncomputable section
namespace RegularityStructures.PDE
end RegularityStructures.PDE
end
public section
namespace RegularityStructures.PDE
open Real Set
/-- Points of `ℝ³` with the same image in `T³` differ by an integer vector. -/
theorem exists_int_of_torusProj_eq {a b : Fin 3 → ℝ} (hab : torusProj a = torusProj b)
    (i : Fin 3) : ∃ n : ℤ, b i = a i + n := by
  have h := congrFun hab i
  simp only [torusProj] at h
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h)
  exact ⟨n, by simp at hn; linarith⟩
end RegularityStructures.PDE
end
@[expose] public noncomputable section
namespace RegularityStructures.PDE
open Real
end RegularityStructures.PDE
end
public section
namespace RegularityStructures.PDE
open Real Set
end RegularityStructures.PDE
end
