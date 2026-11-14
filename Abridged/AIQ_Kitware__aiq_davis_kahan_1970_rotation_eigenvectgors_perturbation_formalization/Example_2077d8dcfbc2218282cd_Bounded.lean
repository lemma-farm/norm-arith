module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Examples.Example_2077d8dcfbc2218282cd_Bounded ====
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Bound/inverse Sylvester estimates

This module isolates the exact dimension-free form of Davis--Kahan Theorem 5.1.
The Neumann construction and ideal-norm convergence are separated so that the
analytic difficulty is visible in the dependency graph.
-/
namespace TauCeti
namespace DavisKahan
namespace Sylvester
open scoped InnerProductSpace
universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
/-- Explicit bounded two-sided inverse data for an endomorphism. -/
structure BoundedInverseData (A : E →L[𝕜] E) where
  inv : E →L[𝕜] E
  left_inv : inv ∘L A = ContinuousLinearMap.id 𝕜 E
  right_inv : A ∘L inv = ContinuousLinearMap.id 𝕜 E
namespace BoundedInverseData

end BoundedInverseData

/-- The `n`th term in the Neumann construction for `A X - X B = C`. -/
noncomputable def sylvesterNeumannTerm
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) (n : ℕ) : F →L[𝕜] E :=
  (hA.inv ^ (n + 1)) ∘L C ∘L (B ^ n)

omit [CompleteSpace E] [CompleteSpace F] in
set_option linter.unusedVariables false in
/-- Operator-norm geometric bound for one Neumann term. -/
theorem norm_sylvesterNeumannTerm_le
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) (n : ℕ) 
    (h_TauCeti_DavisKahan_Sylvester_opNorm_pow_le : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E : Type v} [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) (n : ℕ), ‖T ^ n‖ ≤ ‖T‖ ^ n)
    :
    ‖sylvesterNeumannTerm hA B C n‖ ≤
      ‖hA.inv‖ * ‖C‖ * (‖hA.inv‖ * ‖B‖) ^ n := by
  change
    ‖((hA.inv ^ (n + 1)) ∘L C) ∘L (B ^ n)‖ ≤
      ‖hA.inv‖ * ‖C‖ * (‖hA.inv‖ * ‖B‖) ^ n
  have hleft :
      ‖(hA.inv ^ (n + 1)) ∘L C‖ ≤ ‖hA.inv ^ (n + 1)‖ * ‖C‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have houter :
      ‖((hA.inv ^ (n + 1)) ∘L C) ∘L (B ^ n)‖ ≤
        ‖(hA.inv ^ (n + 1)) ∘L C‖ * ‖B ^ n‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  calc
    ‖((hA.inv ^ (n + 1)) ∘L C) ∘L (B ^ n)‖
        ≤ ‖(hA.inv ^ (n + 1)) ∘L C‖ * ‖B ^ n‖ := houter
    _ ≤ (‖hA.inv ^ (n + 1)‖ * ‖C‖) * ‖B ^ n‖ :=
      mul_le_mul_of_nonneg_right hleft (norm_nonneg (B ^ n))
    _ ≤ (‖hA.inv‖ ^ (n + 1) * ‖C‖) * ‖B‖ ^ n := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (h_TauCeti_DavisKahan_Sylvester_opNorm_pow_le hA.inv (n + 1))
          (norm_nonneg C))
        (h_TauCeti_DavisKahan_Sylvester_opNorm_pow_le B n)
        (norm_nonneg (B ^ n))
        (mul_nonneg (pow_nonneg (norm_nonneg hA.inv) _) (norm_nonneg C))
    _ = ‖hA.inv‖ * ‖C‖ * (‖hA.inv‖ * ‖B‖) ^ n := by
      rw [pow_succ', mul_pow]
      ring

end Sylvester
end DavisKahan
end TauCeti