/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition

/-!
# Dyadic rescalings of a bump

For `h : ℝ⁴ → ℝ` we set `scaledShell h n z = (2^n)^3 h(S^{2^n} z)` (`S^c = parabolicDilate c`).
If `h` is smooth and supported in the unit parabolic ball, then `scaledShell h n` is smooth and
supported in `‖z‖_𝔰 ≤ 2^{-n}`, its derivatives obey the exact scaling
`D_J (scaledShell h n) = (2^n)^{3 + |J|_𝔰} (D_J h)(S^{2^n} ·)`, and its moments scale exactly.

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The `n`-th dyadic rescaling `z ↦ (2^n)^3 h(S^{2^n} z)` of `h`. -/
def scaledShell (h : ParabolicSpace → ℝ) (n : ℕ) (z : ParabolicSpace) : ℝ :=
  ((2 : ℝ) ^ n) ^ 3 * h (parabolicDilate (2 ^ n) z)

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem scaledShell_eq_smul_comp (h : ParabolicSpace → ℝ) (n : ℕ) :
    scaledShell h n = ((2 : ℝ) ^ n) ^ 3 • (h ∘ parabolicDilateCLM (2 ^ n)) := by
  funext z
  simp [scaledShell]

theorem contDiff_scaledShell {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h) (n : ℕ) :
    ContDiff ℝ ∞ (scaledShell h n) := by
  rw [scaledShell_eq_smul_comp]
  exact (hh.comp (parabolicDilateCLM (2 ^ n)).contDiff).const_smul (((2 : ℝ) ^ n) ^ 3)

theorem scaledShell_eq_zero {h : ParabolicSpace → ℝ}
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) {n : ℕ} {z : ParabolicSpace}
    (hz : (2 : ℝ)⁻¹ ^ n < parabolicNorm z) : scaledShell h n z = 0 := by
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have : 1 < parabolicNorm (parabolicDilate (2 ^ n) z) := by
    rw [parabolicNorm_parabolicDilate hc.le]
    rw [inv_pow, inv_lt_iff_one_lt_mul₀ hc] at hz
    linarith
  simp [scaledShell, hs _ this]

                                                              
                                                                                              
                                                                                  
                                        

                                                                                                
                                    
                                                                                            
                                             
                                                   
                                           
                                                                     
                                                            
                                                 
                                                                             
                                                                       
                                                                         
                     
                                                                        
                                                                                         
                 
                           

end RegularityStructures

end
