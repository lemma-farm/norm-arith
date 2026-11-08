/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramDefs
public import Phi43.BPHZ.TreeI3PsiPointwise
public import Phi43.BPHZ.TreeI3PsiSigma
public import Phi43.BPHZ.TreeI3PsiDiagramUniform

/-!
# Basic facts for the diagrams of `I(Ψ³)Ψ²`

* evenness of `Q` when `Q(x) = ∫ J(x + w) J(w) dw`;
* the covariance with a loss `δ` of the exponent, `|Q x| ≤ B 3^δ s(x)^(-(1+δ))`
  (on the slab `|t| ≤ 4`, no support hypothesis on `Q`);
* the flip `s(b - a)^(-p) ≤ 2^p s(a - b)^(-p)` of a centred power.
-/

public section

open MeasureTheory

namespace RegularityStructures

                                                       
                                                                                                    
                      
               
                                                                          
                                 
          
                                                                    
                                      
                                                     
                                

                                                                             
                                                                              
                                                                                        
                                                                       
                                                               
                                                           
                                                 
                                                                        
                                          
                                                                              
                                                                              
                                                               
                                                                                          
                                                          
                                                                       
                    

                                                                     
theorem torusParabolicSize_rpow_neg_flip_le' {p : ℝ} (hp : 0 ≤ p) {a b : SpaceTime}
    (h : 0 < torusParabolicSize (a - b)) :
    torusParabolicSize (b - a) ^ (-p) ≤ 2 ^ p * torusParabolicSize (a - b) ^ (-p) := by
  have hneg := torusParabolicSize_neg_le_two_mul (b - a)
  rw [neg_sub] at hneg
  have hy : 0 < torusParabolicSize (a - b) / 2 := by linarith
  have h1 : torusParabolicSize (b - a) ^ (-p) ≤ (torusParabolicSize (a - b) / 2) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hy (by linarith) (neg_nonpos.2 hp)
  have h2 : (torusParabolicSize (a - b) / 2) ^ (-p) = 2 ^ p * torusParabolicSize (a - b) ^ (-p) := by
    rw [Real.div_rpow h.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg h.le]
    field_simp
  exact h1.trans h2.le

/-- Two centred powers with the same centre merge. -/
theorem singularPow_mul_self (a b : ℝ) (c w : SpaceTime) (h : 0 < torusParabolicSize (c - w)) :
    singularPow a c w * singularPow b c w = singularPow (a + b) c w := by
  unfold singularPow
  rw [← Real.rpow_add h]
  congr 1; ring

end RegularityStructures

end
