/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiCross
public import RegularityStructures.BPHZ.TreeI2Psi2DiagramMultiAlg

/-!
# Common notation for the difference bound of `I(Ψ²) Ψ²`

* `i2Psi2DiffF θ δ r r' d`: the target majorant
  `d^(-η) + d^(-2) (r^(2-η) + r'^(2-η)) + d^(-(2+2θ)) (r^(2-δ) + r'^(2-δ)) + r^(-η) + r'^(-η)`,
  `η = 2θ + δ`;
* `i2Psi2Triple K x y y' g₁ h a b c`: the integrand
  `|A(w)| |A'(w')| s(g₁ - w)^(-a) s(w' - w)^(-b) s(h - w')^(-c)`;
* `i2Psi2PointCfg x y y'`: `0 < r, r' ≤ 1`, `0 < d`, with `r = s(y - x)`, `r' = s(y' - x)`,
  `d = s(y - y')`;
* the relations `d ≤ 8 (r + r')`, `r' ≤ 16 (r + d)`, `r ≤ 16 (r' + d)`.
-/

@[expose] public section

namespace RegularityStructures

/-- The majorant of the difference bound: `η = 2θ + δ`,
`d^(-η) + d^(-2) (r^(2-η) + r'^(2-η)) + d^(-(2+2θ)) (r^(2-δ) + r'^(2-δ)) + (r^(-η) + r'^(-η))`. -/
noncomputable def i2Psi2DiffF (θ δ r r' d : ℝ) : ℝ :=
  d ^ (-(2 * θ + δ)) + d ^ (-(2 : ℝ)) * (r ^ (2 - (2 * θ + δ)) + r' ^ (2 - (2 * θ + δ))) +
    d ^ (-(2 + 2 * θ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) + (r ^ (-(2 * θ + δ)) + r' ^ (-(2 * θ + δ)))

/-- The integrand `|A(w)| |A'(w')| s(g₁ - w)^(-a) s(w' - w)^(-b) s(h - w')^(-c)`. -/
noncomputable def i2Psi2Triple (K : SpaceTime → ℝ) (x y y' g₁ h : SpaceTime) (a b c : ℝ)
    (q : SpaceTime × SpaceTime) : ℝ :=
  |i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| *
    (torusParabolicSize (g₁ - q.1) ^ (-a) * torusParabolicSize (q.2 - q.1) ^ (-b) *
      torusParabolicSize (h - q.2) ^ (-c))

                                                                                                     
                                                                                   
                                      
                                                                       
                                              
                                                                           
                                           

                                                                          
def i2Psi2PointCfg (x y y' : SpaceTime) : Prop :=
  0 < torusParabolicSize (y - x) ∧ torusParabolicSize (y - x) ≤ 1 ∧
    0 < torusParabolicSize (y' - x) ∧ torusParabolicSize (y' - x) ≤ 1 ∧
    0 < torusParabolicSize (y - y')

end RegularityStructures

end

public section

namespace RegularityStructures

theorem i2Psi2PointCfg.time_le {x y y' : SpaceTime} (h : i2Psi2PointCfg x y y') :
    |y.1 - x.1| ≤ 1 ∧ |y'.1 - x.1| ≤ 1 := by
  obtain ⟨-, h1, -, h2, -⟩ := h
  exact ⟨by simpa [Prod.fst_sub] using abs_le_one_of_torusParabolicSize_le_one h1,
    by simpa [Prod.fst_sub] using abs_le_one_of_torusParabolicSize_le_one h2⟩

                                                                       
                                                                               
                                                                                                  
                                                                                                   
                                                                                                       
                                 
                                                   
                                                                   
                                                 
                
                                                         
                                                        
                         
            
                                                                    
                                                 
                
                                                         
                      
            

                                                                                                 
                                                                     
                                          
                     
                                                                            
                                                                           
                                                                               
                                                                                                 
                                                                                     

                                                                                     
                                                                              
                     
                                                                                 
                                                    
                                                             
                                                        

                                                                                          
                                                                  
                                          
                   
                                                                            
                                                                             
                                                                                 
                                                                           
                                                                              
                                                                            

                                                                                
                                                                         
                   
                                                                                 
                                                    
                                                                             
                                                              

                                                        
theorem i2Psi2DiffF_parts_nonneg {θ δ r r' d : ℝ} (hr : 0 < r) (hr' : 0 < r') (hd : 0 < d) :
    0 ≤ d ^ (-(2 * θ + δ)) ∧ 0 ≤ d ^ (-(2 : ℝ)) * (r ^ (2 - (2 * θ + δ)) + r' ^ (2 - (2 * θ + δ))) ∧
      0 ≤ d ^ (-(2 + 2 * θ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) ∧
      0 ≤ r ^ (-(2 * θ + δ)) + r' ^ (-(2 * θ + δ)) := by
  refine ⟨Real.rpow_nonneg hd.le _, mul_nonneg (Real.rpow_nonneg hd.le _)
    (add_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr'.le _)),
    mul_nonneg (Real.rpow_nonneg hd.le _)
    (add_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr'.le _)),
    add_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr'.le _)⟩

                                                                                      
                                    
                                                                                 
                    
          

end RegularityStructures

end
