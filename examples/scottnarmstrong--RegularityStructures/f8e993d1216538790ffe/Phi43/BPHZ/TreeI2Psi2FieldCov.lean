/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2FieldChaosFour

/-!
# The tree `I(Ψ²) Ψ²`: covariance of the field (10.39)

Let `F_a(y) = hairerI2Psi2Field N ρ a ξ x · y` be the field `(10.39)` at scale `a`.  For scales
`a`, `b` (two noises `ξ`, `ξ'` of the same white noise) and points `y`, `y'`,
`E[F_a(y) F_b(y')] = ∫∫ δK_y(w) δK_{y'}(w') (χ₄ + χ₂)(w, w') dw dw' + E[F_a(y)] E[F_b(y')]`,
where `δK_y(w) = K(y - w) - K(x - w)`, the kernels `χ₄`, `χ₂` are the chaos-`4` and chaos-`2`
kernels with covariance entries `Q_{ab}` (resp. `Q_a`, `Q_b`) of `TreeI2Psi2FieldChaos`, and
`E[F_a(y)] = -2 ∫ K(x - w) Q_a(w - y)² dw` (`integral_hairerI2Psi2Field`): the chaos-`0` part is the
square of the mean [Hai14, (10.39)-(10.42)].  Taking `a = b`, `ξ = ξ'` gives the covariance at one
scale; combining four such identities gives the two-scale difference.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

                                                                                      
                                                                              
                                                
                                                  
                                                     
                                                              
                                                                   
                                                                           
                                                              
                                                                
                                                                    
                                                                                        
      

                                                         
private theorem integral_sub_mul_sub_of_integrable {U V : Ω → ℝ} [IsProbabilityMeasure P]
    (hUV : Integrable (fun ω => U ω * V ω) P) (hU : Integrable U P) (hV : Integrable V P)
    (Ca Cb : ℝ) :
    Integrable (fun ω => (U ω - Ca) * (V ω - Cb)) P ∧
      ∫ ω, (U ω - Ca) * (V ω - Cb) ∂P =
        ∫ ω, U ω * V ω ∂P - Cb * ∫ ω, U ω ∂P - Ca * ∫ ω, V ω ∂P + Ca * Cb := by
  have hpt : ∀ ω, (U ω - Ca) * (V ω - Cb) = U ω * V ω - Cb * U ω - Ca * V ω + Ca * Cb :=
    fun ω => by ring
  have h1 : Integrable (fun ω => U ω * V ω - Cb * U ω) P := hUV.sub (hU.const_mul Cb)
  have h2 : Integrable (fun ω => U ω * V ω - Cb * U ω - Ca * V ω) P := h1.sub (hV.const_mul Ca)
  simp_rw [hpt]
  refine ⟨h2.add (integrable_const _), ?_⟩
  rw [integral_add h2 (integrable_const _), integral_sub h1 (hV.const_mul Ca),
    integral_sub hUV (hU.const_mul Cb), integral_const_mul, integral_const_mul]
  simp

                                                                                        
                                                                                          
                                                                                
                                                                             
                                                                                            
                                                                         
                                                                                            
                                                 
                                                                                            
                                                         
                                                 
                                                     
                                                      
                                                     
                                                      
                                                              
                                                                   
                                                        
           
                         
                                                                          
                                                             
           
                         
                                                                      
                                                                                              
                                                 
                      
                                                 
                                            
                                 

                                                                                               
                                                                                               
                               
                                                                                        
                         
                                                                                        
                                                                                              
                                                                           
                                                                             
                                                                                
                                                                             
                          
                                                                                                 
                                                                                 
                                                                                                  
                                                      
                                                                                                  
                                                      
                                                                                    
                                                                                           
                                       
                                                 
                                                  
                                                                                             
                                                                                   
                                                                                     
                                                                  
                                                                    
                                                                     
                                                             
                   
                                                       
                                                                                    
                                        
                            
                                                  
        
                                                         
                                                                                      
                                        
                            
                                                  
        
                                                                                        
                                                                                    
                                                                
                                                                                         
                                                                                      
                                                                
                                                                                            
                                                                                
                                           
                                                                                
                                                 
                                                                          
                                                                               
                                                                           
                                                                                  
                                                                     
                                    
      

end RegularityStructures.Phi43

end
