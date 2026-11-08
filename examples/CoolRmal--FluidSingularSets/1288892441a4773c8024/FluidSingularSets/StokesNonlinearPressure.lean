-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallStokesPressure
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Actual convective and viscous Stokes pressures

Spatial `L⁴` velocity data produce the true `L²` convective tensor. The already
constructed bounded mean-zero Stokes pressure operator yields its nonlinear
pressure and the pressure of the actual negative velocity gradient. The signs
correspond respectively to `-div (u ⊗ u)` and `+div Du`. Their quantitative
bounds and literal compact-test Stokes equations use only the genuine input data.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The true rank-one tensor in the Hilbert matrix norm, with derivative index first. -/
def stokesOuterProduct (a b : Vec3) : StokesGradientMatrix :=
  WithLp.toLp 2 (fun ij ↦ a ij.1 * b ij.2)

@[simp]
theorem stokesOuterProduct_apply (a b : Vec3) (ij : Fin 3 × Fin 3) :
    stokesOuterProduct a b ij = a ij.1 * b ij.2 := rfl

                                                 
                                                                                   
                                                                 
                     
          
                                                         
                                                 

/-- Sup-norm vector data control the true nine-component Hilbert tensor norm. -/
theorem stokesOuterProduct_norm_le (a b : Vec3) :
    ‖stokesOuterProduct a b‖ ≤ 3 * ‖a‖ * ‖b‖ := by
  have hsq : ‖stokesOuterProduct a b‖ ^ 2 ≤ 9 * (‖a‖ * ‖b‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ij : Fin 3 × Fin 3, (‖a‖ * ‖b‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro ij _
        rw [stokesOuterProduct_apply, norm_mul]
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul (norm_le_pi_norm a ij.1) (norm_le_pi_norm b ij.2)
            (norm_nonneg _) (norm_nonneg _)) 2
      _ = _ := by norm_num
  apply le_of_sq_le_sq _ (by positivity)
  convert hsq using 1
  ring

                                                                          
                                        
                              
            
                                                         

                                                                           
                                                                     
                                          
                                                                              
                                                             
                                                                         
                                                                                      

                                                                                
                                                             
                                                                
                                                                                   

                                                                       
                                                                          
                                          
                                                                            
                                                   
                                                             
                                                  
                                                                                 
                                                   
                                                                  
                                                            

                                                                                
                                                                         
                                          
                                     
                                                            
                                             
                                                                                             
                                                                                   

                                                                               
                                                                             
                              
                                             
                                                                  
                                              
                                                                                 
                                                               
                                                          
                                                    
                                                                      
                                                                  
                             
                                
       
                                                                                  
                                               
                                          

                                                                                  
                                                                             
                                                                   
                                             
                                                                                 
                                                                            
                                     
                                                                  
                                           
                                                                        
                                                          
                                                                   
                                                                             
                                                                                 
           
       
                                                                                          
                                                              

                                                                          
                                               
                                                                             
                                                                            

                                                                  
                                                                                         
                                                 

                                                                                              
                                                                                          
                                        

                                                                                 
                                                                                         
                                                                    
                                   

                                                                                      
                                                                              
                                          
                                                                 
                          
          
                                                      

                                                                                
                                                                
                                                                
                                                                       

                                                                         
                                                                              
                                                   
                                                                    
                              
        
                                                
                               
                  
                                                                                       
                                         
                          
                                        
                     
      

                                                                                
                                                                            
                                          
                                                                                   
                                        
                                                                      
                                                       
                                                     
                                                               
                                                                                     
                                    
                                                                
                                                               
                                                               
                                                      

                                                                                          
                                                        
                                                                             
                                                    

                                                                                 
                                                               
                                                       
                                                                             
                                       
                                                                           

                                                                           
                                                        
                                                       
                                      
                                                                          
      
                                                                                         
                                                                              
                                                                                     
                    

                                                                              
                                                                            
                                               
                                                                        
                                                                              
                                                        

                                                                                    
                                                                 
                                                       
                                       
                                                                      
      
                                                                        
                                                                          
                                                                                
                    

                                                                            
                                                                 
                                                       
                                                           
                                                        
                                        

                                                                          
                                                                                     
                                                      
                                                        
                                        

                                                                                         
                                                                                
                                           
                                                                       
                                                                                       
                                        
                                               
                                                                 
                                       
                                                                           
                                                    
                                                
                                                
                                                   
                                                                              
                                           
                                                             
                                                              
                                                                            
                                                         
                      

                                                                                   
                                                               
                                                     
                                           
                                                         
                                                                                       
                                        
                                               
                                                                                               
                                       
                                                             
                                                    
                                                
                                                
                                                                  
                                                             
                                     
                                                               
                                                                                            
                      

                                                                                             
                                                                                 
                                           
                                                    
                                                                                       
                                        
                                               
                                                                    
                                       
                                                        
                                                    
                                                
                                                  
                                                    
                                                                    
                                                         
                                                 
                                                  
                                                    
                       
                           
                                             
           
                                                                             
                    
                      

                                                                                               
                                                                        
                                                     
                                           
                                                          
                                                                                       
                                        
                                               
                                                                                           
                                       
                                                              
                                                    
                                                
                                                  
                                                           
                                                                                           
                                                        
                                                                     
                                                
                                                          
                           
                                                                              
                                                                         
           
       
                   
                      

end FluidSingularSets
