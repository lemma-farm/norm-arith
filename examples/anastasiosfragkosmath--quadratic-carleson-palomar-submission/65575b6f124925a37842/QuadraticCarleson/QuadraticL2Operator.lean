/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.QuadraticTTStar
import QuadraticCarleson.FiniteSparseMaximal
import Mathlib
/-!
# Integral operators for the fixed-height quadratic argument

Finite linearizations of the annular quadratic operators have measurable,
bounded kernels with a finite spatial range. This file develops their actual
integral adjoints and `TT*` representation. The boundedness and finite-range
constants here may depend on the finite family; the oscillatory estimates in
`QuadraticTTStar` will be used to obtain constants independent of that family.
-/

open MeasureTheory Set
open scoped ComplexConjugate

namespace QuadraticCarleson

/-- The elementary kernel properties enjoyed by every finite linearization of
a family of bounded, compactly supported convolution kernels. -/
structure FiniteRangeKernel where
  toFun : ℝ → ℝ → ℂ
  measurable_toFun : Measurable (Function.uncurry toFun)
  radius : ℝ
  radius_pos : 0 < radius
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ x t, ‖toFun x t‖ ≤ bound
  eq_zero : ∀ x t, radius < |x - t| → toFun x t = 0

instance : CoeFun FiniteRangeKernel (fun _ ↦ ℝ → ℝ → ℂ) := ⟨FiniteRangeKernel.toFun⟩

namespace FiniteRangeKernel

theorem measurable_row (K : FiniteRangeKernel) (x : ℝ) : Measurable (K x) :=
  K.measurable_toFun.comp (measurable_const.prodMk measurable_id)

                                                                                         
                                                                 

                                                                                  
noncomputable def adjoint (K : FiniteRangeKernel) : FiniteRangeKernel where
  toFun x t := conj (K t x)
  measurable_toFun := Complex.continuous_conj.measurable.comp
    (K.measurable_toFun.comp measurable_swap)
  radius := K.radius
  radius_pos := K.radius_pos
  bound := K.bound
  bound_nonneg := K.bound_nonneg
  norm_le x t := by simpa only [RCLike.norm_conj] using K.norm_le t x
  eq_zero x t h := by
    rw [K.eq_zero t x (by simpa only [abs_sub_comm] using h), map_zero]

                                                                 
                                       

                                                 
noncomputable def applyIntegral (K : FiniteRangeKernel) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t, K x t * f t

                                                                      
                                                                      
                           

                                                                               
                                                    
                                                         
                                                                                            
                                                          
                          
                     
                            
                       
                               
                                         
                  
                                            
              
                              
                                       

                                                                                            
                                                                                      
                          
                                                      

theorem integrable_row_mul (K : FiniteRangeKernel) {f : ℝ → ℂ}
    (hf : Integrable f) (x : ℝ) : Integrable (fun t ↦ K x t * f t) :=
  hf.bdd_mul (K.measurable_row x).aestronglyMeasurable
    (Filter.Eventually.of_forall (K.norm_le x))

                                                                    
                                                              
                                                             
                                                   
                                                             

theorem norm_applyIntegral_le (K : FiniteRangeKernel) {f : ℝ → ℂ}
    (hf : Integrable f) (x : ℝ) :
    ‖K.applyIntegral f x‖ ≤ K.bound * ∫ t, ‖f t‖ := by
  calc
    _ ≤ ∫ t, ‖K x t * f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, K.bound * ‖f t‖ := by
      apply integral_mono (K.integrable_row_mul hf x).norm (hf.norm.const_mul K.bound)
      intro t
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (K.norm_le x t) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

                                                
                                                              
                                                 
                                                    
                                                   
                   
                
                                          
            
                            
      
                            
                                                      
                                                        
                                
                                                                      
                                                                           
               
                         
               
                            
                                                                              
                                                                              
                                           
          

                                                                 
                                                 
                                            
                                                            
                                       

                                                                        
                                                    
                                                           
                                     
                                                                             
                                                                    
                             
                                                                                
                                     
             
                            
                                                 
                                                            
                                            
                            
                                              
                                                                                    
                                    
                                          
                                                                                  

                                                        
                                                                       
                                                       

                                                                              
                                                                      
                                                                
                                             
                                                                   
                                
                                             
                                                            
                                                                                     
                                                                             
                                                                                                  
                                                       
          
      

                                                                            
                     
                                                                    
                                             
                                                   
                                        
                                  
                           
                                
                                      
                                                                                         
      
                                                  
                             
                              
                             
                              
          
                                                     
                                            

                                                                                
                                                        
                                                           
                                             
                                                         
                                                     
                                                                                             
                            
                                         
                               
                                                     
                                           
                                                                      
                                                           
                                                                           
                                
                                                         
            
        
                      
                                
                                                                              
                         
                          
                                            
                         
                          
                                                            
      

                                                                           
                                                                            
                                                                       
                                                                     
                                     
                                                          
                                                            
                                                                                 
                                                          
        
                         
                          
                                                                                              

                                                                           
                                                                        
                           
                                                         
                                     
                                                                
                                                  
                                                       
                                                                  
                                                        
                                        
                          
                           
                                        
                                                                                              
           

                                                                         
                                                                        
                                                           
                                                                 
                                         
                                
                                       
                                 
                                                                     
                               
                        
                                                                             
                                         
                                                                 
                                                                 
             
                  
            
                    
                                      
                                            

                                                                     
                                         
                                
                                       
                                 
                                                       
                                                                                          

                                                                             
                                                                            
                                                                
                                                                
                                         
                                                                      
                                                                  
           
                                                                          
                                                          
                                
                                   
                                 
                  
                                                                     
            
                                                                           
                                           
                               
                                                                    
                  
            
                                                      
                                                        
                                                                               
                                                                         
                  
                         
                             
                                                                
                                                            

                                                                            
                                                                          
                                                                         
                                                                             
                                                                    
                                     
                                                                     
                                         
                                                                   
                                                                 
                                                    
                                                                     
                                                                                               
                                                               
                                         
                                                                        
                                                              
                            
           
                                                   
                                           

end FiniteRangeKernel

end QuadraticCarleson
