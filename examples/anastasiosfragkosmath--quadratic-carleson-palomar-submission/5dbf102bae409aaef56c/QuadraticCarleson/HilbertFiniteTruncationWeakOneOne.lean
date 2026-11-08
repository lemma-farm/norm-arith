/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import QuadraticCarleson.Definitions
import Mathlib.Analysis.Convolution

/-!
# Weak `(1,1)` for finite annular Hilbert truncations

The zero-modulation contribution of a finite dyadic block is an ordinary
Hilbert kernel restricted to a finite annulus.  Such a kernel is genuinely
`L¹`, so Young's inequality followed by Markov's inequality gives a fully
concrete weak `(1,1)` estimate.  This is the finite-truncation statement; no
maximal-singular-integral hypothesis is introduced.
-/

open Filter MeasureTheory Set
open scoped Convolution ENNReal

namespace QuadraticCarleson
namespace HilbertFiniteTruncationWeakOneOne

set_option autoImplicit false

noncomputable section

                                                               
                                           
                                              

                                                   
                                               
                      
                                                                     
                                                           
                                                                             
                          

                                                       
                                                                  
            
                                             
                                 
                        
                       
                             

                                                                     
                                              
                           
                  
                          
              
             
                                                                     
                                                                         
                                                                 
                                        

                                                                
                                               
                                                      
                                           
                                                          
                                                                       
                                                                           

                                                                      
                                                                          
                                            
                                                                    
                  
                                                         
      
                                         
                                                             
          
                                                           
                
                       
                   
                                                        
                                             
                         
                                                                    
                                                                
                                             
                       
                                                               
                                                         
                             
          

                                                                           
                 
                                                             
                                                           

                                                                  
                                     
                                                  
                                                             
                                    

                                                                    
                                                       
                                                                        
                                     
                                               
                                                              
                                                       
                                
                                                                     
                                   
                                    
                                                                
                                                                         
           
                                                                   
        
                                                     
                                                          
                                        
                                                               
               
                
                     
      
                                                                    
                         
                                                              
                   
                    
                                     
                                                                            
                                                                 

theorem integrableOn_zeroHilbertTail {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    IntegrableOn (fun t ↦ f (x - t) / (t : ℂ)) {t : ℝ | ε < |t|} := by
  let s : Set ℝ := {t : ℝ | ε < |t|}
  have hs : MeasurableSet s := measurableSet_lt measurable_const measurable_id.abs
  have hg : Integrable (fun t ↦ f (x - t)) := hf.comp_sub_left x
  have hm : Measurable (fun t : ℝ ↦ 1 / (t : ℂ)) :=
    measurable_const.div (Complex.measurable_ofReal.comp measurable_id)
  have hb : ∀ᵐ t : ℝ ∂volume.restrict s, ‖(1 : ℂ) / (t : ℂ)‖ ≤ 1 / ε := by
    filter_upwards [ae_restrict_mem hs] with t ht
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, one_div]
    simpa only [one_div] using one_div_le_one_div_of_le hε ht.le
  have hi := hg.integrableOn.bdd_mul hm.aestronglyMeasurable.restrict hb
  change Integrable (fun t ↦ f (x - t) / (t : ℂ)) (volume.restrict s)
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hi

                                                                           
                                                                         
                                                                          
                                                           
                                                                        
                                      
                                                                         
                                     
                                     
                                              
                                
                                                       
                           
              
                         
                                
         
                                                         
                              
                                                               
                                                           
                                                              
                                        
      
                                      
                                           
                                  
                                     
                          
                             
                           
                         
                                                                                      
                      
                                       
                                                                                         
                      
                                      
                     
                                                            
                                          
                                                                       
                                                                           
                                  
                                                       

                                                                 
              
                                                         
                                                                
                                                                  
                                                              
      
                                                                  
                                                  
                                       
                                                           
                                                          
                                                            

                                                              
                                                                  
                                          
                                     
                                                                  
                                      
      
                                                                  
                                                             
                                                    
                                     
                                                                              
                                               

                                                                        
                                           
                                                                   
                              
                                                                        

                                                                        
                               
                                                                  
                                                
                           
                                                                             

                                                                      
                                                                
                                             
                                     
                                                            
                                                                         
         
          
                                                                    

                                                          
                                                       
                                                
                                           
                                                       
                                                                          
                                                 
                                                              
                       

                                                                
                         
                                     
                                                           
           
                                
                                     
                                                    
                                                            
                       
               
                              
                                                         
                                
                                                       
                         
      
                              
                                                           
                                                              
                               
                    

                                                                    
                                                         
                                                    
           
                                                         
                                                                               
           
                                              
                   
                          
                                      
                                                          
                                                              
                                                                 
                                  
             
               
                           
                      

                                                                           
                                                                             
                                                                         
                                                                      
                                             
                                     
                                                               
                                                        
                          
           
      
                                                               
                                               
                                       
                                               
                                        
                                                    
                                                        
                                    
                                                        
                                                                  
                         
                                                          
                                                         
                                                               
                                                  
                                                                  
                             
                 
                                                                
                                                          
                            
                             
                 
                                                               
                                   

                                                       
                                                             
                                                             
                                                          
                                                               
                                               
      
                                                          
                         
                                                       
                                                 
                                      
                                         
                                                             
                                                   

                                                                        
                                                                         
           
                                                                              
                                                             
                                               
                                     
                   
                                                                  
                                               
                                                              
                                         
            
                                                                 
                           
           
                                                                     


end
end HilbertFiniteTruncationWeakOneOne
end QuadraticCarleson
