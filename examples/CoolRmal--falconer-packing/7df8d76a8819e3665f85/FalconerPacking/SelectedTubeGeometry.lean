/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SelectedTubeWeights
                                                       

/-!
# Geometric containment for selected tube tests

Rectangles below are specified by their half-widths. The proof allows a change of frame
of order a/b, and keeps the transverse and longitudinal bounds separate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open Classical

namespace FalconerPacking

                                                                                 
                  
                                                                  
                                                                                
                                                 

                                           
                                    
                                                                  
                                                                                           
                                                                                 
            
                                                                                 
            
                                                             
                                                   

/-- The Euclidean norm is bounded by the sum of the absolute frame coordinates. -/
theorem norm_le_frame_coordinate_sum
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ≤ |(O x) 0| + |(O x) 1| := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 ↦ ℝ) (O x)
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, O.norm_map] at h
  nlinarith [norm_nonneg x, abs_nonneg ((O x) 0), abs_nonneg ((O x) 1),
    mul_nonneg (abs_nonneg ((O x) 0)) (abs_nonneg ((O x) 1))]

                                                         
                                 
                                                                  
                                                 
                                                                           
                                                             
                                                   
                                                        
                                                           
                   
             
                             
                                                     
                          
                             
                                                     
                          

                                                                                           
                                            
                                                                    
                                                    
                                    
                                    
                                  
                                              
           
                                
                                                    
                                                                                      

                                                                                      
                                                          
                                                  
                                                                    
                                                                        
                                                              
                                              
                                                  
                              
                                                                           
                                                                               
                                    
                                               
                                        
                                 
                                                                        
        
                                            
                                                                     
                          
                                                            
                                                         
                                                   
                                         
                                                                                
                                                           
                         
                                                        
                                                           
                         
                                                        
                                                 
                                                          
                
                                               
                                                              
        
                                                         
                                                                
                                           
                             
                                                            
                                                                           
                                                                                
                                               
                                             
        
                                                                    
                                                                     
                                           
                                                            
             
                                                              
                                                                 
                                                           
                                                              

                                                                                
                                                                          
                                     
                                                                  
                                            
                                                                     
                                                  
                       

                                                                                     
                                                                                   
                                                              
                                                           
                                              
                                      
                                                
                                                                    
                                        
                                                                          
                                                  
                                                              
                                                              
                             
                                                      
                                                    
                                                    
                                                                        
                                                                         
                                    
                                                                                         
                                                         
                                                        
                                      
                                                                    
                                   
                              
                                
                             
                                                                              
                                                                         
                                                         
                                                                   

end FalconerPacking
