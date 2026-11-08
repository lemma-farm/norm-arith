module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
The fixed-strip growth and Gaussian contour majorants are new proofs.
See ../../../../../third_party/twelfth/SQUARE_GROWTH_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
No global-order, Hadamard, Architect, or upstream project module is imported.
-/
public import MathCollab.Density.Stronger.Fourth.SquareGrowth
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

theorem norm_hughesYoungAuxiliaryZero_le_polynomial
    {w : ℂ} {R : ℝ} (hR : 1 ≤ R) (hw : ‖w‖ ≤ R) :
    ‖hughesYoungAuxiliaryZero w‖ ≤ 625 * R ^ 8 := by
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hsq : ‖w‖ ^ 2 ≤ R ^ 2 := by nlinarith
  have hbase : ‖1 - 4 * w ^ 2‖ ≤ 1 + 4 * R ^ 2 := by
    calc
      ‖1 - 4 * w ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖4 * w ^ 2‖ := norm_sub_le _ _
      _ = 1 + 4 * ‖w‖ ^ 2 := by simp [norm_pow]
      _ ≤ 1 + 4 * R ^ 2 := by nlinarith
  have hbaseCoarse : 1 + 4 * R ^ 2 ≤ 5 * R ^ 2 := by
    nlinarith [sq_nonneg R]
  unfold hughesYoungAuxiliaryZero
  rw [norm_pow]
  calc
    ‖1 - 4 * w ^ 2‖ ^ 4 ≤ (1 + 4 * R ^ 2) ^ 4 := by gcongr
    _ ≤ (5 * R ^ 2) ^ 4 := by gcongr
    _ = 625 * R ^ 8 := by ring


                                                                      

                                                                          
                           
            

                                                          
                                                                          
                                         
                                                                                       
                                                                 
                      
                                                          
                                                  
                                                            
                                                                          
                      
              
                                
                        
                                                                                   
                          
                                 
                                                         
                                                             
             
                            
                                               
                                                          
                                                                                               
                                        
                                        
                              
               
                                          
                                                                                             
                                                                      
                                    
                                                                 
                                                                                      
                                         
                             
                               
                                                      
                               
                                      
                         
                                   
                                                           
                                                                                    
                                             
      
                                                                      
                                                    
               
                                      
                                               
                                                  
                               

                                                 
                                                                            
                                                                                    
                                                                      
                                                                               
                   
            
                                    
             
              


                                       
                                                                                    
                                                     
                                                                       
                                                        
                         
          
                                                            
                             
          
                                             
                                                     
                             
                           
      
                                                    
                                                          
                    

                                                                           
                                                                    
                                                                     
                                        
                                                                      
                                           
                                                    
                                                             
                       
                                                        
                               

                                                                                      
                                                                            
                               
                                                                        
                                                                        
                                                          
                                                                    
                                                                              
                                                                                   
                                                                           
                                                                                 
                                                 


                                          
                                             
                                                                                        
                                      
                                                                                         
                                           
      
                                                       
                                                     
                                                               
                                                           
                    

                                                                                            
                                                                            
                                                                                    
                                                                             
                                                             
                                                                         
                       
                                                   
                                        
                                                      
                               

                                                                                         
                                                                      
                                                                            
                       
                                                                          
                                         
                                                                   
                            
                                                           
                                            
                                                            
                      
                                                              
                
                                     
                                         
                                                    
                                               
                                                            
                                       
                                                                                       
                                                                      
                                           
                                                                              

                                                                       
                                                                             
                       
                   
                                                                       
                     

                                                                                     
                                                                   
                         
                                                          
                                                            
                                                                   
                                                          
                                                             
                                                                 
                                          
                                                          
                                                            
                       
                                                   
                      
                                                        
                                                        
                         
                            

                                               
                                                                               

                                                                           
                                                                             
                                                      
                                   
                                                                                           
                                                                     
                   
          
                             
                         
                              
     

                                                                               
                                                                                 
                                                 
                                                                              
                                                               
                                                    
                                                     

                                                                           
                                                            
                                                                            
                                                
                                                        
                                           
                                                                                        

end MathCollab.Density.Stronger.Fourth
