module

public import BergmanWeakType.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

/-! # Elementary identities for the Bergman kernels

These lemmas establish the kernels' normalizations and the pointwise comparison of the complex
projection with its positive majorant. They do not assert a sharp weak type estimate.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

@[simp]
theorem mem_disk_iff (z : ℂ) : z ∈ disk ↔ ‖z‖ < 1 := by
  simp [disk, Metric.mem_ball, dist_zero_right]

                                                                              
                            
                                              
                                              
                                    
                            
                                                                      
         
                                                      
                            
                          

                                                                  
                                                                             
                                 
                                    
                            
                                                                                       
                              
                                                   
                                                      

@[simp]
theorem norm_kernel (z w : ℂ) : ‖kernel z w‖ = ‖1 - z * star w‖⁻¹ ^ 2 := by
  simp [kernel, norm_pow, norm_inv]

                                                                                       
                                                                      

       
                                                       
               

       
                                                        
               

       
                                                                                  
                   

       
                                                
                                                         
                           

                                                                                    
                                                                    
                                                    
                                                                        
                                                                                  

                                                                        
                                                                                  
                                                                                  
                                                                                        
                                                            
                                           

@[simp]
theorem norm_weightedKernel (α : ℝ) (z w : ℂ) :
    ‖weightedKernel α z w‖ = ‖1 - z * star w‖ ^ (-(α + 2)) := by
  simpa [weightedKernel] using Complex.norm_cpow_real (1 - z * star w) (-(α + 2))

       
                                                                               
                                                            

       
                                                           
                     

       
                                                                                         
          
                                       

       
                                                     
                                                               
          
                                                       

       
                                                      
                      

                                                                           
               
                                             
                                                             

end BergmanWeakType
