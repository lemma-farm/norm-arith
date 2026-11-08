module

public import Paper.DoobHeat
public import Paper.GaussianPositivity
public import Mathlib
@[expose] public section

/-! # Self-adjointness of the concrete Gaussian heat operator

The bounded observable and integrable test give absolute integrability on
the product space. Symmetry then supplies the reverse order of integration.
These identities are the spatial adjoint step in distributional heat testing.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

theorem heatSemigroup_eq_kernelAverage (ell : ℝ) (hell : 0 < ell)
    (f : ℝ → ℝ) (hf : Measurable f) (x : ℝ) :
    heatSemigroup ell f x = kernelAverage (μ := volume) (heatKernel ell.toNNReal) f x := by
  have hv : ell.toNNReal ≠ 0 := (Real.toNNReal_pos.mpr hell).ne'
  rw [kernelAverage_heatKernel_eq_gaussian_integral ell.toNNReal hv f x]
  exact gaussianExpectation_shift_eq_integral x ell hell.le f hf

                                                                           
                                                             
                                                                              
                                                                  
                                                                             
                                                  
                                                      
                                                                                 
                                                               
                                                                                    
                       
                         
                                                                
                     
        
                                                                         
      
                                                           
                                                   
               
                             
                           
          

                                                                      
                                                          
                                                        
                                                         
                                                        
                                                                               
                                         
             
                                             
                                                        
                                                                   
                                                                           
                                                     
                                                                   
                                     

                                                                  
                                     
                                                                   
                                                                            
                                                                  
                                                                      
                                
                       
                         
                                                                      
                                  
                             

                                                                
                                     
                                                                          
                                                                            
                                                                  
                                                                      
                                
                       
                         
                                                                      
                                  
                      
                           
      
                                                                           
                                                           
                                                             
                                                                           
                             
                           
                                    
               
                             
                                                                            

                                                                  
                                                          
                                          
                                         
             
                                          
           
                                               
             
                                                                                               
                                                          
            
                                                                                   

                                                                
                                                          
                                                 
                                         
             
                                             
                                                         
                                                                                 

                                                                            
                                                                 
                                                          
                                                     
                                                   
                                                                           
                                                                              
                                                                          
         
                                        

end Paper
