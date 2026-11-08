module

public import RequestProject.Euler.ContourNormalizedChord
public import RequestProject.Euler.ContourSmoothEmbedding
public import RequestProject.Euler.ContourHolderScalar

/-! # Actual value, constant, and real-part maps in contour Hölder spaces -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal BoundedContinuousFunction

namespace Euler2D

                                                                   

                                                                                       
                                   
            

theorem contour_dist_le_holder_power {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1)
    (x y : ContourCircle) :
    dist x y ≤ Real.pi ^ (1 - (γ : ℝ)) * dist x y ^ (γ : ℝ) := by
  by_cases hd : dist x y = 0
  · rw [hd]
    positivity
  have hdp : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
  calc
    dist x y = dist x y ^ (1 - (γ : ℝ)) * dist x y ^ (γ : ℝ) := by
      rw [← Real.rpow_add hdp, sub_add_cancel, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow dist_nonneg (contour_dist_le_pi x y) (sub_nonneg.mpr hγ1))
      (Real.rpow_nonneg dist_nonneg _)

                                                                                         
                                                                       
                                                 
                                                                       
                                                                         
                                           
                                                        
           
                                                                                            
                                                                  
                                                                                   
                                        

                                                                               
                           
                                                                                                         

                                                                        
                                                
                                                                    

                                                                                           
                                                                                 
                                                        
                                     
                                                                    
                                                                              
                                     
            
                                                                                             
           
                                                                  
                                                                                
                                                    
             
                                                                         
                                                                  
                                                              
                                                                             
                                                                 
                                       
                                                                                              
                                       

                                                                                         
                                                                                                    
                               
         
     

                                                                                                 
                                                               
                                                        
                                 
                                                

                                                                        
                                         
                                                                          
                                                                               
                                                  
                
                                                      
                                                                              

                                                                                      
                                             

                                                                  
                                                                                 

                                                                                        
                                 
                                          
                                                              
                                                                                 
                                                                    
                                                                                 
                                                  
             
                                                                                                        

                                                                                                      
                                                     

                                                                            
                                         
                                                         
           
                                                                                  
             
                                                                               
                                                
           
                                                                                          

                                                                                           
                                   
                              
                                    
              
                                                                          
           
                               
                                    
              
                                                           
                                                                                                   
                
                                                
                                                                 

                                                                                                         
                                                          

end Euler2D

end
