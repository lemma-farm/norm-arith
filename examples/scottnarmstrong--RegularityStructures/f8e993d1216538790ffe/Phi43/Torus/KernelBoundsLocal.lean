/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsWeighted
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Local parabolic singular-integral estimate

The estimate in this file is the local `L¹` counterpart of the weighted tail
estimate.  It is used after splitting a covariance convolution into the two
regions where one of its two factors is at least a fixed fraction of the
separation.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric

namespace RegularityStructures

namespace Phi43

                                                         
                                                             
                                     
        

theorem measurable_pos_rpow_extension (p : ℝ) :
    Measurable (fun x : ℝ => if 0 < x then x ^ p else 0) := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ p) (Ioi 0) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
  exact hcont.measurable_piecewise continuousOn_const measurableSet_Ioi

                                                                
                                               
                                         
                                                               
                                       
           
                                          
                                                             
                                                                           
                                                                       
                                                                                          
                                            
                                                                 
                                                                                   
                                                      
                    
          
                                                                   
                                                                      
                    
             

                                                               
                                        
                             
           
                                                          
                

                                                                            
                               
                                                             
                                              
                                                        
                                        
                                                                     
                                   
                                                     
                                                 
                                                                       
                                  
                            
                        
                                    
                                                                   
              
                                                                      
                 
                                                                       
                                                 
                                                                    
                                     
                                                            
                                  
                        
        
                                                               
                                                                                  
                          
                  
                                                                          
                                                                
                                                      
                                                                           
                                                                      
                          
                                                                                     
                                            
                        
                                                                           
                                                     
                                                                 
                                                           
                                                        
               
                                                       
                

                                                                            
                                                                           
                                                           
                                              
                                                          
                                                       
                            
                            
              
            

                                                                              
                                                                   
                                       
                                                                 
                                                                                            
                                                                                         
                                               
                                                   
                                                               
                                                
                                                          
                                          
                                                                       
                                                                                           
               
                                                      
                                           
                               
                                      
                                                    
                            
                                          
                                  
                                    
                                                                                 
                                     
                  
                                                            
                                                   
                                                                  
                                 
                                                                            
                                                               
                                                    
               
                          
                                                  
                                                          
                                         
                                                                                           
                                                            
                                          
           
                                                 
                 
                          
                               
             
                                            
                                                         
                                                              
           
        
                                   
                                                   
                                    
                   
                                                             
                                   
           
                          
                                          
                                                                       
                                         
                                                                                           
                                                                               
           
                                        
                 
                          
                                                                  
             
                                          
                                         
                                                  
                                        
                                                                   
              
                                            
                                                             
                                                                   
            
        
                                                                              
                              
                                             
                                                         
                                                      
                              
                                            
                                                      
                                                                   
                                           
                                                                                           
              
                          
                                                   
                                                            
                                            
                                                                      
                                         
                                                                          
        
                                                                                         
                                           
                                                                  
                                        
                 
                      
                    
                
                                                                     
                                                                                          
                                                                                     
                           
              
                             

end Phi43

end RegularityStructures

end
