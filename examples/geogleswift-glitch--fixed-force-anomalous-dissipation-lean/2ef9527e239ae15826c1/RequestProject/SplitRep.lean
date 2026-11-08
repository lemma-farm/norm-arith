module

public import RequestProject.SplitConvergence

/-!
# The probabilistic representation of the split operator

`P_j h(x) = 𝔼_ζ h(Ψ_j(x))` where `Ψ_j = f_1 ∘ ⋯ ∘ f_j`, `f_i(y) = ψ_i(y + ζ_i)`, and the `ζ_i` are
independent Gaussian increments (the first part of Lemma 3.8).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

instance gaussSeq_isProb (v : ℝ≥0) : IsProbabilityMeasure (gaussSeq v) := by
  unfold gaussSeq; infer_instance

                                                                                  
                                             
                                                                                                 
                      
                                                                                        
            
                 
                                                 
           
                                                                                         
                                                                           
               
                                                                                    
               
             
                                 
                               
                       
                                               
                         
                        
                                            
                 
                           
                          
                 
                                 
                                      
                
                                      
                             
                                                                                         
                      
                                                                                       
                                                                                  
         
                   
                                     
                                                            

                                                                             
                                                                              

                                           
                                                                                               
                                                               
                  
               
                
            
                                                                                      

                                                                                      
                                                                      
                  
                                
                
                                                     
                                               
                                                            
                                                          
                    

                                                                                                 
                                                                                              
                                                                                         
                                                                                    
                       
                                 
                                         
                
                     
                 
                                       
                                     
                                                                                        
             
                                 
                                      
                                                                  
                                                
                                                             
                                                                                         
                                                              
                                                                                   
                        
           
                                                           
                                                                                                
              
                                                                          
                                                                                             
                                                    
                                                                
                     
                                                                                          

end AnomDiss
