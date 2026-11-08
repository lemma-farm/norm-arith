-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Lean module/public-import adaptation).
module

public import Mathlib
public import SlowEquilibration.Upstream.OAI.Probability.SKGap.Model

@[expose] public section


namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKGap

                                                                           
                                    
                                                          
                                                                       
                        
                                                                  
                                                                      
         
                                                          
                                                 
            
        

                                                                            
                                                                                             
                                       
                                                                            
                                                  
                                             

                                                                    
                                                    
                                                                                   
                                                                    
                                            
                                                   
                                                                       
                                                
                                                  
                                                  
                                                                       
                                     
                                                                    
                                                                   
        
                                                                
                                                             
                               
                                                                      
                                                                     
                                                
                                              
                         
                                                                      
                                                      
                                       
                     

def standardGaussianProduct (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (n : ℕ) : IsProbabilityMeasure (standardGaussianProduct n) := by
  unfold standardGaussianProduct
  infer_instance

                                                                        
                                                                     
                     
                                            
                                        
                                                                  
           
                                                    
                                                        

                                                                
                                            
                                             
                                                           
                                      
                                                                           
                                                       
                                                      
                                                                      
                                    
                                                           
                                          
                                                                         
                                                             
                                             
                                                        
                                                                 
                                                     
                                                               
                                                                         
                                         
                                                             
                                                   
                                                                                        
                                                 
                                                                
                                         
                                                   
                                   
       
                                
                         
                          
                                      
                                                                            
                                                                                   
                                        
                                                                              
                                                                                    
                                         
                                                                                    
                                                                                                                    
                                                               
                                        
                                                      
                                                                                 
                                           

end SKGap

open Filter
open scoped Topology
namespace SKGap
                                                                    
                                                                 
                            
                                                            
                         
           
                                                        
            
                                                                                
                                                             
                                                                                                             
                          
                                                                                                            

                                                                        
                                                                               
                                                                              
            
                          
           
        
         
                                             

                                                                        
                                                                 
                                                                                       
                                                      
                                                       
                                                                       
                                                            
                                                                     
                                                                                                    
                                                                  
                                                     
                              
                                                                                           
                                                                                             
                                                                 
                                                      
                                                                                                  
                                                                  
                                                   
                                  
                                                                                              
              
                       
                                                                                                                 
                                                                  
                                                          
                                         
             
             
            
        
                                                                                    
                                                                        
                                                                                         
                                                                                          
                                                                         
                                                          
                                                                   
                                                                                                     
                          
                                
                                                                              
                 
                                                            
                                                                                                  
                         
                                                                            
                                                                   
                 
                     

end SKGap

end

end OAI
