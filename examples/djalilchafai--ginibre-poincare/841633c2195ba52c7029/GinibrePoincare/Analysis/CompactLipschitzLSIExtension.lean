module

public import GinibrePoincare.Analysis.LipschitzMollification

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution NNReal
namespace GinibrePoincare
noncomputable section

                                     
                                                        
                                                              
                                                                   
                                                       
                                                
                                               
                                         
                                                                                                      
      
                                                                              
                                      
                                                                                                     
                                
             
                
                                                                         
                                                                
                                                                   

                                                                                  
def directionalEnergy {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (d : ι → E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, (fderiv ℝ f x (d i)) ^ 2

                                       
                                                                      
                                                                              
                                                                
                                                                                   
                         
            
                                                     
                                                                                          
                                                                          
                                                

                                                                            
                                                                            
                                                                             
                                  
                                                          
                                                                          
                                                                                 
                                     
                                                                
                                                              
                                                                               
                                                                 
                                                                             
                                         
                                                                           
                                                                        
                                               
                                                                
                                                               
                                                                              
                                                                  
                                                        
                                                     
                                                                                       
                                                      
                                                      
                                           
                                                                                     
                                                                    
                                                                                    
             
                                
             
                                                        
                        
                                 
                              
                                                    
                                                           
                                                                       
                                                       
                                                                                 
                                           
                              
                                
                
                                                                                     
                                                   
                                                                      
             
                                                                            
                                      
                              
                             
                
                                                                                               
                                                 
                                                                                        
                                                                                           
                                              
                                                            
                                            

end
end GinibrePoincare
