module

public import RequestProject.Euler.ContourCrossLogShapeLipschitz

/-! # Actual local Lipschitz regularity on the open separated-pair locus -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) crossLocusC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossLocusC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

                                                       
                                                 
                                                 
                                                        
                                                        
          

                                                      
                                                                               
                                                                                  
           
                                                                  
                                                                    
                                               
                                                                                  
                                                                                                
           
                                                                                      
                                               
                                  
                                 
                    
          

                                                
                                                                                       

                                                        
                                                                                                     
                        
            
                            
                                   
            
                                 
                                         
            
                                                   
                                                        
                                                                                          

                                                          
                                                              
                                                                                         

                                                                 
                                                             
                                                      
                                                                                     
                                                                                          
                                 

                                                                           
                                          
                                                                                                             

                                                                                        
                                                                                  
                                                             
                                                       
                                                                   
                                                                                  
                                            
                                                                     
                                      
                 
                                                                                 
                                                                     
                                               
                                                                                                       
      
                                                                                                 
                                                                                                        
                                                                          
                                                                           
                                                                                      
                    

                                                                                 
                                                         
         
                                    
                                      
                                             
                        
                                                         
                                                                       
                                                                                         
                                                                            
                                                                  
                                         
                                                                         
                                                         
              
                                         
                                                                             
                                         
                                                                             
                                                                                                     
                                                    
                                                                                  
                                                    
                                                                                   
                                                              
                                                                                       
                                     
                                                                                          
                                                             

end Euler2D

end
