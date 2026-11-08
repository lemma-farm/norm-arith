module

public import RequestProject.Euler.ContourCrossLogLocus

/-! # Genuine little-space preservation of the separated cross-interaction

Both actual inputs are approximated by genuine smooth contours in their
real Banach norms. Separation is retained quantitatively, and the proved
C¹ Hölder local Lipschitz estimate passes the actual outputs to the closed
little subspace.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) crossLittleC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossLittleC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

local instance (priority := 2000) crossLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

                                                                           
                                                     
                                   
                                                             
                                                                                
                                                
                                                                                         
                                                                                
                              
                                                                                         
                                                                 
                            
                     
              
                                         
                                               
                                                                                               
                                             
                           

                                                                  
                                                                                                    
                                                                                                     
                                                                                            
                                  
                                                                                            
                                  
                                                                              
                                                                                   
                                               
                       
                                              
                                               
                       
                                              
            
                                                        
                                                           
                                                                            
                                                              
                                                                      
                                                              
                                                                      
                                                                                       
                                                                       
                                              
                                                                                   
                                                       
                                                         
                            
         
                                                                                           
                                      
                                                                                                  
                                                                                  
                                                                                        

                                                       
                                                                                                    
                           
                                                                                           

                                                                             
                                                                                                    
                                                                            
                                                      

                                                                        
                                                                                                    
                                                                       
                                                  

                                                      
                                                                                                       

                                                                                  
                                                                              

                                                    
                                                     
           
     

                                                              
                                                                        
                                                                                             

                                                                                    
                                                
                                                                         
                                                                     

                                                                               
                                                
                                                                    
                                                              

                                                                                     
                                                             
                                                                             
                                                                  
                                                        
                                                                     
         
                                 
                       
                 
                  

end Euler2D

end
