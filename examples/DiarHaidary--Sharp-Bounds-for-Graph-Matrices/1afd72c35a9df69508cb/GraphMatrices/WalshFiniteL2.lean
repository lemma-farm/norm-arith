import GraphMatrices.FiniteL2
import GraphMatrices.Walsh
import GraphMatrices.SignGraphDegree

/-! A complete finite Walsh basis and its exact matrix-valued vacuum identity. -/

namespace GraphMatrices.Walsh

noncomputable section

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem character_eq_prod (S : Finset E) (σ : E → Bool) :
    character S σ = ∏ i ∈ S, sign (σ i) := by
  simp [character]

                                                 
                                                     
                                                         
           
                                
                                                                 
                                                     
                
                                                       
                                                    
              
                              
             
                                                                      
              
                      
           
            
                   
                                                             
                                                 
                                                         

                                                          
                                                                 
                       
                                                   

                                                                      
                                                                                          
           
                                                         
                      
                              
                      
                                                                                 
                                              
                                                               
                       
                              
             
        
                                          
                                           

                                                                          
                                          
                                  
                                          
                    
                          
                                         
                                         
                             
                              
                                         
                                         
                                  
                          
                                                                                          
             
                                  

                                                     
                                                                           
                                                                      
     

                                        
                                           
                                             
                                                                         
                                                                       
                               
                                                           

end
end GraphMatrices.Walsh
