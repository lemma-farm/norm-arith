module

public import DirectedCycles.LocalGroupUltraproduct

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

                                                                               
                                                      
                                                    
                                                                                 
                                                
           
             
                 
                                               
            
                                                           
                                      
           
                                                                  
                                                  
                                                                          
                                
                  
                        
                               

                                                               
                                                                       
                                                  

                                                                  
                                                                         
             
                    
                                                  
                                         
                               
                            

                                                           
def LocalGroupAlgebra.setMul {X : Type*} (L : LocalGroupAlgebra X) (A B : Set X) : Set X :=
  {z | ∃ a ∈ A, ∃ b ∈ B, L.mulRel a b z}

                                                  
                                                           
                                                                                        
           
       
                                             
          
               
              
                                                   
                                                                         
                                               
                                                                         
                                                                         
                                          
                                    
                 
                            
                                          
                                          
                                    
                 
                            
                                                                    
                                                                
                                    
                   
                                            
                                                                    
                                                                    
                                                               
                                                      
                                            
                                            
                                                              
                                                     
                                  
end DirectedCycles
