module

public import DirectedCycles.LocalDivision
public import DirectedCycles.FiniteGroupDerivatives

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Translation by a local group element, extended by zero outside its actual
range. No arbitrary multiplication is introduced at undefined pairs. -/
noncomputable def leftShift (g : G) (f : G → ℝ) (x : G) : ℝ := by
  classical
  exact if h : ∃ y, L.mulRel g y x then f (Classical.choose h) else 0

                                                             
                                                                     
           
                  
                          
                                                                                                     

                                                                                    
                               
           
                       

                                                                                       
          
                                                

                                                                              
                                             
                                                               
           
          
                                    
                    

                                                                      
                                                                         
                                                                           
                                                             
                                                     
           
                                 
          
                                          
                      
                                    
                                                                          
                                       
                                     
                
                                              
                             
                          

                                                                             

section Finite
variable [Fintype G]

                                                           
                                                                             
           
                                                    
         
                  
           
                             
                         
                       

                                                                              
                                                                   
                                                                       
                                             
                                                                    
         
                       
                     
                       
                            
                                                  
                                          
            

                                                                              

                                                       
                                      
                                  
      
                                                                  
                                                              
                        

                                                 
                                                     
                                                                                         
end Finite
end LocalGroupAlgebra
end DirectedCycles
