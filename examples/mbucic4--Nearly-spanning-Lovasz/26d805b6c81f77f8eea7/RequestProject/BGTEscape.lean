module
public import RequestProject.BGTSanders
public import Mathlib
/-!
# Escape norms and strong approximate groups (Sections 7–8 of Breuillard–Green–Tao)

* `Lovasz.BGT.escNorm`: the escape norm `‖g‖_{e,A}` of Definition 4.3;
* `Lovasz.BGT.IsStrongApproxGroup`: strong approximate groups (Definition 7.1);
* `Lovasz.BGT.escNorm_conj_le`: Theorem 8.1 (i), the conjugation property of the escape norm.
-/

@[expose] public section

open scoped Pointwise

namespace Lovasz.BGT

variable {G : Type*} [Group G]

/-! ### The escape norm -/

                                                                                       
                                                                  

                                                               
                                                          
                                                    
                                                       

section EscNorm

variable {A : Set G} {g : G}

                                                         
            
                                           

                                                                                     
                                          

                                                      
                                                                                

                                                                                          
                                       

                                                         
                                                                         

                                           
                                                                                
                            
                                           
                                                         
                                                
                                                                     
                       
                                                         
                                                                        
                                          
                              
                                                    
            
                        
                                              
         
            
                           

                                                                            
                                                                           
                  

                                                                            
                                                                                      

                                                            
                                           
                                               
                                            
                                                                                             
                            

                                                                 
       
                                               
             
                
                  
                               
                
                                 

                                                                    
                                    

                                                                 
                                                                                             
                                           
                                               
                                            
                                                                         
                            

                                                      
                                                                                          
                                                                  

end EscNorm

/-! ### Strong approximate groups -/

/-- The set of conjugates `S^B = {b⁻¹ s b : s ∈ S, b ∈ B}`. -/
def conjSet (S B : Set G) : Set G := {x | ∃ s ∈ S, ∃ b ∈ B, x = b⁻¹ * s * b}

                                                                                   
                                                                                               
                                                                      
                                                                        

                                                                                                
                                                      
                                                     
                                               
                                             
                                                                      
                                                                           

                                                                                         
                
                                           
                                                                            
                                                                                                
             
              
                
                                        

                                                                                           
                      
                                              
                                                                            
                                                                                       
                                                                   
                                                      
                                   
                                               
                    
                                                        
                                              
                                                                   
              
                       
                                                      
          

                                                                                                 
                                                                                                
                                        
                                                                                    
                                                                          
                                                      
                               
                                                          
                                           
                                                
                                                                     
              
                                                      
                                                       
          
                                                   
                                                 
                                      
                                                         
                                                                 
                                       
                                                    
                                                          
                                                    
                                                                                    
                                                                                    
                                                       
                
                                                           
                                                                         
                                             
                              
                                                 
                                                                                   
                      
                                                         
                                    
                                             
             
                          
                                                               
                                                                                         
                                                     

end Lovasz.BGT
