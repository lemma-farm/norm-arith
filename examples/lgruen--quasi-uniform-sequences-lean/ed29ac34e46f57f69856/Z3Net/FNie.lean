module
public import Z3Net.FBasic
public import Mathlib
@[expose] public section

/-!
# Entry F, part 2: `lem:nie` (box criterion, both directions)

The map `v ↦ (⌊X_c(v)/q^(m-d_c)⌋)_c` factors as `ψ ∘ (box matrix ·)`, where `ψ` reads the stacked
leading digits as base-`q` numbers; `ψ` is a bijection, so every box holds exactly one point iff
the box matrix is bijective on `R^m`, i.e. (finite ring) iff its determinant is a unit.
-/

namespace Z3NetF.Proofs

open Matrix Finset

noncomputable section

variable {R : Type*} [CommRing R] {q s m : ℕ}

                                                                                
                                                                                                  

                                         
                           

                                          
                                                                                       
                  
                                       
                                                                                                         
                                                                              

                                                                                             
                                     
                                                                                               
                                                                                                        

                                                                                               
                                
                                                    

                                                                                     
                                                                
          
                                                  
                                                                                            
                                  
                                    
                                                                      
                              
                      

                                                            
                                                                                   
                                                     
                                                                                             
                                                          
         
          
                                                                                  
                                                                    
                                                             
                                      
        

                                                                
                                                    
           
             
           
                                                                
                                                     
           
                                       
                                                    

                                
                                                                                      
                                                                                         
           
                                                   
                     
                               
                                
                                                                                                         
                                                    
                                                                 
                                                                                  
                                                    
                                                          
                                       
                                         
                                                                      
                                                                                  
                                  
             
             
                                                   
             
                                                                             
                          
                                                          
                                                            
                 
                                                    
                            
                                           
                     
                
                 
              
                   
                       
                     
                       

                                                                        
                                                                                             
                                                                 

                                                                                                    
                                                                                             
              
                                                                         

                                     
                                                   
                                   
                                
                                       
                                                     

                                                                                     
                                                                                       

                                                                                   
                                                 
                                                                             
                                      

end

end Z3NetF.Proofs
