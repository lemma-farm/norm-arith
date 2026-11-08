module

public import Sidon.Combinatorics.Differences
public import Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Tactic

@[expose] public section

/-! # The additive energy of a Sidon set -/

open scoped BigOperators

namespace IsSidonSet

variable {M : Type*} [AddCommGroup M] {S : Finset M}

                                                                  
                                                         
                                                           
             
           
                                       
                                                               
                                                      
                                                   
                             
                                 
                              
                                    
         
                        

variable [DecidableEq M]

                                                                
                                                    
                                                        
           
                                         
                                               
                                               
                                                             
         
                                  
               
              
                                                 
                                                   
                                                  
                                                  
                                   
                                                              
                              
                                                           
                                                         
                              
                            
                 
                                                             
                                                           
                                                              
                                                                
              
                                                
                                                           
                                                    
                  
                     
                                                           
                                                       
                  
                               
                                 
                                  
                 
                                                
                                                 
                                                         
                                             
                                                        
                                                                
                                              
                                       
                                   
                 
                               
                                                       
                                       
                                 
                 
                               
                                               
                                                                 
                                                              
       

                                                    
                                               
                      
                      

theorem card_nonzero_differences (hS : IsSidonSet (S : Set M)) :
    (S.offDiag.image (fun p => p.1 - p.2)).card = S.card ^ 2 - S.card := by
  rw [Finset.card_image_of_injOn hS.difference_injOn, Finset.offDiag_card, pow_two]

                                                    
                                   
                                                  
                                                       
                                            
              
                                                 
                                                                               
                        
                                           
                                                                                
                              
             

end IsSidonSet
