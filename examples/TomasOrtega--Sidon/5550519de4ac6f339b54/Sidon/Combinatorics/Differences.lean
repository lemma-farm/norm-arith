module

public import Sidon.Basic

@[expose] public section

/-! # Nonzero differences of Sidon sets -/

namespace IsSidonSet

variable {M : Type*} [AddCommGroup M] {s : Set M}

/-- A nonzero difference in a Sidon set determines both endpoints. -/
theorem eq_of_sub_eq_sub (hs : IsSidonSet s) {a b c d : M}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (h : a - b = c - d) : a = c ∧ b = d := by
  have hsum := sub_eq_sub_iff_add_eq_add.mp h
  have hp := hs a d c b ha hd hc hb hsum
  have hmem : a ∈ ({c, b} : Set M) := hp ▸ Set.mem_insert a {d}
  have hac : a = c := (show a = c ∨ a = b from hmem).resolve_right hab
  rw [hac, add_right_inj] at hsum
  exact ⟨hac, hsum.symm⟩

                                                                       
                                                      
                                       
                                                 
             
                                      
                                               
                                    
                        
                                                      
                   
                                                                 
                                   
                                                          
                   
                             

                                                                                 
                                                       
                                   
                                                                          
                     
                                                     
                                                  
                                                                 
                      

end IsSidonSet

namespace Sidon

variable {M : Type*} [AddCommGroup M] [DecidableEq M]

                                                                               
                                                 
                                               

       
                                                                                
                        
                                                                      
         
                                                                                   
                                                                   
                              

                                                                        
                                                                           
                                                        
                              
                 
                                             
                                             
                                               
                                               
                             
             
                                                   
                                                             
                        
                      

end Sidon
