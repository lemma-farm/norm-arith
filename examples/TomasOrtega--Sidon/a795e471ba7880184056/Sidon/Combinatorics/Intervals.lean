module

public import Sidon.Combinatorics.Differences
public import Mathlib.Data.Int.Interval

@[expose] public section

/-! # Integer intervals and elementary invariances -/

namespace Sidon

/-- The paper's interval `[N]`, as a finite set of integers. -/
def interval (N : ℕ) : Finset ℤ := Finset.Icc 1 N

@[simp]
theorem mem_interval {N : ℕ} {x : ℤ} :
    x ∈ interval N ↔ 1 ≤ x ∧ x ≤ N := Finset.mem_Icc

       
                                                           
                               

       
                                            
                 

end Sidon

namespace IsSidonSet

variable {M : Type*} [AddCommGroup M] {s t : Set M}

                                                            
                                                               
                                                                       

                                                
                                               
                                            
                                                                      
                                 
                                       
                                                           
                                        
                                   
                                                        

end IsSidonSet
