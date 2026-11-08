module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.MulAction

@[expose] public section

/-!
# Closed additive subgroups of the p-adic integers

Integer density makes a closed additive subgroup of `ℤ_[p]` stable under every
`ℤ_[p]`-scalar. It is therefore an ideal, and the discrete valuation ring
classification identifies each nonzero such subgroup with `p^n ℤ_[p]`.

The action-kernel results below are conditional on a nontrivial kernel. They do
not establish that a p-adic action on a manifold has a nontrivial kernel.
-/

namespace HSFormal

open Topology

/-- The additive subgroup `p^n ℤ_[p]`. -/
noncomputable def padicPowerSubgroup (p : ℕ) [Fact p.Prime] (n : ℕ) : AddSubgroup ℤ_[p] :=
  (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]).toAddSubgroup

section ClosedSubgroups

variable {p : ℕ} [Fact p.Prime]

                                                                                              
                                                           
                                                                                          
                                                         
                                                          
           
                                                    

                                                                     
                                                                                      
                     
              
                         
                                          
                                                                  

       
                                                                      
                                                                                              

                                                                              
                                                            
                                                   
                                             
                                                   
           
             
                                                                  
                                                           
                                                   
                
                                                                       
                                                   

                                                                            
                                                                   
                                                                                       
                    
                  
                                                      

                                                                       
theorem padicPowerSubgroup_eq_closedBall (n : ℕ) :
    (padicPowerSubgroup p n : Set ℤ_[p]) =
      Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) := by
  ext x
  change x ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) ↔
    x ∈ Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ)))
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm

                                                                                          
                                                                                             
                                       
                                             
                                                                        

                                      
theorem padicPowerSubgroup_isClosed (n : ℕ) : IsClosed (padicPowerSubgroup p n : Set ℤ_[p]) := by
  rw [padicPowerSubgroup_eq_closedBall]
  exact Metric.isClosed_closedBall

                                                                
                                                          
                                                                                
                                                          
                                   

                                                               
                                                                 
                                                                                        
                        
              
                
                                                           
              
           
           
                 
           
         
                             
             
           
              
                                                                  
                                   
                                                                                      
                                                                           
                                                                                      

end ClosedSubgroups

section ActionKernel

variable {p : ℕ} [Fact p.Prime] {X : Type*} [AddAction ℤ_[p] X]

                                                            
                                                                                            

       
                                           
                                                                       
                                                    
                     

variable [TopologicalSpace X] [T2Space X] [ContinuousVAdd ℤ_[p] X]

                                                                        
                                                                                                     
                                                                 
                                             
         
                                                        
                                                                        
           
                                 
                                                                       

                                                                                 
                                                                                    
                                                                            
                                                               

                                                      
                                                                                  
                                                               
                                                             

end ActionKernel

end HSFormal
