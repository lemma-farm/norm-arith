module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
                                                                           
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! A positive symmetric killed inverse is determined by its dual energy and
finite-energy domain. No existence or convergence of an inverse is asserted. -/

open MeasureTheory Set TopologicalSpace

namespace SubdiffusiveProcess
noncomputable section
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- The dual energy at an image vector equals its original quadratic pairing. -/
theorem limitFormEnergy_apply_eq
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hs : ∀ x y, inner ℝ x (G y) = inner ℝ y (G x))
    (hp : ∀ x, 0 ≤ inner ℝ x (G x)) (x : DomainL2 Q) :
    limitFormEnergy G (G x) = ((inner ℝ x (G x) : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro f
    apply EReal.coe_le_coe_iff.mpr
    have h := hp (f - x)
    simp only [map_sub, inner_sub_left, inner_sub_right] at h
    rw [hs x f] at h
    linarith only [h]
  · apply le_iSup_of_le x
    apply EReal.coe_le_coe_iff.mpr
    linarith only []

                                                                                              
                                 
                                     
                                                   
                                                      
                                 
                                    
                                         
                          

                                                                                                
                                      
                                       
                                                   
                                   
                                                                             
                                                              
                                          
                                                            
                                                                
                                
                                                       
                                            
                                         
                       

                                                                                                 
                                
                                       
                                                    
                                    
                                                    
                                    
                                                
                                                                                           
                                                                    
                                                                       
                                                    
              
                                    
                               
         
                        
         
                                              
                                                                    

end
end SubdiffusiveProcess
