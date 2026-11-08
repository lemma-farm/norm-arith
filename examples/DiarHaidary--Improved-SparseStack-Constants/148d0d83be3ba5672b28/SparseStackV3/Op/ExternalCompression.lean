/-
Copyright (c) 2026 Diar Heidary. Released under the MIT license.
-/
import SparseStackV3.Op.Norm

/-!
# Exact external compression on the signed-bucket state space

The analysis map of the actual Parseval frame is an isometry at every sample.
Its adjoint is a contraction. These maps act only on the external coordinate
and commute with every physical occupation projection. The resulting norm
transfer is the external-compression step of the coordinate-frame estimates.
-/

open scoped BigOperators InnerProductSpace

namespace SparseStackV3.Op.ExternalCompression

open SparseFock ParsevalFrame SparseStackDistribution Occupation

variable {n d s b : ℕ}
noncomputable section

def lift (F : Frame n d) (X : Vec d s b n) : Vec n s b n :=
  fun z i => ∑ a, F.u i a * X z a

                                                            
                                 

theorem lift_eq_analyze (F : Frame n d) (X : Vec d s b n)
    (z : RawSample s b n) (i : Fin n) :
    lift F X z i = analyze F (WithLp.toLp 2 (X z)) i := by
  simp [lift, analyze, PiLp.inner_apply, mul_comm]

                                                             
                                       
                                                          
                                    

                                                                                   
            
                          
                                                            
                                  
                     

theorem nrm2_lift (hb : 0 < b) (F : Frame n d) (X : Vec d s b n) :
    nrm2 hb (lift F X) = nrm2 hb X := by
  apply FiniteLaw.expect_congr
  intro z
  have h := analysis_energy_eq F (WithLp.toLp 2 (X z))
  rw [normSq_eq_norm_sq, EuclideanSpace.real_norm_sq_eq] at h
  simpa [← lift_eq_analyze, pow_two] using h

                                                                 
                                      
                     
     

                                                                      
                                         
                             
         
                                                
                                                             
                                                        

                                                                     
                                    
                                          

                                                             
                                                                                         
            
                                                                  
                      
                                                                               

                                                              
                                                                                           
            
                                                                   
                      
                                                                               

                                                                           
                                                                         
                                                                   
                                                      
                                           
                                                               
                                                        
      
                                                                                  
                                     
                                        

end
end SparseStackV3.Op.ExternalCompression
