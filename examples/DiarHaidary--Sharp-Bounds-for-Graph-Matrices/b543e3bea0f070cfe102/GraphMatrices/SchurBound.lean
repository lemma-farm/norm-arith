import GraphMatrices.SpectralNorm

/-! The rectangular Schur bound for the actual Euclidean operator norm. -/

namespace GraphMatrices

noncomputable section
open scoped BigOperators

private theorem weighted_sum_sq_le
    {ι : Type*} [Fintype ι] (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * f i) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun i => Real.sqrt (w i))
    (g := fun i => Real.sqrt (w i) * f i)
  have hprod (i : ι) : Real.sqrt (w i) * (Real.sqrt (w i) * f i) = w i * f i := by
    rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  simp only [hprod, mul_pow, Real.sq_sqrt (hw _)] at h
  exact h

                          
                                                         
                                                          
                                   
                                     
                                            
           
                                                                  
         
                     
                                                                 
               
                                                       
                                
                                                                      
                                           
                                                                             
                                                                      
                             
                             
        
                                                                        
                                       
                                              
                                                          
                                         
                                            
                                                                                  
             
                                                                      
        
                                                  
                                             
                                                       
                                              
               
                                  
                 
                           
                                      
                                            
                                           
                                                             
                                             
            
                                                                       
                                                 
                                                           
                                                                             
                                  
                                                             

end
end GraphMatrices
