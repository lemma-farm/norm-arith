import APFoundation
import MajorArcPrimePairWeld
import Mathlib.NumberTheory.AbelSummation

/-!
# Abel weld for the pointwise MAP major-arc estimate

MRT Proposition 4.1 cites Nathanson, Lemma 8.3.  Once the rational-point
prefix discrepancy is known, the only analytic operation in that lemma is
Abel summation against the small phase `e(beta t)`.  This file certifies that
operation with literal constants.  It deliberately does not package the
desired prime-polynomial estimate as an assumption.
-/

namespace MAPPointwiseMajorArc

open AddCircle Finset MeasureTheory Set
open MAPMajorArcWeld
open scoped ArithmeticFunction

noncomputable section

/-- A completely quantitative form of the Abel-summation step in Nathanson,
Lemma 8.3.  If every prefix of `c` between `a` and `b` has norm at most `E`,
then twisting by a differentiable phase of endpoint norm at most one and
derivative norm at most `D` costs at most
`2 E + (b-a) D E`.

The two endpoint copies of `E` are retained because this version is designed
for an arbitrary dyadic interval.  In the prefix version with `a = 0` and
vanishing initial coefficient, one of them disappears. -/
theorem norm_sum_Ioc_mul_le_of_prefix_bound
    (c : ℕ → ℂ) {f : ℝ → ℂ} {a b E D : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b))
    (hf_a : ‖f a‖ ≤ 1) (hf_b : ‖f b‖ ≤ 1)
    (hderiv : ∀ t ∈ Set.Icc a b, ‖deriv f t‖ ≤ D)
    (hprefix : ∀ t ∈ Set.Icc a b,
      ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ E) :
    ‖∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k‖ ≤
      2 * E + (b - a) * D * E := by
  let C : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
  have hAbel := sum_mul_eq_sub_sub_integral_mul c ha hab hf_diff hf_int
  have hCa : ‖C a‖ ≤ E := hprefix a ⟨le_rfl, hab⟩
  have hCb : ‖C b‖ ≤ E := hprefix b ⟨hab, le_rfl⟩
  have hend : ‖f b * C b - f a * C a‖ ≤ 2 * E := by
    calc
      ‖f b * C b - f a * C a‖ ≤
          ‖f b * C b‖ + ‖f a * C a‖ := norm_sub_le _ _
      _ = ‖f b‖ * ‖C b‖ + ‖f a‖ * ‖C a‖ := by
        simp only [norm_mul]
      _ ≤ 1 * E + 1 * E := by gcongr
      _ = 2 * E := by ring
  have hInt :
      ‖∫ t in Set.Ioc a b, deriv f t * C t‖ ≤
        (D * E) * (b - a) := by
    have hbound :
        ‖∫ t in a..b, deriv f t * C t‖ ≤ (D * E) * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have ht' : t ∈ Set.Icc a b := by
        rw [Set.uIoc_of_le hab] at ht
        exact Set.Ioc_subset_Icc_self ht
      rw [norm_mul]
      exact mul_le_mul (hderiv t ht') (hprefix t ht')
        (norm_nonneg _) hD
    rw [← intervalIntegral.integral_of_le hab]
    simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using hbound
  rw [hAbel]
  change ‖f b * C b - f a * C a -
      ∫ t in Set.Ioc a b, deriv f t * C t‖ ≤ _
  calc
    ‖f b * C b - f a * C a -
        ∫ t in Set.Ioc a b, deriv f t * C t‖ ≤
        ‖f b * C b - f a * C a‖ +
          ‖∫ t in Set.Ioc a b, deriv f t * C t‖ := norm_sub_le _ _
    _ ≤ 2 * E + (D * E) * (b - a) := add_le_add hend hInt
    _ = 2 * E + (b - a) * D * E := by ring

/-! ## The literal small Fourier phase -/

                                                                      
                                     
                                     
                                                             

                                               
                                   
                                                                          
                                                
                                                             
                                                                      
                                                   

                                         
                                    
             
                                                     
                                                         
             
        
                                                            

                                               
                                                            
                                                        
                          
                                                                    
                   
                             
          

                                                                        
                                 
                                                        
                             
                                           
                                 
                                           
                                
                                     
                                                     
                                                       
                                                                           
              
                                                            
                                         
                                       
                                                
              
                                                    
                                                   
                                              
                                                      
                                                       
                              
                              
              
                                    
                 

                                                                               

                                                         
                                                                    
                        
                         
         
           
      

                                                                             
                                    
                                                           
                                                             
                                                  
                      
                                            
                                              
                             

                                                                     
                                      
                                            
                                                      

                                              
                                            
                                            
                                                    
                                                             
                                   
                                                                    
           
                                                                       
                                               
                            
            
                        
                                         
                                           
         
                                              
                                    
                                                                    
      

                                                                              
                                                                            
                                                                        
                                               
                                                                
                                                   
                                       
                               
                                                   
                                             
                                                      
                                                                
                                               
                                                
                                     
                                                            
                                                                
                            

                                          

                                                          
                                             
                      
                                            
                                          

                                                                             
                                                                            
                                                                      
                                 
                                                          
                                                           
                                     

                                      
                                            
                                            
                                                    
                                     
                                                                 
           
                                               
                            
            
                        
                                         
                                           
         
                                         
                                    
                                                                    
      

                                                                           
                                                                        
                                                                        
                  
                                                                  
                                                   
                                       
                                                  
                                             
                                                      
                                                                  
                                               
                                             
                                     
                                      
                                                        
                                             
                                     
                                                                     
              
                                                            
                                    
                                                     
            
                                                 
                                                               
                 
                                
                                              
                                                      
                                                       
                                                                     
                                                     
                                                              
                                
                                              
                                                      
                                      
                                                                   
                                                                 
                                             
                                                 
              
                                       
               
                              
                                                       
                                                    
                                                                             
                
                                                                 
                                                             
                                                                   
                              
                                                       
                                            
                                                     
                                             
                                                            
                            
                                                                 
                                             
                                    
                                                                 
                                    
            
                                                            
                            
                                           
                                                                  
              
                   
          
            
                            
                   
                                                    
                                                      
                                              
                                         
              
        
                  
                                          
                                            
                                                        
                                           
                                                                  
              
                   
          
                                                                      
               
                                                   
                                    
                                           
                                                
                                 
                 
        
                            
                                                                
                             
                                   
                                                                
                                   
                                                               
        
                                           
                                                                  
                                                         
                            
                             
                                                               
                          
                  
                                          
                                                   
                                                            
              
                                          
                                   
                                      
                 
                                                   
                                                          
           
          
                                                                              
                                                                   
             
                                   
                                              
                                  
                                         
              
                                   
           
             
        
                   
      
                                        
                                           
                                             
                                                               
                                                        
                               
                                                 
                                                       
          

                                                            

                                            
                                  
                                          
                                                         
                       
                        
                                        
                                         
                                                   
                                                                
                                                             
         
           
            

                                  
                                  
                                          
                                                          
                                           
                                         
         
      

                                                                              
                                                                              
                                                        
                                          
                                                             
                           
                                              
                                                       
           
                                      
                  
                                                               
                                                                   
        
                           
                
                                        
           
                    
                                          
                                  
             
                                   
                
                            
                                                    
              
                                                                    
                                             
                                            
                            
            
      
                                    
           
                     
                     
                                            
                                                                                     
                             
                                                
                                                  
                    
                                           
                
                                                       
                          
                        
         
                                                    
              
                               
                                              
                                                      
                          
                                                        
                                             
        

end

end MAPPointwiseMajorArc
