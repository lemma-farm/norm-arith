module

public import Sidon.Analysis.VanDerCorput
public import Sidon.Combinatorics.IntervalSize
public import Mathlib.Tactic

@[expose] public section

/-! # Correlation estimates for a Sidon set and its interval model -/

noncomputable section

open scoped ComplexConjugate

namespace Sidon

def intervalModel (N : ℕ) (S : Finset ℤ) : ℤ →₀ ℂ :=
  ((S.card : ℝ) / N) • indicatorFinsupp (interval N)

def correlationError (N : ℕ) (S : Finset ℤ) (H : ℕ) (f g : ℤ →₀ ℂ) : ℝ :=
  (fejerWeight H).sum
    (fun h w => w * |(S.card : ℝ) ^ 2 / N - (correlation f g h).re|)

                                                             
                                      

theorem correlation_indicatorFinsupp (S T : Finset ℤ) (h : ℤ) :
    correlation (indicatorFinsupp S) (indicatorFinsupp T) h =
      (((S.filter fun x => x + h ∈ T).card : ℕ) : ℂ) := by
  classical
  rw [correlation, Finsupp.sum, support_indicatorFinsupp, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x hx
  simp [indicatorFinsupp_apply, hx]

theorem re_correlation_indicatorFinsupp (S T : Finset ℤ) (h : ℤ) :
    (correlation (indicatorFinsupp S) (indicatorFinsupp T) h).re =
      ((S.filter fun x => x + h ∈ T).card : ℝ) := by
  rw [correlation_indicatorFinsupp]
  simp

                                                                  
                                                                          
                                   
      

                                                             
                                                                               
                                      
                      
                                                 

                                                                         
                                                                          
                                      
            

                                                             
                                                        
                                                                          
                                      
                                                           
                                
                   
                                               
                                               
                                                                     
                      

                                                              
                                                                             
                  
                                                

                                                                           
                                                                 
                                                                                  
                                                                  
                                    
     

                                                                    
                           
                                                                      
                                                          
                                         
                                                                  
                                                    
                                              
                                                                                    
                                   
                                                                              
                                                          
                
        
                                 

                                                   
                                                                  
                                                                   
                                                                   
                                                              
                                                    
                                      
             
                     
                                                             
              
                                                
                                                  
                                                                                   
                                        
                                               
                                                 
                                                 
              
                                                
                                                  
                                                                                   
                                         
                                                           
                                                 

                                                                             
                                                                 
                         
                                                       
                                 
                                                              

                                                          
                                                                       
                                                                     
                                              
                         
                                   
            
                                  
                                              
                                       
                                                              
                                      
                                                     
      
                                                    
                                                         
                                             
                                                           
                                                     

theorem interval_overlap_card {N : ℕ} {h : ℤ} (hh : |h| ≤ (N : ℤ)) :
    (((interval N).filter fun x => x + h ∈ interval N).card : ℝ) =
      (N : ℝ) - |(h : ℝ)| := by
  classical
  have hh' := abs_le.mp hh
  by_cases hh₀ : 0 ≤ h
  · have hset : ((interval N).filter fun x => x + h ∈ interval N) =
        Finset.Icc 1 ((N : ℤ) - h) := by
      ext x
      simp only [Finset.mem_filter, mem_interval, Finset.mem_Icc]
      omega
    rw [hset]
    have hcast : ((Finset.Icc 1 ((N : ℤ) - h)).card : ℤ) = (N : ℤ) - h := by
      calc
        _ = ((N : ℤ) - h) + 1 - 1 := Int.card_Icc_of_le 1 ((N : ℤ) - h) (by omega)
        _ = _ := by omega
    have hreal : ((Finset.Icc 1 ((N : ℤ) - h)).card : ℝ) = (N : ℝ) - h := by
      exact_mod_cast hcast
    rw [hreal, abs_of_nonneg (show (0 : ℝ) ≤ h by exact_mod_cast hh₀)]
  · have hset : ((interval N).filter fun x => x + h ∈ interval N) =
        Finset.Icc (1 - h) (N : ℤ) := by
      ext x
      simp only [Finset.mem_filter, mem_interval, Finset.mem_Icc]
      omega
    rw [hset]
    have hcast : ((Finset.Icc (1 - h) (N : ℤ)).card : ℤ) = (N : ℤ) + h := by
      calc
        _ = (N : ℤ) + 1 - (1 - h) := Int.card_Icc_of_le (1 - h) (N : ℤ) (by omega)
        _ = _ := by omega
    have hreal : ((Finset.Icc (1 - h) (N : ℤ)).card : ℝ) = (N : ℝ) + h := by
      exact_mod_cast hcast
    rw [hreal, abs_of_neg (show (h : ℝ) < 0 by exact_mod_cast (lt_of_not_ge hh₀))]
    ring

theorem re_correlation_intervalModel_self (N : ℕ) (S : Finset ℤ) (h : ℤ) :
    (correlation (intervalModel N S) (intervalModel N S) h).re =
      ((S.card : ℝ) / N) ^ 2 *
        (((interval N).filter fun x => x + h ∈ interval N).card : ℝ) := by
  rw [intervalModel, correlation_real_smul_left, correlation_real_smul_right,
    Complex.smul_re, Complex.smul_re, re_correlation_indicatorFinsupp]
  simp only [smul_eq_mul]
  ring

theorem intervalModel_self_deficit {N : ℕ} (hN : 0 < N) (S : Finset ℤ)
    {h : ℤ} (hh : |h| ≤ (N : ℤ)) :
    |(S.card : ℝ) ^ 2 / N - (correlation (intervalModel N S) (intervalModel N S) h).re| =
      (S.card : ℝ) ^ 2 / (N : ℝ) ^ 2 * |(h : ℝ)| := by
  rw [re_correlation_intervalModel_self, interval_overlap_card hh]
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have heq : (S.card : ℝ) ^ 2 / N - ((S.card : ℝ) / N) ^ 2 *
      ((N : ℝ) - |(h : ℝ)|) = (S.card : ℝ) ^ 2 / (N : ℝ) ^ 2 * |(h : ℝ)| := by
    field_simp
    ring
  rw [heq, abs_of_nonneg (by positivity)]

theorem intervalModel_correlationError_le {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (hHN : H ≤ N) (S : Finset ℤ) :
    correlationError N S H (intervalModel N S) (intervalModel N S) ≤
      (S.card : ℝ) ^ 2 * H / (N : ℝ) ^ 2 := by
  unfold correlationError
  apply sum_fejerWeight_mul_le H hH
  intro h hh
  have habs : |h| ≤ (N : ℤ) := by
    have := abs_lt_of_mem_support_fejerWeight H hh
    exact le_trans this.le (by exact_mod_cast hHN)
  rw [intervalModel_self_deficit hN S habs]
  have hh' : |(h : ℝ)| ≤ (H : ℝ) := by
    exact_mod_cast (abs_lt_of_mem_support_fejerWeight H hh).le
  calc
    (S.card : ℝ) ^ 2 / (N : ℝ) ^ 2 * |(h : ℝ)| ≤
        (S.card : ℝ) ^ 2 / (N : ℝ) ^ 2 * H := by gcongr
    _ = (S.card : ℝ) ^ 2 * H / (N : ℝ) ^ 2 := by ring

                                                                      
                            
                                      
                                     
                                                                               
                                                                          
                                                                  
                                                          
                                                        
                 
                                               
                                     
                                                                               
                  
                                                                    
                                 

                                                       
                                                   
                                                                        
                                                                                    
                                                   
                     
           
                                                         
                    
                                                                       
                                      
                            
                                                           
        
                                                                          
                         
                                                                                
               
            
                        
                                                                                         
                                                              

                                                                           
                                   
                                                                      
                                         
                                                                           
                                                             
                                   
                     
                                                
                                                       
              
                                   
                                                                     
                                              
                           
                                                     
        
      
                                                                      
                                                            
                                                                        
                                              
                             
               
                                                                               
                                
                                                            
                                       
                                                                             
                                                                               
                                                                       
                                                 
          
                                                                          

                                                                    
                                                                         
                                                                      
                                      
                                                                       
                                                 
                                                             
                                         
                                             
                                         
                                                   
                                
                                                        
              
        
                                                            
                                          
                                                       
                                         
                                              
                                                   
                                                                         
                                                    
                     
          

end Sidon
