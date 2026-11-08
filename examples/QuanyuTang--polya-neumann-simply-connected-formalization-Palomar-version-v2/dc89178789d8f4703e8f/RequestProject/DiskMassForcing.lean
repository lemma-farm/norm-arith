module

public import RequestProject.DiskAreaBessel
                                              
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# One full Sobolev derivative from physical disk mass forcing

The nonzero-mode coefficient has multiplier sqrt(1+|n|)/(sqrt(2π)|n|).
The area Bessel estimate bounds the entire H¹ Fourier norm, rather than
only the individual coefficients. Frequency zero is removed explicitly.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate

def diskMassForcingScale (m : ℕ) : ℝ :=
  Real.sqrt ((m + 2 : ℕ) : ℝ) / (Real.sqrt (2 * π) * ((m + 1 : ℕ) : ℝ))

                                                          
                    
                                                       
                                                             
                                                   
                                                        

private theorem diskMassForcingScale_weight (m : ℕ) (a : ℂ) :
    (((m + 2 : ℕ) : ℝ) * ‖(diskMassForcingScale m : ℂ) * a‖) ^ 2 ≤
      (4 / (2 * π)) * (((m + 2 : ℕ) : ℝ) * ‖a‖ ^ 2) := by
  have hk : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hweightPos : 0 < ((m + 2 : ℕ) : ℝ) := by positivity
  have hratio : ((m + 2 : ℕ) : ℝ) ^ 2 ≤ 4 * ((m + 1 : ℕ) : ℝ) ^ 2 := by
    have hle : ((m + 2 : ℕ) : ℝ) ≤ 2 * ((m + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    calc
      ((m + 2 : ℕ) : ℝ) ^ 2 ≤ (2 * ((m + 1 : ℕ) : ℝ)) ^ 2 :=
        (sq_le_sq₀ hweightPos.le (by positivity)).mpr hle
      _ = 4 * ((m + 1 : ℕ) : ℝ) ^ 2 := by ring
  have hscale : 0 ≤ diskMassForcingScale m := by unfold diskMassForcingScale; positivity
  have hw : (((m + 2 : ℕ) : ℝ) * diskMassForcingScale m) ^ 2 ≤
      (4 / (2 * π)) * ((m + 2 : ℕ) : ℝ) := by
    rw [mul_pow, diskMassForcingScale, div_pow, mul_pow,
      Real.sq_sqrt hweightPos.le, Real.sq_sqrt Real.two_pi_pos.le]
    calc
      _ ≤ (4 * ((m + 1 : ℕ) : ℝ) ^ 2) *
          (((m + 2 : ℕ) : ℝ) / ((2 * π) * ((m + 1 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := by field_simp [hk.ne', Real.pi_ne_zero]
  calc
    _ = (((m + 2 : ℕ) : ℝ) * diskMassForcingScale m) ^ 2 * ‖a‖ ^ 2 := by
      rw [norm_mul, Complex.norm_of_nonneg hscale]
      ring
    _ ≤ ((4 / (2 * π)) * ((m + 2 : ℕ) : ℝ)) * ‖a‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = _ := by ring

private theorem diskMassForcing_sector (M : ℕ → ℂ) (B : ℝ)
    (hs : Summable (fun m => ((m + 1 : ℕ) : ℝ) * ‖M m‖ ^ 2))
    (hB : (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * ‖M m‖ ^ 2) ≤ π * B) :
    Summable (fun m => (((m + 2 : ℕ) : ℝ) *
      ‖(diskMassForcingScale m : ℂ) * M (m + 1)‖) ^ 2) ∧
    (∑' m : ℕ, (((m + 2 : ℕ) : ℝ) *
      ‖(diskMassForcingScale m : ℂ) * M (m + 1)‖) ^ 2) ≤ 2 * B := by
  let f : ℕ → ℝ := fun m => ((m + 1 : ℕ) : ℝ) * ‖M m‖ ^ 2
  let e : ℕ → ℝ := fun m => (((m + 2 : ℕ) : ℝ) *
    ‖(diskMassForcingScale m : ℂ) * M (m + 1)‖) ^ 2
  have hi : Function.Injective (fun m : ℕ => m + 1) := by
    intro m n h
    change m + 1 = n + 1 at h
    exact Nat.add_right_cancel h
  have ht : Summable (fun m : ℕ => f (m + 1)) := hs.comp_injective hi
  have htail : (∑' m : ℕ, f (m + 1)) ≤ π * B :=
    (tsum_comp_le_tsum_of_inj hs (fun m => by positivity) hi).trans hB
  have he (m : ℕ) : e m ≤ (4 / (2 * π)) * f (m + 1) := by
    simpa only [e, f, Nat.add_assoc] using diskMassForcingScale_weight m (M (m + 1))
  have hse : Summable e := Summable.of_nonneg_of_le (fun m => sq_nonneg _) he
    (ht.mul_left (4 / (2 * π)))
  refine ⟨hse, ?_⟩
  calc
    _ ≤ ∑' m : ℕ, (4 / (2 * π)) * f (m + 1) :=
      hse.tsum_le_tsum he (ht.mul_left _)
    _ = (4 / (2 * π)) * ∑' m : ℕ, f (m + 1) := tsum_mul_left
    _ ≤ (4 / (2 * π)) * (π * B) := mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 2 * B := by field_simp [Real.pi_ne_zero]; ring

                                                                      
                                    
                                                       
                                                            
                                                          
                                                 
                                                 
                                                           
                                    
                                                                                 
                                                              
                                    
                                                           
                                                     
                                                     
                                                               
                                         
      
                                                                 
             
                           
                        
               
                                                          
                                    

                                                           
                                             
                                                              
                                                                              
                                                                         
                                                
                                                                         
                                                
                                                                                 
                                                 
                                                    
                                                 
                                                    
                                     
                                                                          
                                                  
                                                               
                                                                           
                                                                
                                     
           
             
        
                                                                  
                                                            
                                                                               
                                                                         
                                     
           
             
        
                                                                                            
             
                 
                                                     
                                                                                   
                             
                              
                                                   
                                                  
                         

                                                                      
                                                                                              
              
              
                  
                                           
                 
                                          
                                                                                               
                                                                              
                
                                      
                                                                                                   
                                                                              

                                                                             
                                                                       
              
              
                  
                                           
                 
                                          
                                                                                               
                             
              
                
                                      
                                                                                                   
                         
          

                                                              
                                                                    
                                  
                                                        
                                                                                          
                    
                
            
                                                                 
                                                                             
                     
                
            
                                                               
                                                        
                                  
        

                                                                
                                            
                                                               
                    
                                                                             
                                                                     
                                           
                                             
                 
                                                          

                                                        
                                                                  

                                                                           
                                                                               

end PolyaNeumann

end
