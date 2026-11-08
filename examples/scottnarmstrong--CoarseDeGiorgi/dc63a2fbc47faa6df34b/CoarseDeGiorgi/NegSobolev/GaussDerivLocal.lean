module

public import CoarseDeGiorgi.NegSobolev.GaussDerivDomination
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Coordinate differential formulas and local domination of Gaussian derivatives. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators Topology

namespace CoarseDeGiorgi.NegSobolev

                                                                     
                                                                                    
                      
                                                                      

                                                               
                                                                         
                                                           

                                                                   
                                                 
                                                      
                                                 
                                                                                          
                                                                      
                                                                   
                        
                                            
                           
     

                                                             
                                       
                                           
                                                            
                                    
                                            
                                                          
                                             

                                                
                                                                            
                                             
                                                                                             
                                                           
                                                         
                                                                                          
                                                                             
                                 
                                                                                      
                                                                        
                                                                                   
           
                                                 
        
                                                                                             
                                                                  
                    
                                                                                     
                                               
                                            
                   
           
                                                          

/-- A ball whose radius is the square root of the time admits one wider Gaussian
as a common integrable envelope for all shifts of its center. -/
theorem gaussDeriv_gaussian_local {d : ℕ} (s : ℝ) (hs : 0 < s)
    (x x₀ y : Vec d) (hx : ‖x - x₀‖ < Real.sqrt s) :
    gaussianKernel s hs (x - y) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4) *
        gaussianKernel (2 * s) (by positivity) (x₀ - y) := by
  apply gaussianKernel_le_double_time
  have hb : vecNormSq (x₀ - x) ≤ (d : ℝ) * s := by
    unfold vecNormSq vecDot
    have hc (i : Fin d) : (x₀ i - x i) ^ 2 ≤ s := by
      have hi := norm_le_pi_norm (x - x₀) i
      have hsq := sq_le_sq₀ (abs_nonneg ((x - x₀) i)) (Real.sqrt_nonneg s)
      have hi' : |(x - x₀) i| ≤ Real.sqrt s :=
        (show |(x - x₀) i| ≤ ‖x - x₀‖ by simpa only [Real.norm_eq_abs] using hi).trans hx.le
      have h := hsq.mpr hi'
      rw [sq_abs, Real.sq_sqrt hs.le] at h
      simpa only [Pi.sub_apply, sub_sq_comm] using h
    calc
      _ = ∑ i : Fin d, (x₀ i - x i) ^ 2 := by simp only [Pi.sub_apply, pow_two]
      _ ≤ ∑ _i : Fin d, s := Finset.sum_le_sum fun i _ => hc i
      _ = _ := by simp
  have htri := vecNormSq_add_le (x - y) (x₀ - x)
  rw [show x - y + (x₀ - x) = x₀ - y by abel] at htri
  linarith only [htri, hb]

end CoarseDeGiorgi.NegSobolev
