module
-- Reversible module-visibility port of the audited development.
/- Narrow actual normalized-zeta source and kernel port from Scott McColm,
MIT-0, exact pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../../third_party/twelfth/SQUARE_NORMALIZED_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0. -/
public import MathCollab.Density.Stronger.Fourth.SquareContour
public import Mathlib
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped ComplexConjugate Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

theorem gammaReal_conj (z : ℂ) : Complex.Gammaℝ (conj z) = conj (Complex.Gammaℝ z) := by
  have hpow := Complex.cpow_conj (Real.pi : ℂ) (-z / 2)
    (by rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm)
  simp only [map_div₀, map_neg, map_ofNat, conj_ofReal] at hpow
  simp only [Complex.Gammaℝ, map_mul, ← Complex.Gamma_conj,
    map_div₀, map_ofNat, hpow]


                                      
                                          
                            
                    
                                                             
                                  
         
                       
                        
                                  
                                                                      
                                                
              
                
                                        
                                    
              


                                          
                              
                                 
                                                          
                                              
                                     

                                                  
                                              
                                        
                                                                    
                                                                       
                                                    
             
                                 
                    
                              
            
                                                                 
                                          
                            
                                


                                                                         
                                                    
                                 
                                                    
                                                        
                              
                                 
                                                              
                                                                                       
                                                                                       
                                                                                    
                                                                                               
                                          
                                        
                                                                     
                     
                                            
      

                                              
                                                                            
                                                                            
                                                                                               
                              
            
                                        
                                                                      
                                                                                             
                    


                                                                           

                                                           
                                                 
                                                                     
                                                                          

                                                
                                                          
                                                             
                                                        
                                                   
                                     
        
                                                            
                                                          
                                                                        
                                                                        
                                                     
      

                                                
                                                                             
                                                             
                                
                            
                                                                        
                                                       
                                                                

                                                   
                                                                                
                                                                                               
                                                                                  
      

                                                            
                                                    
                                  
                                                                                    
                                                     
                                                                      
                                            
                                                                                            
                                                                       
                                                                          
                                                                                  
                                                                                               
                       
                                  
                                                                                   


                                       
                                                                 

                                                           
                                                                 
                                      

                                          
                                                                   
                                                                             
                                                
                                              

                                                
                                         
                                                       
                                                  

                                                       
                                                                   
                                                       
                                                         
                                             
                                      
                                                                                    

theorem norm_zetaSquareGammaNormalization (t : ℝ) :
    ‖zetaSquareGammaNormalization t‖ =
      ‖Complex.Gammaℝ (afeCriticalPoint (-t))‖^2 := by
  have he : ‖Complex.Gammaℝ (afeCriticalPoint (-t))‖ =
      ‖Complex.Gammaℝ (afeCriticalPoint t)‖ := by
    have hs : afeCriticalPoint (-t) = conj (afeCriticalPoint t) :=
      afeCriticalPoint_neg_eq_star t
    rw [hs, gammaReal_conj, Complex.norm_conj]
  rw [zetaSquareGammaNormalization, norm_mul, he, pow_two]

theorem norm_gammaSquare_div_zetaSquareGammaNormalization (t : ℝ) (w : ℂ) :
    ‖Complex.Gammaℝ (afeCriticalPoint (-t)+w)^2 /
        zetaSquareGammaNormalization t‖ =
      ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ := by
  rw [norm_div, norm_pow, norm_zetaSquareGammaNormalization,
    norm_pow, norm_div, div_pow]


def zetaSquarePoleShift (t : ℝ) (w : ℂ) : ℂ :=
  ((afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
    (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)))) ^ 2

theorem criticalPoint_pole_product (t : ℝ) :
    afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
  unfold afeCriticalPoint
  push_cast
  ring_nf
  simp

                                                       
                             
                                                                             
                                           
                                        
                     

theorem poleShift_sub_one_identity (t : ℝ) (w : ℂ) :
    (afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
        (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) - 1 =
      (2 * (t : ℂ) * I * w - w ^ 2) / ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
  have hne : ((1 / 4 + t ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  rw [criticalPoint_pole_product]
  rw [div_sub_one hne]
  congr 1
  unfold afeCriticalPoint
  push_cast
  ring_nf
  simp

theorem norm_poleShift_linear_sub_one_le {t : ℝ} (ht : 0 < t)
    {w : ℂ} (hw : ‖w‖ ≤ t / 2) :
    ‖(afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
        (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) - 1‖ ≤ 3 * ‖w‖ / t := by
  rw [poleShift_sub_one_identity, norm_div]
  have hn : ‖2 * (t : ℂ) * I * w - w ^ 2‖ ≤ 2 * t * ‖w‖ + ‖w‖ ^ 2 := by
    simpa only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, norm_I, mul_one] using
      norm_sub_le (2 * (t : ℂ) * I * w) (w ^ (2 : ℕ))
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / 4 + t ^ 2)]
  apply (div_le_div_of_nonneg_right hn (by positivity)).trans
  apply (div_le_div_iff₀ (by positivity) ht).mpr
  have hwt : ‖w‖ * t ≤ t ^ 2 / 2 := by nlinarith
  nlinarith [norm_nonneg w,
    mul_nonneg (norm_nonneg w) (show 0 ≤ t ^ 2 - ‖w‖ * t by nlinarith)]

theorem norm_zetaSquarePoleShift_le {t : ℝ} (ht : 0 < t)
    {w : ℂ} (hw : ‖w‖ ≤ t / 2) : ‖zetaSquarePoleShift t w‖ ≤ 9 := by
  have h := norm_poleShift_linear_sub_one_le ht hw
  have hfrac : 3 * ‖w‖ / t ≤ 3 / 2 := (div_le_iff₀ ht).mpr (by linarith)
  have hn := norm_le_norm_sub_add
    ((afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
      (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)))) (1 : ℂ)
  simp only [norm_one] at hn
  rw [zetaSquarePoleShift, norm_pow]
  nlinarith [norm_nonneg ((afeCriticalPoint (-t) + w) *
    (1 - (afeCriticalPoint (-t) + w)) /
      (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))))]

                                                                
                                                                                   
                                                                            
                                                         
                                                                          
                                                                        
                             
                                             
                              
            
                                
                                    
                              
            
                        
                                                           
      
                                                                               
                    


def zetaFourthKernel (t : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (100*w^2) * hughesYoungAuxiliaryZero w *
    zetaSquarePoleShift t w *
      (Complex.Gammaℝ (afeCriticalPoint (-t)+w)^2 /
        zetaSquareGammaNormalization t) / w

                                        
                                    
                                                                         
                         
                                    
                              
            
                                      
                            
      

                                                                           
                                                                      
                                                                           
                                                                 
                                            
              
                                     
                  
            
                                             
                                          
                                

theorem norm_zetaFourthKernel_vertical (t c u : ℝ) :
    ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ =
      Real.exp (100*c^2-100*u^2) *
        ‖hughesYoungAuxiliaryZero ((c:ℂ)+(u:ℂ)*I)‖ *
        ‖zetaSquarePoleShift t ((c:ℂ)+(u:ℂ)*I)‖ *
        ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+((c:ℂ)+(u:ℂ)*I)) /
          Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ /
        ‖(c:ℂ)+(u:ℂ)*I‖ := by
  have he : (100*((c:ℂ)+(u:ℂ)*I)^2).re = 100*c^2-100*u^2 := by
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  unfold zetaFourthKernel
  rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_exp, he,
    norm_gammaSquare_div_zetaSquareGammaNormalization]

                                                          
                                                
                                               
                                                  
                                                   
                                                                                  
                                
                                    
         
                         
                       
                                                                                  
      



                                                                            
                                                     
                                                         
                                                               
                                                  
                                                    
                                                        
                                                                           
                
                       
                                
                                                                                  
      

end MathCollab.Density.Stronger.Fourth
