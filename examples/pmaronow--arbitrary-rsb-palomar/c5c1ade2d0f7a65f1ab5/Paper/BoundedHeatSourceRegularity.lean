module

public import Paper.ParisiDuhamelWeak
public import Paper.HeatGradient
public import Paper.GaussianBoundedSmoothing

@[expose] public section


/-!
# Regularity of the heat Volterra potential of a bounded measurable source

The source may be discontinuous in both variables. Spatial differentiation
acts on the genuine Gaussian kernel; the inverse-square-root time singularity
is integrable. The source is never assumed to have a classical derivative.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open scoped Topology NNReal

namespace Paper

def boundedHeatGradientSource (β : ℝ) (F : ℝ × ℝ → ℝ) (t s x : ℝ) : ℝ :=
  heatGradient (β ^ 2 * (s - t)) (fun y => F (s, y)) x

def boundedVolterraGradient (β : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s, if p.1 < s then boundedHeatGradientSource β F p.1 s p.2 else 0 ∂parisiTimeMeasure

                                                                    
                         
                                                                                           
                                                    
                                                                                  
                                              
                                                
                                                             
                                                                                       

                                                                  
                                                                        
                                                               
                                                                                
                                                              
                                                        
                                                                               
                                        

theorem norm_boundedHeatGradientSource_le (β : ℝ) (F : ℝ × ℝ → ℝ)
    (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M) (t s x : ℝ) :
    ‖boundedHeatGradientSource β F t s x‖ ≤
      (|β|⁻¹ * gaussianAbsMoment * M) * (Real.sqrt (s - t))⁻¹ := by
  have h := norm_heatGradient_le (β ^ 2 * (s - t)) (fun y => F (s, y)) M
    (fun y => hb (s, y)) x
  apply h.trans_eq
  rw [Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq_eq_abs, mul_inv_rev]
  ring

                                                                    
                                                                     
                                                                              
                                                     
                                                     
                                                                                    
                                                                        

                                                                            
                                                     
                               
                                                                                      
                                                            
                                              
                                                             
                                                                                    
                                                                                

theorem boundedVolterraGradient_eq (β : ℝ) (F : ℝ × ℝ → ℝ)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    boundedVolterraGradient β F (t, x) = ∫ s in t..1, boundedHeatGradientSource β F t s x :=
  integral_parisiTime_lower_triangle (fun s => boundedHeatGradientSource β F t s x) t ht

theorem norm_boundedVolterraGradient_le (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖boundedVolterraGradient β F (t, x)‖ ≤
      2 * M * gaussianAbsMoment / |β| * Real.sqrt (1 - t) := by
  rw [boundedVolterraGradient_eq β F t x ht]
  have hh := intervalIntegral.norm_integral_le_of_norm_le ht.2
    (.of_forall (fun s _ => norm_boundedHeatGradientSource_le β F M hb t s x))
    ((intervalIntegrable_inv_sqrt_sub t 1 ht.2).const_mul (|β|⁻¹ * gaussianAbsMoment * M))
  rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_sub t 1 ht.2] at hh
  exact hh.trans_eq (by ring)

                                                                            
                                                                        
                                                                     
                                        
                                                             
                                                  
                                                
                           
                                                                      
                                                                    
                                                                                     
                                                                  
                                                                
                                                                                     
                                                       
                                                                                    
                                              
                                             
                                                                  
                                                                              
                                 
                                                                   
                                                                                            
                                          
                                                       
                                                     
                                                                    
                                                            
                                                         
                                                                          
                                                                
                                                 
                                                 
                                                          
                                                       
                                            
                                                            
                                                          
                                                            
         
                                                              

                                                           
                                                                     
                                        
                                                                           
                                                                      
                                                                   
                                                 
                                                     
                                                                
                                                                                 

                                                                             
                                                                
                                                                
                                                                       
                                                   
                                                          
                                  
         
                                 
                                                          
                                                                                            
                         
                                                                           
                                                                       
                                                                                                 
                                                      
               
                                                          
                        
                            
                                                    
                                                    
                                  
                                              
                                                   
                                                                                             
                              
                                                    
                                   
                     
                                               
                                                                  
                                                                                          
                                   
                     

end Paper
