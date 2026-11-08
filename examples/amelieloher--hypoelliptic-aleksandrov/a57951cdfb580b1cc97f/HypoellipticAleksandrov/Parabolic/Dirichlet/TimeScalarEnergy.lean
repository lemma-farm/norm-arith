module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDerivativeKernel
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy
public import Mathlib
/-!
# Scalar reverse-time energy representatives

This module constructs the scalar no-defect energy representative attached to
a reverse-time Gelfand weak derivative.  It deliberately does not construct a
Hilbert-valued trace or assert a PDE solvability result.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

                                   
                                                         
                                        
                                  

                                       
                                                         
                                                                      
                          

                                                    
                                                         
                                                                      
                                                                            

                                    
                                                         
                               
                                                             
                                                    
                                                            
                  
                                                                         
                                                                     
                  
                                                          

                                        
                                                         
                                                             
                                                                   
                      
       
                                                            

                                                       
                                                         
                                                             
                                                                      
                                                       
                                                               
                  
                                               
                                                    

                                              
                                                         
                                                           
                                                                   
                                           
                                               
                                                                         
                                                                          
                                                                       
                                             
                                           
                                               
                                                            
                                                             
                                        

                                         
                                                          
                                      
                                                                           
                                                       
                               
                                                                   
                               
                                                                   
                                                               
                                                               
                                                    
                                                    
                                      
                                       
                                                        
                
                                     
                                     
                                                                
                                                                            
                                                  
                                                                        
                                   
                  
                                       
                                       
                                                                   
                                       
              
                                            
                                      
                                     
                  
             
                                
          
                                                                            
               
          
                 
          

                                                                       
                               
                                                                    
                                                                               
                                                                          
                                                                            
            
                                                       
                                                    
      

                                                                              
                                         
                                           
                                                 
                                      
                                                                              
                                         
                                          
                                                                     
                                                                     
                                                                                      
                                                               
                                                      
                                                                               
              
                                            
        
                                                      
                                                 
                                                          
                                                    
                                                                             
                                                 
              
                                
                       
            
      
                                                                         
                       
                                                                             
                                                         
                     
                
                                                                     
                                               
                           
                                                                     
                                                                              
                                                                     
                                            
                                                                          
                                                        
                                         
                                                
                                                                                
                                 
                                                
                                                            
                                 
                                                
                                                            
                   
            
                                    
          

private theorem abs_sq_sub_le_of_bounds
    {a b N delta y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hdelta : 0 ≤ delta) (hy : 0 ≤ y)
    (hdiff : |a - b| ≤ N * delta)
    (hsum : a + b ≤ N * delta + 2 * N * y) :
    |a ^ 2 - b ^ 2| ≤ N ^ 2 * delta ^ 2 + 2 * N ^ 2 * y * delta := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  calc
    (a + b) * |a - b| ≤ (N * delta + 2 * N * y) * (N * delta) := by
      exact mul_le_mul hsum hdiff (abs_nonneg _) (by positivity)
    _ = N ^ 2 * delta ^ 2 + 2 * N ^ 2 * y * delta := by ring

private theorem abs_sqNorm_valueCLM_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x y : H10HilbertGraph hΩ) :
    |‖valueCLM hΩ x‖ ^ 2 - ‖valueCLM hΩ y‖ ^ 2| ≤
      ‖valueCLM hΩ‖ ^ 2 * ‖x - y‖ ^ 2 +
        2 * ‖valueCLM hΩ‖ ^ 2 * ‖y‖ * ‖x - y‖ := by
  let L := valueCLM hΩ
  have hLx : ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
  have hLy : ‖L y‖ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
  have hLsub : ‖L (x - y)‖ ≤ ‖L‖ * ‖x - y‖ := L.le_opNorm (x - y)
  have hx : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by
        congr 1
        abel
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  have hLx' : ‖L x‖ ≤ ‖L‖ * (‖x - y‖ + ‖y‖) :=
    hLx.trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hdiff : |‖L x‖ - ‖L y‖| ≤ ‖L‖ * ‖x - y‖ := by
    calc
      |‖L x‖ - ‖L y‖| ≤ ‖L x - L y‖ := abs_norm_sub_norm_le _ _
      _ = ‖L (x - y)‖ := by rw [L.map_sub]
      _ ≤ ‖L‖ * ‖x - y‖ := hLsub
  have hfactor : ‖L x‖ + ‖L y‖ ≤ ‖L‖ * ‖x - y‖ + 2 * ‖L‖ * ‖y‖ := by
    calc
      ‖L x‖ + ‖L y‖ ≤ ‖L‖ * (‖x - y‖ + ‖y‖) + ‖L‖ * ‖y‖ :=
        add_le_add hLx' hLy
      _ = ‖L‖ * ‖x - y‖ + 2 * ‖L‖ * ‖y‖ := by ring
  exact abs_sq_sub_le_of_bounds (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) hdiff hfactor

private theorem integral_mul_norm_le_sqrt_mul_sqrt
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure ℝ} (f : ℝ → E) (g : ℝ → F)
    (hf : MemLp f (2 : ℝ≥0∞) μ) (hg : MemLp g (2 : ℝ≥0∞) μ) :
    ∫ t, ‖f t‖ * ‖g t‖ ∂μ ≤
      √(∫ t, ‖f t‖ ^ 2 ∂μ) * √(∫ t, ‖g t‖ ^ 2 ∂μ) := by
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (μ := μ) (f := fun t => ‖f t‖) (g := fun t => ‖g t‖)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (by simpa only [ENNReal.ofReal_ofNat] using hf.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using hg.norm)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two] using hholder

                                          
                                      
                                               
                                                        
                                                                          
                                        

private theorem tendsto_integral_abs_valueSq_of_sqNorm
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (μ : Measure ℝ) (u : ℝ → H10HilbertGraph hΩ)
    (uh : ℝ → ℝ → H10HilbertGraph hΩ)
    (hu : MemLp u (2 : ℝ≥0∞) μ)
    (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) (2 : ℝ≥0∞) μ)
    (hU : Tendsto (fun h : ℝ => ∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t,
      |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  let C : ℝ := ‖valueCLM hΩ‖ ^ 2
  have hUsqrt : Tendsto (fun h : ℝ =>
      √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hU.sqrt
  have hfirst : Tendsto (fun h : ℝ =>
      C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hU
  have hsecond : Tendsto (fun h : ℝ =>
      2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ) *
        √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ =>
        2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ))
        (𝓝[>] 0) (𝓝 (2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ)) : Filter ℝ) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hconst.mul hUsqrt
  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => abs_nonneg _
  · filter_upwards [huh] with h huh
    have hdu : MemLp (fun t => uh h t - u t) (2 : ℝ≥0∞) μ := huh.sub hu
    have hLuh : MemLp (fun t => valueCLM hΩ (uh h t)) (2 : ℝ≥0∞) μ :=
      huh.continuousLinearMap_comp (valueCLM hΩ)
    have hLu : MemLp (fun t => valueCLM hΩ (u t)) (2 : ℝ≥0∞) μ :=
      hu.continuousLinearMap_comp (valueCLM hΩ)
    have hleft : Integrable (fun t =>
        |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2|) μ := by
      simpa only [Real.norm_eq_abs, Pi.sub_def] using
        ((hLuh.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).sub
          (hLu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).norm
    have hterm1 : Integrable (fun t =>
        C * ‖uh h t - u t‖ ^ 2) μ :=
      (hdu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
    have hterm2 : Integrable (fun t =>
        2 * C * ‖u t‖ * ‖uh h t - u t‖) μ :=
      by
        apply ((hu.norm).integrable_mul hdu.norm).const_mul (2 * C) |>.congr
        filter_upwards with t
        change 2 * C *
          ((fun x => ‖u x‖) * fun x => ‖uh h x - u x‖) t = _
        simp only [Pi.mul_apply]
        ring
    have hpoint : ∀ t : ℝ,
        |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ≤
          C * ‖uh h t - u t‖ ^ 2 + 2 * C * ‖u t‖ * ‖uh h t - u t‖ := by
      intro t
      simpa only [C] using abs_sqNorm_valueCLM_sub_le hΩ (uh h t) (u t)
    have hmono := integral_mono hleft (hterm1.add hterm2) hpoint
    have hholder := integral_mul_norm_le_sqrt_mul_sqrt
      u (fun t => uh h t - u t) hu hdu
    have hterm2_eq : (∫ t,
        2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ) =
        2 * C *
          (∫ t, ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
      rw [show (fun t : ℝ =>
          2 * C * ‖u t‖ * ‖uh h t - u t‖) =
          fun t => (2 * C) *
            (‖u t‖ * ‖uh h t - u t‖) by
            funext t
            ring, integral_const_mul]
    calc
      (∫ t, |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ) ≤
          ∫ t, C * ‖uh h t - u t‖ ^ 2 +
            2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ := hmono
      _ = C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
          (∫ t, 2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
            rw [integral_add hterm1 hterm2, integral_const_mul]
      _ = C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
          2 * C *
            (∫ t, ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
            rw [hterm2_eq]
      _ ≤ C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
          2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ) *
            √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) := by
            apply add_le_add_right
            simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_left hholder (by positivity : 0 ≤ 2 * C)
  · simpa only [add_zero] using hfirst.add hsecond

                                                           
                                                         
                                       
                                             
                                         
                                                              
                                                      
                                                
                                   
              
                                                          
                                                                 
                                                              
                                                   
                                                   
                                
                                                                
                                                                            
               
                                                   
                                       
                                                         
                                                                        
                                   
                                                            
                                                 
                                                   
                                                                               
             

                                                            
                                                         
                                       
                                             
                                         
                                                               
                                                      
                                                
                                   
              
                                                          
                                                                 
                                                              
                                                   
                                                   
                                
                                                                 
                                                                            
               
                                                   
                                        
                                                          
                                                                         
                                   
                                                             
                                                 
                                                   
                                                                                
             

                                                            
                                                   
                                                 
                                                             
                                            
                                                                          
                                                         
                                     
                          
                                            
           
                                     
                        
                
                                    
                                                                  
                          
                                                
                       
                           
                         
                                   
                                                                   
                                                                     
                                                                             
          
                                         
                                                                               
                                                 
                                 
                               
                                         
                                           
                             
                       
                                        
                   
                
                                                            
                                                               
                                                   
                                          
                                                       
                                                             
                                   
                                                            
                                              
                                                           
                   
                               
                                                               
                                                               
                                                           
                                                    
                                                        
                                
                         
                       
      

                                              
                                                           
                                        
                                                                

                                                  
                                                           
                                                                      
                                                  
                                       

                                           
                                       
                                                                    

                                                   
                                                           
                                                                     
                                                                        
                                              
                                                                
                                                 
                                                                
                           

                                    
                                 
                                        
                                                           
                                                       
                                     
                                                                  
                                                                         
                                                                                   
                                         
              
                                                          
                                                                             
                                                 
                                                
                                                                                  
                                                 
                                                               
                                     
                                                                                 
                                                                                        
                                                                            
                                                                                       
                      
                                                              
                                          
                                                                   
                                                                    
                                
                                                                  
                                                          
                                                     
                                                                           
                                                                     
                         
                                                                    
                                                                   
          
                                                               
                                                                   
                                
                                                 
                                                       
                                                                         
                                     
                                        
                                                                       
                                     
                                                 
                                                      
                                                                   
                                                 
                                 
                                                                             
                                                                      
                                                                                          
                                         
                                      
                                                                                  
                                                                            
               
                                        
                                                                                     
                                      
                                                                                        
                                                                            
               
                               
                                                                
                                                                          
                                                                               
                                                                                        
                                                                            
                                                                                     
                                                                                 
                     
                                                     
                                                                         
                          
                                                
              
                               
                             
                           
                                                            
              
                                                                             
                                                                          
                                        
                                                                       
                                                                              
                                       
                                                                               
                                                                        
            
                                     
                                                 
                                                              
                                                                
                          
                                          
            
                                                                      
                                                                
                                                       
                                                                           
                                                                    
          

                                                     
                                                         
                                                             
                                                                                
                                                                                  
                                                                                    
                       

                                                          
                                                                 
                                     
                                                                       
                                            
                                                                     
                       
            

                                                     
                                                         
                                                           
                                     
                                                             
                             
                                                                         
                                                 
                                                                                    
                                                                                
                                                           
                                               
                                                                               
                                   
                                                                                     
                                                                
                                                                            
                       
                                                                              
                                                           
                                                            
                                                    
                            
                
                                             
                                                                              
                            
      
                                                             
                             
                                                                                    
                                                       
                                                                           
                                                                   
                                                               
                                                            

                                                                           
                                 
                                        
                                                           
                                                         
                
                                
                                        
                                                               
                                                    
                                                                                       
                                                                                           
                                                           
                                                                                      
                                                  
                                                                  
             
                                                              
                                       
                                                               
                                                          
                                                                 
                                                                      
                                                                  
                                   
                                          
                             
                           
                         
           
                                                  
                                                         
        
                                                                                      
                                                                     
                                           
                                                                             
                                                              
                                 
                             
                  
            
                                                      
                                                                             
                                                             
                                                
                                                                                  
                                      
             
                                                      
                                                                       
                                         
                                                                                
              
                  
                          
                                        
                     
      
                                                       
                                                   
                        
              
                                                                        
                                                       

                                                                            
                                                  
                                                               
                                 
                                        
                                                           
                                                         
                
                                    
                                            
                                            
                                            
                                                            
                   
                                  
                                                   
                                              
                                                                                  
                                      
                            
              
                       
                            
                                                 


end HypoellipticAleksandrov.Parabolic.Dirichlet
