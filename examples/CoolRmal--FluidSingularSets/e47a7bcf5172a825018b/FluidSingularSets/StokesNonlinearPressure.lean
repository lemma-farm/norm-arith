-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallStokesPressure
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Actual convective and viscous Stokes pressures

Spatial `L⁴` velocity data produce the true `L²` convective tensor. The already
constructed bounded mean-zero Stokes pressure operator yields its nonlinear
pressure and the pressure of the actual negative velocity gradient. The signs
correspond respectively to `-div (u ⊗ u)` and `+div Du`. Their quantitative
bounds and literal compact-test Stokes equations use only the genuine input data.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

                                                                                        
                                                             
                                          

       
                                                                    
                                                      

                                                 
                                                                                   
                                                                 
                     
          
                                                         
                                                 

                                                                                
                                                 
                                                  
                                                                     
                              
        
                                                      
                               
                  
                                               
                                              
                                                                       
                                              
                          
                                        
                     
      

                                                                          
                                        
                              
            
                                                         

                                                                           
                                                                     
                                          
                                                                              
                                                             
                                                                         
                                                                                      

                                                                                
                                                             
                                                                
                                                                                   

                                                                       
                                                                          
                                          
                                                                            
                                                   
                                                             
                                                  
                                                                                 
                                                   
                                                                  
                                                            

                                                                                
                                                                         
                                          
                                     
                                                            
                                             
                                                                                             
                                                                                   

                                                                               
                                                                             
                              
                                             
                                                                  
                                              
                                                                                 
                                                               
                                                          
                                                    
                                                                      
                                                                  
                             
                                
       
                                                                                  
                                               
                                          

                                                                                  
                                                                             
                                                                   
                                             
                                                                                 
                                                                            
                                     
                                                                  
                                           
                                                                        
                                                          
                                                                   
                                                                             
                                                                                 
           
       
                                                                                          
                                                              

                                                                          
                                               
                                                                             
                                                                            

                                                                  
                                                                                         
                                                 

                                                                                              
def stokesRawGradientMatrix (D : Vec3 → Fin 3 → Vec3) (x : Vec3) : StokesGradientMatrix :=
  WithLp.toLp 2 (fun ij ↦ D x ij.2 ij.1)

                                                                                 
                                                                                         
                                                                    
                                   

                                                                                      
theorem stokesRawGradientMatrix_memLp {U : Set Vec3} (D : Vec3 → Fin 3 → Vec3)
    (hD : MemLp D 2 (volume.restrict U)) :
    MemLp (stokesRawGradientMatrix D) 2 (volume.restrict U) := by
  apply MemLp.of_eval_piLp
  intro ij
  exact memLp_pi_iff.mp (memLp_pi_iff.mp hD ij.2) ij.1

/-- The actual raw velocity derivative array as a genuine Hilbert `L²` class. -/
def stokesRawGradientL2 {U : Set Vec3} (D : Vec3 → Fin 3 → Vec3)
    (hD : MemLp D 2 (volume.restrict U)) : StokesGradientL2 U :=
  (stokesRawGradientMatrix_memLp D hD).toLp (stokesRawGradientMatrix D)

/-- The raw derivative array controls its genuine Hilbert matrix norm. -/
theorem stokesRawGradientMatrix_norm_le (D : Vec3 → Fin 3 → Vec3) (x : Vec3) :
    ‖stokesRawGradientMatrix D x‖ ≤ 3 * ‖D x‖ := by
  have hsq : ‖stokesRawGradientMatrix D x‖ ^ 2 ≤ 9 * ‖D x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ij : Fin 3 × Fin 3, ‖D x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ij _
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm (D x ij.2) ij.1).trans
          (norm_le_pi_norm (D x) ij.2)) 2
      _ = _ := by norm_num
  apply le_of_sq_le_sq _ (by positivity)
  convert hsq using 1
  ring

/-- Quantitative genuine conversion from raw derivative data to Hilbert `L²`. -/
theorem stokesRawGradientL2_norm_le {U : Set Vec3} (D : Vec3 → Fin 3 → Vec3)
    (hD : MemLp D 2 (volume.restrict U)) :
    ‖stokesRawGradientL2 D hD‖ ≤ 3 * (eLpNorm D 2 (volume.restrict U)).toReal := by
  rw [stokesRawGradientL2, Lp.norm_toLp]
  have h : eLpNorm (stokesRawGradientMatrix D) 2 (volume.restrict U) ≤
      (3 : ℝ≥0) • eLpNorm D 2 (volume.restrict U) := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (stokesRawGradientMatrix_memLp D hD).aestronglyMeasurable
    exact ae_of_all _ (fun x ↦ by exact_mod_cast stokesRawGradientMatrix_norm_le D x)
  have ht := ENNReal.toReal_mono (by
    simp only [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_ofNat]
    exact ENNReal.mul_ne_top (by norm_num) hD.eLpNorm_ne_top) h
  simpa only [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_ofNat,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat] using ht

                                                                                          
                                                        
                                                                             
                                                    

                                                                                 
                                                               
                                                       
                                                                             
                                       
                                                                           

                                                                           
                                                        
                                                       
                                      
                                                                          
      
                                                                                         
                                                                              
                                                                                     
                    

                                                                              
                                                                            
                                               
                                                                        
                                                                              
                                                        

                                                                                    
                                                                 
                                                       
                                       
                                                                      
      
                                                                        
                                                                          
                                                                                
                    

                                                                            
                                                                 
                                                       
                                                           
                                                        
                                        

                                                                          
                                                                                     
                                                      
                                                        
                                        

                                                                                         
                                                                                
                                           
                                                                       
                                                                                       
                                        
                                               
                                                                 
                                       
                                                                           
                                                    
                                                
                                                
                                                   
                                                                              
                                           
                                                             
                                                              
                                                                            
                                                         
                      

                                                                                   
                                                               
                                                     
                                           
                                                         
                                                                                       
                                        
                                               
                                                                                               
                                       
                                                             
                                                    
                                                
                                                
                                                                  
                                                             
                                     
                                                               
                                                                                            
                      

                                                                                             
                                                                                 
                                           
                                                    
                                                                                       
                                        
                                               
                                                                    
                                       
                                                        
                                                    
                                                
                                                  
                                                    
                                                                    
                                                         
                                                 
                                                  
                                                    
                       
                           
                                             
           
                                                                             
                    
                      

                                                                                               
                                                                        
                                                     
                                           
                                                          
                                                                                       
                                        
                                               
                                                                                           
                                       
                                                              
                                                    
                                                
                                                  
                                                           
                                                                                           
                                                        
                                                                     
                                                
                                                          
                           
                                                                              
                                                                         
           
       
                   
                      

end FluidSingularSets
