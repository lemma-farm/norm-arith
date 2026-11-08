-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Harmonic.Interior
import CKN.Foundation.Parabolic.BallDisplays
import CKN.Foundation.Sobolev.Mollify.LpApproximation
import CKN.Foundation.Sobolev.Inequalities.Smooth
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Heat

private lemma basisVec_norm (i : Fin 3) : ‖CKN.basisVec i‖ = (1 : ℝ) := by
  apply le_antisymm
  · rw [Pi.norm_def]
    change (↑(Finset.univ.sup (fun b => ‖CKN.basisVec i b‖₊) : NNReal) : ℝ) ≤
      ↑(1 : NNReal)
    exact_mod_cast (Finset.sup_le fun j hj => by
      by_cases h : j = i
      · subst h
        simp only [CKN.basisVec_apply]
        simp
      · simp only [CKN.basisVec_apply]
        simp [h])
  · have hi' : ‖CKN.basisVec i i‖ ≤ ‖CKN.basisVec i‖ :=
      norm_le_pi_norm _ _
    simpa [CKN.basisVec] using hi'

private lemma eta_gradient_bound (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec3) (i : Fin 3) :
    |CKN.spatialDeriv (eta x₀ hρ) i y| ≤ cutoffGradientConstant / ρ := by
  have hg := mollifiedBallCutoff_gradient_bound x₀ hρ y
  have hi := CKN.abs_apply_le_vecEuclideanNorm
    (classicalGradient (mollifiedBallCutoff x₀ hρ) y) i
  have hle := hi.trans hg
  simpa [eta, spatialDeriv, classicalGradient, classicalGradient_apply,
    CKN.basisVec_apply] using hle

private lemma eta_second_derivative_bound (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec3) (i j : Fin 3) :
    |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) j y| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
  have hgrad_diff : DifferentiableAt ℝ
      (classicalGradient (mollifiedBallCutoff x₀ hρ)) y := by
    apply differentiableAt_pi.mpr
    intro k
    change DifferentiableAt ℝ
      (CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) k) y
    exact (CKN.contDiff_spatialDeriv_smooth
      (mollifiedBallCutoff_smooth x₀ hρ) k).differentiable (by norm_num) y
  have hh := mollifiedBallCutoff_second_derivative_bound x₀ hρ y
  have hi := ContinuousLinearMap.le_opNorm
    (fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) y)
    (CKN.basisVec j)
  have hi' : ‖(fderiv ℝ (classicalGradient
      (mollifiedBallCutoff x₀ hρ)) y) (CKN.basisVec j)‖ ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
    calc
      ‖(fderiv ℝ (classicalGradient
          (mollifiedBallCutoff x₀ hρ)) y) (CKN.basisVec j)‖ ≤
          ‖fderiv ℝ (classicalGradient
            (mollifiedBallCutoff x₀ hρ)) y‖ * ‖CKN.basisVec j‖ := hi
      _ = ‖fderiv ℝ (classicalGradient
            (mollifiedBallCutoff x₀ hρ)) y‖ := by rw [basisVec_norm, mul_one]
      _ ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := hh
  have hcoord : (fun z : Vec3 =>
      classicalGradient (mollifiedBallCutoff x₀ hρ) z i) =
      CKN.spatialDeriv (mollifiedBallCutoff x₀ hρ) i := by
    rfl
  have hcoordfd := congrArg (fun g : Vec3 → ℝ => fderiv ℝ g y) hcoord
  have hcoordapply := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec j)) hcoordfd
  have hfdapply := fderiv_apply hgrad_diff i
  have hcoord_le :
      |(fderiv ℝ (fun z : Vec3 =>
          classicalGradient (mollifiedBallCutoff x₀ hρ) z i) y)
          (CKN.basisVec j)| ≤
        ‖(fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) y)
          (CKN.basisVec j)‖ := by
    rw [hfdapply]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      Real.norm_eq_abs] using
      (norm_le_pi_norm
        ((fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) y)
          (CKN.basisVec j)) i)
  have hi'' : |CKN.spatialDeriv (CKN.spatialDeriv
      (mollifiedBallCutoff x₀ hρ) i) j y| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
    change |(fderiv ℝ (CKN.spatialDeriv
      (mollifiedBallCutoff x₀ hρ) i) y) (CKN.basisVec j)| ≤ _
    rw [← hcoordapply]
    exact hcoord_le.trans hi'
  simpa [eta] using hi''

lemma eta_spatialDeriv_bound_global (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec3) (i : Fin 3) :
    |CKN.spatialDeriv (eta x₀ hρ) i y| ≤ cutoffGradientConstant / ρ :=
  eta_gradient_bound x₀ hρ y i

lemma eta_spatialSecond_bound_global (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec3) (i j : Fin 3) :
    |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) j y| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 :=
  eta_second_derivative_bound x₀ hρ y i j

def cutoffAnnulus (x₀ : Vec3) (ρ : ℝ) : Set Vec3 :=
  euclideanBall x₀ (3 * ρ / 4) \ euclideanClosedBall x₀ (13 * ρ / 20)

                                                    
                                                             
                                       
                                              
                                            
                                              
                                                  
      
                                                                                   
                                                                        
                                                           
                                                                
                 
              
                                                                             
                          
                                                                                        
                                          
                                                                  
                                                         
                              
        
                                
                                                    
                   
                 
                                                  
                
                                   
                                                     
                                   
                                        
                                              
                   
                                                    
                  
                                                  
                                             
                                                  
                      
                                                      
                  
                                       
            

                                                 
                                                             
                                       
                                              
                          
                                                                 
                                                                  
                                                              
                                                                       
                                    

                                             
                                      
                                                 
                                          
                                                                     
                                                                            
                                                         
                                                                         
                                                                   
                                
                                                          
                                                          
       
                                                                     
                                                                                    
                                                                           
                                                  
                                      
                                                             
                                 
           
                             
                                                        
                                           
                                                                          
                                            
                                                                                
                                                        
                          
                                      
                                                            
                      
                 
                     
                        

                                       
                                      
                                               
                                           
                                                       

                                        
                                      
                                                 
                                                                
                                                       

                                       
                                                             
                   
                                       
                                                          
                                                      
                                                                       
                                                                       
                            
               
                       
                                                                            
                             
              
                                                
                                          
                                                                  
                                              
                                             
                                        
        
                                                                        
                                                   
        

                                            
                                                             
                   
                                       
                                                            
                                                                           
                                                                         
                                      
                                                        
                                                                       
                            
               
                       
                                                                            
                                                          
      
                                                              
                                               
                                 
                                            
                                    
                                                                   
                                                 
                                   
                                             
                                        
                  
                                                     
                                                 
                                            
                                        
                                      
                                                        
                                                                        
                                                                
                    
                                                        
                                                                      
                                                          
                                                        
                                                                            
                          
                                                              
                                                          
                                                                                 
                                                       
                                                  
                                 
                                                                    
                                                                                
                                                               
                                                                             
                 
                  

                                                              
                                                         

noncomputable def harmonicInteriorGradientConstant : ℝ :=
  (4 * Real.pi)⁻¹ * 900 * (3 / 4) * cutoffGradientConstant +
    (4 * Real.pi)⁻¹ * 30 * (9 / 16) * cutoffSecondDerivativeConstant

                                                       
                                                                   

                                                               
                                                                    

                                                                
                                                                  
                                                                     

                                                                              
                                                                                  
                                                       
                                                              
                        

                                                     
                                            
                                                       
                                       
                                
                                
                                                                  

                                                                          
                               

                                                    
                                         
                                       

                                                    
                                           
                                       
                                          
            

                                               
                                              
                                          
                                          
                                                  
            

                                             
                                            
                                        
                                                  
            

                                                     
                                                    
                                                
                                                  
            

                                                      
                                                     
                                                 
                                          
                                                  
            

                                              
                                      
                                       
                                                                    
                                                                        
                                                     
                                              
                                                                       
                                       
                       
                     

                                           
                                      
                                       
                                                                      
                                                              
                                      
                                                        
                                              
                                                                              
                                          
                       
                     
      

                                                  
                                                           
                                                      
                                                          
                                                            
                                                                 
                                     

                                               
                                                             
                                                       
                                                            
                                                                                 
                          
                                                           
                                                                         
                                                               
                             
                                                             
                                                                               
                      
             
                                                              
                           
                                
                                                          
                                
                                           
           
               
                                                            
                                                                   
                     

                                       
                                       
                                                         
                                                 
                                               
                       
                                                         
                                                           
                                                     
                                 
            
                                                   
                                                       
                                                
                                                  
                                                  
                                                
                                              
                                              
                                                                    
            
                                                            
            
                   
                   
                                                                    
              
                                                            
              
                                                                         
                                          
            
                                                             
                                          
            
                                                             
                                                                 
                                                                 
                                        

                                 
                                                 
                                          
                                                      
                                               
      
                                                            
                                                               
                                                                
                                                                 
                                                                     
                                                                       
                
                                                                      
                                                                           
                                                                            
                                                                          
                                                                            
                                                                              
                              
                 
                                                                            
                                                                              
                                                                              
                                                  
                              
                                                        
          
                                                    
                                                    
                                                          
                          
                                                                 
                                                        
                                                     
                                                                 

                                
                                                 
                                          
                                                   
                             

                                    
                                      
                                   
                                                
                                                          
                           
                                                          
                           
                                                          
                           
                                               
                         

                                
                                      
                                       
                                                        
                              
                                                                           
                                                      
                                                                             
                            
               
                       
                                                                            
                                                
                                              
                                                                  
                                                                           
              
                                             
                                        
                                                                            
      
                               
                             
                                                          
                                        
                                                                      
                  
                                                        
                                            
                         
          

                                             
                                      
                                       
                                                                    
                                                 
                                                                           
                                                              
                                                                             
                            
               
                       
                                                                            
                                                              
                                                          
          
                                                               
                                              
                                                                           
                                                                           
              
      
                                                  
                             
                                                        
                                              
                                                                      
                  
                                                                
                                                    
                         
          

                                             
                                      
                                       
                                                      
                   
                                                                       
                                                                          
                                                    
                                            
                                                               
                                                               
                                                                             
                            
               
                       
                                                                            
                                            
                                                                  
                                                        
          
                                                        
          
                                                                     
                                                              
                                                                       
                                                             
                                                                       
                                                               
                                              
                                                                         
                                                                         
                                                                 
                         
      
                                                                       
                                                                          
                                                    
                                            
                                                               
                                                                           
                                                                           
                                                     
                                            
                                                                               
                                                                           
                                                                            
                                                      
                                             
                                                                   
                                          
       
                                                  
                                                    
                                                
                                                                    
                    
                                                                 
                                                     
                         
          

                                                                          
                                            
       
                                                                
                                                                               
                                                  

                                                                
                                            
                                                          
                   
                                                         
              
                                
                                                                 

                                     
                                      
                                                           
            
                                                        
                                                                                
                                                 
                                                    
             
                                                                                    

                                 
                                                        
                                   
                                               
                                           
                                       
                                                         
                                               
                                                 

                     
                                         
                                
                                         
                                                      
                                   
                                    
                                              
                                    
                                                           
                               
                          
                                                 
                 
                                                                     
                                                                      
                            
                                             
                                                
                                                            
                                 
           
                       
                   
                       
                   
              
      
                                                                          
                                                                            
                                                                 
                                                
                                    
                                                           
                                             

                       
                                                   
                                   
                                       
                                                 
                                                    
                                
                                                  
                             
                                                                        
                                 
                             
                      
                                  
                                                                       
                                
                                                     
                                             
                                                                         
                                             
      
                                       
                                                            
                                                   
                                                
                                                               
              

                                 
                                             
                                                          
                                                                   
                                                               
                                      
                      
                                                                 
                                                                   
                                           
                                                                            
                   
                                       
                                                        
                                                                     
                                                   
                                             
                                                        
                                       
                                                    
                                                                 
                                                   
                                             
                                                        
                                                           
                                                                 
                                                                   
                           
                                                           
                                   
                                            
            
                       
               
                             
                                     
      
                           
                                                             
                                                     
             
              
                    
                     

end CKN.Foundation.Heat
