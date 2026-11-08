-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.RieszSecond
import CKN.Foundation.Euclidean.RieszSecondBadPart
import CKN.Foundation.Euclidean.HessianL2
import CKN.Foundation.Euclidean.RieszSecondL2Global
import CKN.Foundation.Euclidean.InterpolationBasic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

abbrev rieszSecondL2 := Lp ℝ 2 (volume : Measure Vec3)

private def rieszSecondSchwartzEmbedding :
    SchwartzMap Vec3 ℝ →L[ℝ] rieszSecondL2 :=
  SchwartzMap.toLpCLM ℝ ℝ 2 volume

/- The smooth input map is kept as a bounded map into the completed `L²`
   space.  Its norm bound is the global endpoint estimate. -/
structure RieszSecondL2Input (i j : Fin 3) where
  smoothMap : SchwartzMap Vec3 ℝ →L[ℝ] rieszSecondL2
  smooth_bound : ∀ φ, ‖smoothMap φ‖ ≤ ‖rieszSecondSchwartzEmbedding φ‖
  smooth_hessian : ∀ (F : Vec3 → ℝ)
    (_hF : ContDiff ℝ (⊤ : ℕ∞) F) (_hFc : HasCompactSupport F),
    ∃ hmem : MemLp (mixedSecond (pressureNewtonianPotential F) i j)
        (2 : ℝ≥0∞) volume,
      smoothMap (_hFc.toSchwartzMap _hF) = MemLp.toLp _ hmem

/- The completion extension is made with the norm-controlled extension API;
   no choice of an approximating sequence is retained in the definition. -/
def rieszSecondL2Extension {i j : Fin 3} (hL2 : RieszSecondL2Input i j) :
    rieszSecondL2 →L[ℝ] rieszSecondL2 :=
  LinearMap.mkContinuous
    (hL2.smoothMap.toLinearMap.extendOfNorm
      rieszSecondSchwartzEmbedding.toLinearMap)
    1 (by
      intro f
      exact LinearMap.norm_extendOfNorm_apply_le
        (SchwartzMap.denseRange_toLpCLM (p := (2 : ℝ≥0∞)) (by norm_num))
        1 (fun φ => by
          change ‖hL2.smoothMap φ‖ ≤ 1 *
            ‖rieszSecondSchwartzEmbedding φ‖
          simpa only [one_mul] using hL2.smooth_bound φ) f)

                                                   
                                  
                              
                                                                 
                           
                                 
                                                     
                    
       
                    
             
                                    
                                        
                                                      

                                                           
                                  
                                               
                                 
                                                                   
                          
                                              
                                                         
                                                                              
                                                   
                   
      
                                            
                                                         
                                                  
                           
                                                          
                                                                
                                  
                                                                
                                                               
                                                                    
                                                                               

                                                    
                                  
                         
                                              
                                                             
                                                   
                                                                      
                                                 
                                                        
                            
                                         
            
                
                                    
                                        
                                                       

def rieszSecondLpMeasurableRepresentative (u : rieszSecondL2) : Vec3 → ℝ :=
  (Lp.aestronglyMeasurable u).aemeasurable.mk u

                                                        
                         
                                                            
                                                              

                                                   
                         
                           
                                                   
                                                         

                                                                        
                                                                          
                                                      
def rieszSecondL2MeasurableOperator {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (u : rieszSecondL2) : Vec3 → ℝ :=
  rieszSecondLpMeasurableRepresentative (rieszSecondL2Extension hL2 u)

                                                                
                                                        
                                                            
                                                          

                                                                     
                                                        
                                                    
                                        
                                                             

                                                            
                                                          
                                                          
                                             
                                                   
      
                                                          
                                                                            
                                                           
                
                                                                     
                                                                           
                  
                            
                                                        
                                                     
                                                               
                                                       

                                                             
                                                                
                                                          
                                                     
      
                                                          
                                                                            
                                                           
                    
                                                                         
                   
                             
                                                                
                                                                        

                                                                
                                                        
                                                   
                                                  
                               
                                                                   
                                                    
                                        
                           
                                 
                                                      
                             
             

                                                              
                                                        
                                                                      
                                                 
                                  
                                                       
                                                                           
                                                           
                             
                                                     
                                                              
                                
                                                     
                                       
                                
                                                    
                                    
                                                    
                                    
                                                                
                                                              
                         
                                                                           
                                                                                
                                     
                                                                      
                                                                                
      
                                                                      
                                                                           
                       
                       
                                                             
                                                        
                                                          
                                                                  
                                    
                                                                
                
                                                   
                       
                                                                  

                                                                         
                                                 
                                                              
                                                    
                                                                        
                  
                                    
                                                                        
                                                 
                                                                              
                                                                       
        
                                         
                                                                                  
                                      
                                                                           
                                           
                                                             
                              
                                                                                 
                
                                                                                 
                       
                        
                                               
                                                                                              
                                                                                        
                                   
                        
                               
                                                              
                                      
                                             

                                                                           
                                                                      
                                                                          
                                                              
                                                 
                                                              
                                                      
                                                          
                                                           
                                              
                                                  
                                                                
                      
                                             
                                                                  
                                             
                                                    
                                       
                                                    
                                          
                                             
                                 
                               
                                                                  
                                  
                                                                   
                                  
                                                           
                            
                                                                      
                                  
                                              
                                        
                                            
                                                        
                                                            
                              
                                                             
                            
                                                     
                                                     
                                        
                                          
                                                             
                                                                 
                                

                                                                           
                                                                                 
structure RieszSecondL2CZCertificate {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) (F : Vec3 → ℝ)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume) (level : ℝ) where
  A : ℝ
  hA : 0 ≤ A
  hAeq : dyadicL1Norm F = ENNReal.ofReal A
  G : CZDecomposition F level → Vec3 → ℝ
  B : CZDecomposition F level → Vec3 → ℝ
  hdecomp : ∀ D : CZDecomposition F level, ∀ x,
      rieszSecondL2MeasurableOperator hL2
        (MemLp.toLp F hF₂) x =
      G D x + B D x
  henergy : ∀ D : CZDecomposition F level,
    ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ) ≤ 8 * level * A
  hgoodL2 : ∀ D : CZDecomposition F level,
    Integrable (fun x => G D x ^ (2 : ℕ)) volume ∧
    (∫ x, G D x ^ (2 : ℕ)) ≤
      (1 : ℝ) ^ 2 * ∫ x, (dyadicGoodPart F D.cubes x) ^ (2 : ℕ)
  hbad : ∀ D : CZDecomposition F level,
    ∃ Tbad : {Q // Q ∈ D.cubes} → Vec3 → ℝ,
      Integrable (B D) volume ∧
      (∀ᵐ x ∂(volume.restrict
          (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ),
        ENNReal.ofReal |B D x| ≤
          ∑' Q : {Q // Q ∈ D.cubes}, ENNReal.ofReal |Tbad Q x|) ∧
      (∀ Q : {Q // Q ∈ D.cubes},
        AEMeasurable (fun x => ENNReal.ofReal |Tbad Q x|)
          (volume.restrict
            (⋃ Q : {Q // Q ∈ D.cubes}, rieszSecondCubeStar Q.1)ᶜ)) ∧
        (∀ Q : {Q // Q ∈ D.cubes},
          (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
            ENNReal.ofReal |Tbad Q x|) ≤
          ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
            ∫⁻ x in dyadicCubeSet Q.1,
              ENNReal.ofReal |dyadicBadPart F Q.1 x|)

                                      
                                   
                                       

                              
                                                         
                               
         
                             
                              
      

                                          
                                                                  
           
                                              
                                                         
        

                                                         
                                                 
                                      
                                                     
           
                                                       
                                                        

                                                    
                                                 
                                      
                                             
                                                                 
           
                                                       
                        

                                               
                                                  
                                                                  
                            
                                                     
                                                 
                                                              
                                   
                                   
                                                                       
                            
      
                                                            
                            
                                                     
                                                 
                                                              
                                   
                                      
                                                                       
                              
                                         
                                      
                                                            
                          
                  
                 
                                                                
                                             
                                                            
                                                                  
                                                 
                                                                       
                                           
                                                 
                                          
                                                                      
                                                                          
                                                            
                                                                          
                          
                                                                      
                                                                     
                                               
                                                    
                                                                  
                                  
                                                               
                                                               
                                                                      
                                                                   
                              
                                                            
                                                               
                                                 
                                         
                  
             
                       
             

                                                                         
                                                                            
                                                            
                                                        
                                  
                                                
                                                      
                                                    
                                                   
                                      
                                                  
                                                             
                                                      
                                                     
                         
                                        
                                                          
                   
                                                                
                  
                                                                      
                                                                   
                                                             
                    
       
            
                                                         
                                                            

end CKN.Foundation.Euclidean
