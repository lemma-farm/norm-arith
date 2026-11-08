-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.Dyadic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The consumer-facing Calderón--Zygmund decomposition certificate

The certificate records the maximal dyadic cubes and all estimates needed by
the good/bad part argument.  Its geometry is native to `Vec3`; no alternate
Euclidean carrier is introduced.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

private instance dyadicIndexCountable : Countable DyadicIndex := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat (ℤ × DyadicCorner)
  apply Countable.mk
  refine ⟨fun Q : DyadicIndex => f (Q.scale, Q.corner), ?_⟩
  intro Q R h
  cases Q
  cases R
  have hc := Prod.mk.inj (hf h)
  cases hc.1
  cases hc.2
  rfl

                                                      
          
                                              

                                                       
                                
     

                                                               
                                                                      
     

                                                                
                                                                          
                  
                                 
                
                                  
                                                
                            

                                                                
                                                        
                  
                                 
                
                                                              
                                               
             
               
          

                                                                      
                                 
                                                                             
                  
                            
                
                              
                                                                    

                                                                 
                                                                                
                                                                 
                  
                                 
                
                                                                       
            

                                                      
                                                    
                                          
                                                          
                              
              
               
                
                 
                           
              
           
                                       

                                                          
                                                    
                                          
                                              
                                                              
                                            
                                                               
                                             
             
                                     
                                                             
                                 
        
                                                
                              
                                                        
                             

def dyadicCubeSet (Q : DyadicIndex) : Set Vec3 :=
  dyadicCube Q.scale Q.corner

                                                   
                                

def dyadicAverage (F : Vec3 → ℝ) (Q : DyadicIndex) : ℝ :=
  ⨍ x in dyadicCubeSet Q, F x

def dyadicAbsAverage (F : Vec3 → ℝ) (Q : DyadicIndex) : ℝ :=
  ⨍ x in dyadicCubeSet Q, |F x|

def dyadicL1Norm (F : Vec3 → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal |F x|

def dyadicCubeMember (D : Set DyadicIndex) (x : Vec3) : Prop :=
  ∃ Q, Q ∈ D ∧ x ∈ dyadicCubeSet Q

noncomputable def dyadicGoodPart (F : Vec3 → ℝ) (D : Set DyadicIndex) : Vec3 → ℝ := by
  classical
  exact fun x => if hx : dyadicCubeMember D x then
    dyadicAverage F (Classical.choose hx)
  else F x

def dyadicBadPart (F : Vec3 → ℝ) (Q : DyadicIndex) : Vec3 → ℝ :=
  (dyadicCubeSet Q).indicator (fun x => F x - dyadicAverage F Q)

                                                                      
                               

                                                                       
                              
                                                               

                                         
                                                                          
                     
                                                    
                                             
                                       
                                         
                                                                  
                                                                    
                                                             
                                           
              
                                                                   
                            
                                       
                                                             
                                 
              
                                                               
                                 
                               
             
                                                                   
                                                                            
                                                                
                             
                                                                                  
                                                                       
                           
             
              
                                                       

                                                                        
                            
                   
                                                      
                                          
                                       
        
                                                       
                             
               
                                                   
                               
                                               
         
                             

                                              
                                                                          
                       
                      
                                                            
                                                           
                                                                
                                                                  
                                                                        
                                                        
                                                                       
                                                               
                                       
                                                           
                                 
              
                     
                                                                 
                                                       
                                                  
                                                                              
                                                                       
                     
                                           
                                                     
                                                         
                                                                             
                                  
                                            
                                          
                                                 
                               
                                              
                                                     
                                            
                                                            
                                                    
                                
                                               

                                          
                                                                          
                       
                                                                   
                                                                        
                  

                                         
                                                                          
                                                    
                                          
                                             
           
                   
                                                                    
                             
                                            
                      
                                      
                                   
                      
             
                                                       
                                           
               
                        
                                                
                                          
                           
                                                     
                                                                 
                 
             
                    
                                 
                                                           
                               
                 
                                          

                                                
                                                          
                                                                        
                                                                        
                        
                                            
                                                                     
              
                                       
                                                          
                                    
                                               
                                                                 
                                                 
                                                   
                                 
              
                                                   
                                                   
                                 
                               
                                                       
                                    
                 
                                                        
                                                   
                                                     
                                        
                                                         
                                                      
            
                                     
                                           
                                             
                                        
       
                                                    
                                                          
                                                            
                                        
       
                             
      
                                         
                                         
                                           
                                                            
                
                                                        
                                                             
                    

                                           
                                                                          
                         
                                                                     
                                               
                                                       
                                                  
                                              
                                        
                                                                      
                                      
                                                          
                                                             
                                                                         
                          
                                                            
                                                               
                                                      
                                        
                                             
                                      
                                                     
                                                                           
                                  
                                                             
                    
                                                     
                                                         
                                   
                
                                                       
                                                         
                                   
                                 
                                                                            
                      
                           
                                                          
                            
        
                           
                                                            
                                                        
                                      
            
                              
                 
                                                          
                       
                                                               
                              
                            
              
                                                    
                                                                           
      
                                                       
                               
                          
                                                                
              
                                                               
                                       
                                     
                                                                       
                        
                                    
                                                                        
                                            
                            
                                                          
                                                  
                                       

                                                                                
                    
                                                                        
            
                                          
                                                  
                                                    
         
                                      
                                                           
                          
             
                                                   

                                                                               
                             
                                                                        
                                                                               
                                   
                                                                 
                        
                                                      
                                  
                               
        
                                                                  
                                     
                                                       
                                   
                                                                 
                               

                                              
                                                                            
                 
                                                              
                            
                                                                  
                                 
                                  
             
                         
                        
                                                          
                      
             
                                                                    
               
                                                  
                                                   
                           
                                                 
                       
                                        
                            
                       
                                                                 
                        
                                                              
                 
                                                                 
                                                  
                         
                                                                
                                         
                                    
                                                   
           
                                                         
                                
                           
                                                           
                                             
                                                  
                  
                                                                                
                                             
                 
                                                                      
                                                        
                                   
                               
                                                           
                                                        
                                                  
                                                    
                                        
                 
                                                                       
                                     
                                                                 
                                                  
                                                                
                 
                       
                                                           

                                      
                                 
                                          
                                                   
                     
                                
                                
                           
                 
             
                                    
                                                              
                                                      
                                              
                                           
               
                                                                  
                       
                             
                              
                                        
                   
                      
                    
                                                                 
                
                    
                                                 
                                              
                                           
               
                  
                                        
                                                       
                           
                                                                   
                       
                             
                                      
                 
                    
                                                                 
                
                    
                                                 

                                             
                                      
                                                    
                                                               
              
                                  
                                           
                                           
                                     
       
                                     
                                           
                                             
                                        
       
                   
      
                                          
                                        
                                           
                                           
                                              
                                             
                                           
            
                                                        
                                                                      

                                                 
                                                                            
                 
                                                                           
                                                        
                                    
                                                                   
                                               
                  
                                                                                 
                        
               
                                             
                 
                                                                     
          
                                                    
                                                          
                                                 
                                  
                                                      
                                               
                            
                
                                              
                 
                                                                    
               
                                            
                                             
                              
                                          
          
                                      
                                                     
                                              

                               
                                                                            
                                        
                 
                                                          
                                                
                                                    
                                                               
                                                          
                                                 
                    
                                                        
                    
                                                  
       
                                      
                               
                                                                     
                                                                        
                                
                                                          
              
              
                          
                                                        
              
                      
             
                                    
                                                              
              
                                 
        
                            
                                                    
                                             
                                 
                                                            
                                                              
                                                   
                                                      

structure CZDecomposition (F : Vec3 → ℝ) (height : ℝ) where
  height_pos : 0 < height
  integrable : Integrable F
  cubes : Set DyadicIndex
  cubes_countable : cubes.Countable
  cubes_pairwise_disjoint : cubes.Pairwise (Function.onFun Disjoint dyadicCubeSet)
  cube_average_gt : ∀ Q ∈ cubes, height < dyadicAbsAverage F Q
  cube_average_le : ∀ Q ∈ cubes, dyadicAbsAverage F Q ≤ 8 * height
  parent_average_le : ∀ Q ∈ cubes, dyadicAbsAverage F (dyadicParent Q) ≤ height
  cube_volume_sum_le :
    (∑' Q : {Q // Q ∈ cubes}, volume (dyadicCubeSet Q.1)) ≤
      dyadicL1Norm F / ENNReal.ofReal height
  off_cubes_le_ae : ∀ᵐ x ∂volume,
    x ∉ ⋃ Q ∈ cubes, dyadicCubeSet Q → |F x| ≤ height
  good_part_bound_ae : ∀ᵐ x ∂volume,
    |dyadicGoodPart F cubes x| ≤ 8 * height
  good_part_l1_le :
    (∫⁻ x, ENNReal.ofReal |dyadicGoodPart F cubes x|) ≤ dyadicL1Norm F
  bad_part_mean_zero : ∀ Q ∈ cubes,
    ∫ x in dyadicCubeSet Q, dyadicBadPart F Q x = 0
  bad_part_l1_sum_le :
    (∑' Q : {Q // Q ∈ cubes},
      ∫⁻ x in dyadicCubeSet Q.1, ENNReal.ofReal |dyadicBadPart F Q.1 x|) ≤
        2 * dyadicL1Norm F

                                                                         
                                             
                                    
                           

                                                                       
                                                                
            
               
                                 

                                                                   
                                    
                 
                                                            
                   

                                                                   
                                    
                                                              
                      

                                                                 
                                                                         
                                                      
                           

end CKN.Foundation.Euclidean
