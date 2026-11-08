/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffRelativeSource
import Mathlib.Tactic.Linarith
public import Mathlib.Order.CompletePartialOrder

/-!
# Pathwise annular bounds for the difference `DΓ × DΓ` channel

The difference of two Chen products is a sum of two terms.  When both
coordinates belong to `DΓ`, one factor is controlled pathwise by the
deterministic model estimate and the other by the pathwise difference
estimate.  The positive degree of the fine factor gives the geometric
endpoint reserve.  This is the difference analogue of the pathwise part of
Hairer [Hai14, (2.17)].
-/

@[expose] public noncomputable section

open Set
open scoped ENNReal

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  {𝒯 : RegularityStructure ι}

private theorem gammaDiffBad_left_geometry
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (N k : ℕ) (hNk : N ≤ k) (a b : gammaCell S (k + 1))
    (hnear : parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤
        20 / (2 : ℝ) ^ N) :
    parabolicNorm
        (hsParabolicCellRepresentative S (k + 1) a -
          hsParabolicCellRepresentative S (k + 1) b) ≤
        24 / (2 : ℝ) ^ N ∧
      parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) a) ≤
        4 / (2 : ℝ) ^ k := by
  have hparent := hsParabolicCellParent_radius S hbox k a
  have hparent' : parabolicNorm
      (hsParabolicCellRepresentative S (k + 1) a -
        hsParabolicCellRepresentative S k (hsParabolicCellParent S k a)) ≤
      4 / (2 : ℝ) ^ k := by
    rw [parabolicNorm_sub_comm]
    exact hparent
  constructor
  · calc
      _ = parabolicNorm
          ((hsParabolicCellRepresentative S (k + 1) a -
              hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k a)) +
            (hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k a) -
              hsParabolicCellRepresentative S (k + 1) b)) := by
            congr 1
            abel
      _ ≤ 4 / (2 : ℝ) ^ k + 20 / (2 : ℝ) ^ N :=
        (parabolicNorm_add_le _ _).trans (add_le_add hparent' hnear)
      _ ≤ 24 / (2 : ℝ) ^ N := by
        have hscale : 4 / (2 : ℝ) ^ k ≤ 4 / (2 : ℝ) ^ N := by
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (pow_le_pow_right₀ (by norm_num) hNk)
        calc
          4 / (2 : ℝ) ^ k + 20 / (2 : ℝ) ^ N ≤
              4 / (2 : ℝ) ^ N + 20 / (2 : ℝ) ^ N :=
            by simpa [add_comm] using
              (add_le_add_right hscale (20 / (2 : ℝ) ^ N))
          _ = 24 / (2 : ℝ) ^ N := by ring_nf
  · exact hparent

                                           
                            
                                          
                                 
                                                       
                          
                                                                          
                                                      
                           
                 
                                                                          
                                                                            
                          
                   
                                                                          
                                                      
                             
                                                         
                               
                                                  
                                                                          
                           
                               
                 
             
        
                       
                                             
                                             
                                                        
                                                        
                                               
                                                     
                   
                
                                               
                                                                    
                                
                                                             
                                                                       
                                                 
            
                                              
                                                   
                                     
                                                         
                                            
                 

                                                     
                                               
                                                                    
                             
                                      
                                              
                                            
                                              
                                            
                                          
                                                   
                                                         
                                                   
                                
                                                         
                                
                                  
                                       
                                               
        
                         
                                                       
                                        
                                            
                                 
                                           
                                                 
                                                           
                                                       
                                                       
                                                    
                                                                  
                 
                                                       
                                                
                                              
                                            
                                          
                                                   
                                                      
                                               
                             
                                       
                                     
                                        
                                                  
                    
             
                                                        
          
                                             
                                             
                                       
                               
                                      
                                        
                                              
                                 
                                           
                                         
                                              
                                   
              
                                                       
               
                                                                        
                                                        
                                                        
                                                                               
                                                   
                
                                                                  
                                                                      
          
                                               
                                      
                 
                                            
                                               
                                      
                 
              
                                                               
                               
                
                                                            
                                                                
          
                                               
                                
                 
                                            
                                               
                                
                 
              
                                                               
                               
                                                                        
                     
                               

                                         
                            
                                          
                                 
                                                              
                                           
                                              
                                  
                                               
                                                                   
                                              
                                  
                                               
                                                                   
                                              
                                  
                                              
                                                
                                                                   
                                                          
                                                      
                                                        
                            
                       
                                                              
                                         
                                                              
                                    
                                                   
           
                                       
               
         
               
         
                                
                                              
                                               
                                                        
                      
                                 
                                                             
                                      
                                                   
                                     
                                                     
                                                     
                                              
                                                   
                                                              
                                                              
                                                              
        
                                               
                                                          
                                                           
                                                             
                                    
                                                            
                                                    
                                                  
                                                             
                                    
                                                          
                                                           
                                                             
                                    
                                                            
                                                    
                                                  
                                                             
                                           
                                             
                                                                
                                      
                                                     
                                   
                  
                                                                     
                                                
                                                
                                                            
                                         
                                  
                                                             
                                                        
                                                           
                                     
                                                   
                                                   
                               
                                                              
                                                
                                                   
                                                         
                                  
                                                   
                             
                                                           
                                
                    
                                                              
                                        
                                               
                                     
                                                              
                                        
                                                   
                                                     
                                                      
                     
                                                            
                                                             
                                                               
                                      
                                                              
                                                      
                                                    
                                                               
                                      
                                   
                                          
                                                               
                                                                 
                                       
                                          
                                                        
                                                      
                                                                 
                                            
                                                            
                                                             
                                                               
                                      
                                           
                                                          
                                          
                 
                 
                     
                                                            
                                                             
                                                               
                                      
                                                              
                                                      
                                                    
                                                               
                                      
                                   
                                          
                                                               
                                                                 
                                       
                                          
                                                        
                                                      
                                                                 
                                            
                                   
                   
                
                                                 
                                                          
                   
                                   
                                          
                                                               
                                                                 
                                       
                                          
                                                        
                                                      
                                                                 
                                        
                                                              
                                        
                                                   
                                                     
                                               
                    
                                   
                                          
                                                               
                                                                 
                                       
                                          
                                                        
                                                      
                                                                 
                                        
                                                              
                                        
                                                       
              
                                                                  
                                          
                                                     
                                                       
                                             
                                                                  
                                                             
                                                                
                              
            
                                                                 
                                                             
                                   
                                                                 
                                                             
                                               
                                                         
                                                                    
                                                             
                                           
                                  
                

                                          
                            
                                          
                                 
                                                              
                                           
                                              
                                  
                                               
                                                                   
                                              
                                  
                                               
                                                                   
                                              
                                  
                                              
                                                
                                                                   
                                                          
                                                      
                                                        
                            
                       
                                                               
                                         
                                                              
                                    
                                                   
           
                                        
               
         
               
         
                                
                                              
                                               
                                                        
                      
                                 
                                                              
                                      
                                                    
                                     
                                              
                                            
                                                     
                                              
                                                   
                                                              
                                                              
                                                              
        
                                               
                                                          
                                                           
                                                    
                                                    
                                    
                                                            
                                                    
                                                  
                                                             
                                    
                                                          
                                                           
                                                    
                                                    
                                    
                                                            
                                                    
                                                  
                                                             
                                           
                                             
                                                                
                                      
                                                     
                                   
                  
                                                                     
                                                
                                                
                                                            
                                         
                             
                                                    
                                                   
                                                           
                             
                                                            
                                                   
                                                   
                                  
                                                             
                                                        
                                                           
                                     
             
                                   
                                                        
                                                       
                                                                
                                      
                                                     
                                            
             
                                                                         
                                                            
                                                
                                                   
                                
                                                         
                                  
                                                   
                             
                                                           
                                
                                                
                     
                                                            
                                                             
                                                      
                                                      
                                      
                                                              
                                                      
                                                    
                                                               
                                      
                                   
                                          
                                                        
                                                      
                                                                 
                                       
                                          
                                                               
                                                        
                                                        
                                            
                                                            
                                                             
                                                      
                                                      
                                      
                                           
                                                          
                                          
                 
              
                     
                                                            
                                                             
                                                      
                                                      
                                      
                                                              
                                                      
                                                    
                                                               
                                      
                                   
                                          
                                                        
                                                      
                                                                 
                                       
                                          
                                                               
                                                        
                                                        
                                            
                                   
                   
                   
                                                 
                                                          
                     
                                                            
                                                             
                                                      
                                                      
                                      
                                                              
                                                      
                                                    
                                                               
                                      
                                                              
                                                           
                                    
              
                                       
                                            
                                                          
                                                        
                                                                   
                                         
                                            
                                                                 
                                                          
                                                          
                                                  
                                                                  
                                                             
                                                        
                                                      
                              
                     
                                                            
                                                             
                                                      
                                                      
                                      
                                                              
                                                      
                                                    
                                                               
                                      
                                                              
                                                           
                                    
              
                                       
                                            
                                                          
                                                        
                                                                   
                                         
                                            
                                                                 
                                                          
                                                          
                                                  
                                                                  
                                                             
                                                        
                                                      
                              
            
                                                                 
                                                             
                                   
                                                                 
                                                             
                                               
                         
                                                                    
                                                             
                                           
                                  
                

end RegularityStructures

end
