/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ClockLawProbability
public import Rhone.Statistics.Identifiability.ClockDecay
public import Rhone.Statistics.Identifiability.PanReconstructionODE
public import Mathlib
/-! # A normalized full panmictic event law from the three-state forward equations -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

                                                      
                                                                                      
                                   
                                                             
                           
                                                   
                                   
                            
                                                                      
                                                         
                                                        
                                                     
                                                                 
                
                                                 
               
                
                                            
                 
                                                           
                                                   
              
                                  
        
                                                                            
                                                                             
                                               
           
            
        
         
                                                                                          
                               
                                                  
                                                  
                                                                          
                                                    
                                                  
                                                  

structure PanPreModel (rate : ℝ → ℝ) where
  recomb : ℝ → ℝ
  D : ℝ → ℝ
  R : ℝ → ℝ
  U : ℝ → ℝ
  recomb_continuous : Continuous recomb
  D_continuous : Continuous D
  R_continuous : Continuous R
  U_continuous : Continuous U
  recomb_nonneg : ∀ t, 0 ≤ t → 0 ≤ recomb t
  D_positive : ∀ t, 0 ≤ t → 0 < D t
  R_nonneg : ∀ t, 0 ≤ t → 0 ≤ R t
  U_nonneg : ∀ t, 0 ≤ t → 0 ≤ U t
  initial : D 0 = 1 ∧ R 0 = 0 ∧ U 0 = 0
  equations : PanPreEquations rate recomb D R U

                                                                                     
                                                                      

                                                                          
                          
                                             
                                                 
                                         
                                     
      

                                                                                     
                                                                              
                                                                                     
                                        
                                                                   
                                                                
                                        
                                                                
                                      
                                         

end Rhone.Statistics.Identifiability
