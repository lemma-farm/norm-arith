/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanRates
public import Mathlib
/-! # An AC/AE panmictic pre-model -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability

def IntegrablePanPreEquations (rate recomb D R U : ℝ → ℝ) : Prop :=
  ∀ᵐ t, 0 ≤ t →
    HasDerivAt D (rate t * (R t - D t) - 2 * recomb t * D t) t ∧
    HasDerivAt R (2 * recomb t * D t - (3 * rate t + recomb t) * R t +
      4 * rate t * U t) t ∧
    HasDerivAt U (recomb t * R t - 6 * rate t * U t) t

structure IntegrablePanPreModel (rate : ℝ → ℝ) where
  recomb : ℝ → ℝ
  D : ℝ → ℝ
  R : ℝ → ℝ
  U : ℝ → ℝ
  rate_integrable : LocallyIntegrableOn rate (Ici 0) volume
  recomb_integrable : LocallyIntegrableOn recomb (Ici 0) volume
  rate_nonneg : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t
  recomb_nonneg : ∀ᵐ t, 0 ≤ t → 0 ≤ recomb t
  D_ac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval D 0 T
  R_ac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval R 0 T
  U_ac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval U 0 T
  D_positive : ∀ t, 0 ≤ t → 0 < D t
  R_nonneg : ∀ t, 0 ≤ t → 0 ≤ R t
  U_nonneg : ∀ t, 0 ≤ t → 0 ≤ U t
  initial : D 0 = 1 ∧ R 0 = 0 ∧ U 0 = 0
  equations : IntegrablePanPreEquations rate recomb D R U

                                                                            

                                                                 
                                                        
                      
                                                      
                                          
                                                                                                   
                                     
                                                                                 
                                                                  
                                    
             
                    
                      
                      

                                                                                  
                                                        
                   
                                                                                              
                                                                           
                            
                                   
                                 
                                                 
                                                
                                                                                       
                          

                                                                             
                                                  
                                                    
                                    
                                      
                                                            
                                                            
                                                            
                                                              
                                                              
                                                              
                                                      
                                                          
                                                    
                                                                   
                                                                                                
                                                                  
                                                                                    
                                             
                                                          
                                               
                                                      
                                                 
                                                             
                              
                                                                                    
                
               
                   
                   
                   
                               
                                                                                       
                
               
                    
                    
                    
                                                                     
                                               
                                                                          
                                                               
                                                                          
                                    

                                                          
                                                                   
                                                                            
                                                                              
                                                                       
                                                         
                                     
                                                                                      
                                             

                                                                                       
                                                      
                                         
                                               
                                                       
                                                   
                                            

                                                                   
                                                                      
                                         
                                                  
                                                                            
                                                                               
                                                                       
                                             
                                               
                                                                                    
                                           

end Rhone.Statistics.Identifiability
