-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Ergodic.BasicL1
public import AVenhance.Infra.Ergodic.FourierDecay
public import AVenhance.Infra.Ergodic.LatticeDecay
public import Mathlib
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # The basic L¹ ergodic estimate -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open scoped ContDiff
open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus

noncomputable section

local instance avInfraErgodicAveragesL1MeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraErgodicAveragesL1MeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraErgodicAveragesL1IsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem AveragesL1.toUnitTorus_isOpenQuotientMap (d : ℕ) :
    IsOpenQuotientMap (Torus.toUnitTorus d) := by
  let q : ℝ → UnitAddCircle := fun x => (x : UnitAddCircle)
  have hq : IsOpenQuotientMap q := by
    change IsOpenQuotientMap (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ))
    exact QuotientAddGroup.isOpenQuotientMap_mk
  change IsOpenQuotientMap (Pi.map (fun _ : Fin d => q))
  exact IsOpenQuotientMap.piMap (fun _ => hq)

theorem periodicToTorus_continuous_of_periodic {d : ℕ} {f : Vec d → ℂ}
    (hf : Continuous f) (hper : Torus.IsZdPeriodic f) :
    Continuous (Torus.periodicToTorus f) := by
  have hquot := AveragesL1.toUnitTorus_isOpenQuotientMap d
  apply hquot.continuous_comp_iff.mp
  have hcomp : Continuous
      (Torus.fromUnitTorus (Torus.periodicToTorus f)) := by
    rw [Torus.fromUnitTorus_periodicToTorus hper]
    exact hf
  exact hcomp

                                                       
                                                                               
            
                                                        
         
                                                    

                                                               
                                                                           
                                                                               
                                                                           
                                    
                                                                    
                                                                                                 
                                                                              
                                                            
                                                            
                                                       
                                                                       
                                                                                  
                                                       
                                   
                                                        
                                                       
                                     
                                                
                                                   
                          
                             
                                                                                 
                                            
                              
                                    
                                                                                 
                                   
            
       
                    
              

                                                                      
                                                         
                                         
                              
                                
                                                         
                                            
                                  
                                
                                                                  
                                          
                                                                          
                            
                                                                   
                         
                            
                                                                 
                                                           
                                                  
                                              
                         
                       
                
     

                                                        
                                                              
                       
                                             
               
                 
             
            
             
                        
                        
             
            
                
        
                                           
                                  
                                          
                                                
                         
                                                            
        
                                            
                                                                               
                                           
                                   
                                            
                                  
                                                  
                                

                                                                       
                                                                     
     

                                                                           
                                                                             
                                                                              
                                             
                                                            
                                       
                                                                
                                          
                                                                      
                                                                         
                                                          
                                                                        
                                               
                                                              
                                              
           
                                                            
             
                                            
                                          
                                                
                                            
                                                             
                                     
                                         
                                                    
                                         
                                                      
                                                               
                       
                                                            
             
                                                          
              
                                   
                                                                     
                                 
                                                        
                                
                                      
                                                       
                                                                              
                                                      
                                           
                                 
                                                           
                                           
                                       
                       
             
                                                  
                               
                                             
                                                    
                                                
                                     
                                        
                                             
           
                        
             
                                                                          
                                                      
                                                                     
          
                                                                         
                                       
                            
                                   
                    
                                                                              
                                                                                       
            
                                                       
                                                     
                
                                                                        
                                                   
                                                                     
                                                        
                                                   
                   
                                                                 
                                                                   
                                                               
                                            
                                               
                
                                                                     
                                                       
                                                                 
              
                                                        
                                                    
                                                              
                                                                 
                                                                          
                   
            
                                                                           
                                                         
                                                
                                                              
                                              
                                                                    
                                                          
                                          
                                                               
                                                         
                                           
                                             
                                                      
                                                 
                                         
             
                          
                  
                                            
                                                                     
                           
             
                          
                  
                                            
                           
                           
                                 
                                                               
                                                 
                    
                                                                         
              
              
           
                     
                                    
                                                              
                                        
                                                      
                     
                                                      
                                   
                                                     
        
                                        
                                                                        
                                                 
                                                                 
                                                                                       
                                                                    
                                                                        
                                       
                                                               
                                                           
                                                                 
        
                                                                
                               
                             
                                     
                                                                      
                                                                               
                                
                                                                      
                                                                 
        
                                                                
                               
                             
                                     
                                                                      
                                                                               
                                
                                                                      
                                                
                                                  
        
                            
                                                                
                               
                             
                                              
                                                                             
                                                        
                                              
                                           
                                                          
                            
                             
                                                                              
                                                   
                                                                      
                                                                             
        
                                                      
                               
                             
                                                             
                                                                   
                               
                             
                            
                                         
                                              
                    
                                              
                                       
                                                      
                                             
                                                            
                                              
        
                                                                
                                                             
                               
                                                    
                                      
                                                 
                                                               
                                                 
                      
                                                       
                      
                                          
                          
                             
               
                          
                                                        
                                                  
                                                                                
                                              
                  
        
                                                     
                              
                                                              
                                                         
                                                                       
                                                            
                                                          

end

end AVenhance.Infra.Ergodic
