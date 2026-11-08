-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.Basis
public import Mathlib

/-!
# Exhaustion limits for the symmetric torus Fourier cutoffs

The finite frequency boxes exhaust the full integer lattice.  This file records the unconditional
sum convergence needed to turn the landed torus Fourier basis expansion into cutoff convergence.
-/

@[expose] public section

namespace AVenhance.Infra.Parabolic.FourierGalerkin

open Filter Topology
open MeasureTheory
open scoped Topology

noncomputable section

local instance fourierLimitMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance fourierLimitMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance fourierLimitProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance two_le_fact : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

                                                    
                                                              

                                                                                   
                                                  
                        
                               
                  
                          
                        
                   
            
                                        

                                                                                        
                                             
                                                   
                              
         
                                                         
                                                   
            
                                              
                                                              
                                                                           
                                                                            
                                     
                                                                    
                                          
                                     
                                                                    
                                          
                                             
                                             
                                                                       
                                        

                                                                                                  
  
                                     
                                                      
                                                       
                                                                               
                 
                                                                 
                                                
                
                                                                                 
                                                      

                                                               
              
                                                                   
                           
                                
                                                    
                                                 

                                                                                      
                                                                               
                                
                                                    
                                               

                                                                                  
                                                                             
                                                          
                                                             
                                    
                                     
                                                              
                                                  
                                                           
                                                       
                                                        
                                                      
                                                       
                      
           
                                 
                                                      
                                                    
                                                                           
                                                                   
                                                       
                                                                        
        
                                                                    
                                                                   
                                                          
                                                                    
                                                          
                                                                     
                                                  
                                 
           
                              
                                       
                            
            
                      

                                                                                        
                                                                       
                                                                       
                       
                                                            
                                         
                                            
                                               
                                           

                                                                  
                                                                        
                                                                                  
                                        
                                                                             
                                          

end

end AVenhance.Infra.Parabolic.FourierGalerkin
