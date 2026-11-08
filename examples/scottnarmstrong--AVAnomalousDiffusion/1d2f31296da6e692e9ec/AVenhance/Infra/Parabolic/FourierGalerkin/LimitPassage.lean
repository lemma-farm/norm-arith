-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.GalerkinSequence
public import AVenhance.Infra.Parabolic.FourierGalerkin.FourierLimit
public import Mathlib
/-!
# The projected trace and the real Fourier limit

These lemmas identify the initial value of the concrete Galerkin paths with the real part of the
complex torus Fourier cutoff.  Combined with Parseval convergence, they supply the weak path
compactness theorem with the exact initial trace.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance limitPassageMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance limitPassageMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance limitPassageProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

                                                                                               
                                                                                     
                                                                                        
                           
                                                                      
                                            
                                                                                     
                                                             
                                                                                         
                    
                                                                                

                                                             
                                            
                                                                         
                                   
                         
                                
           

                                                                                
                                                                                
                                                                       
                                                                                     
                                                                  
                                                                                 
                                                     
     

                                                                                                
                                                                  
                                      
                                                       
                          
                                                                                        
                                                                  
                                                                            
                               
                                       
                                                                
                                                                              
                              
                                                            
                                             
           
                                                                             
               
                                                             
                                           
                                                                    
                     
              
                                            
                                                
                                                                                   
                                                                            
                                                                       
                                                                                 
                                                               
      
                                                           
                                                                     
                                              
                                             
                                                             
                                                 
                                                               
                 
                                                                                

                                                                        
                                                                                
                                                  
                                                             
                               
                                                           
                                  

                                                                            
                                                                             
                         
           
                                                                               
                                            
                                                                            
                                                               
                
                                                  
                                                                       
                         
                        
                                                                   
                                
                                                    
                               
                                                                     
                                                        
                                                                         
                                                                             
              
                                                                              
             
            
                                                                         
                                        
                                                     

end AVenhance.Infra.Parabolic.FourierGalerkin

end
