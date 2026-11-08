-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.EquationModulus
public import Mathlib

/-!
# Weak extraction in the scalar and gradient time-L² spaces

The positive-cutoff paths are continuous with values in their spatial Hilbert spaces. The scalar
energy estimate bounds the time-L² scalar sequence, and the integrated Galerkin estimate bounds
the time-L² gradient sequence. This file extracts one subsequence weakly in both spaces.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance spacetimeTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance spacetimeOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

local instance spacetimeMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance spacetimeMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance spacetimeProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Scalar `L²` paths on the open time interval. -/
abbrev ScalarTimeL2 := Lp ScalarTorusL2 2 (volume.restrict (Ioc (0 : ℝ) 1))

/-- Gradient `L²` paths on the open time interval. -/
abbrev GradientTimeL2 := Lp SpatialGradientL2 2 (volume.restrict (Ioc (0 : ℝ) 1))

local instance spacetimeTorusMeasureSeparable : IsSeparable (volume : Measure Torus) := inferInstance
local instance spacetimeScalarSecondCountable : SecondCountableTopology ScalarTorusL2 := inferInstance
local instance spacetimeGradientSecondCountable : SecondCountableTopology SpatialGradientL2 := inferInstance
local instance spacetimeTimeMeasureSeparable : IsSeparable
    (volume.restrict (Ioc (0 : ℝ) 1)) := inferInstance
local instance spacetimeScalarTimeSecondCountable : SecondCountableTopology ScalarTimeL2 := inferInstance
local instance spacetimeGradientTimeSecondCountable : SecondCountableTopology GradientTimeL2 := inferInstance
local instance spacetimeScalarTimeSeparable : TopologicalSpace.SeparableSpace ScalarTimeL2 := inferInstance
local instance spacetimeGradientTimeSeparable : TopologicalSpace.SeparableSpace GradientTimeL2 := inferInstance

                                                                                
                                                
                                                                     

                                                                                                  
                                                                            
                                 
                                                                          

                                                                                                    
                                                                              
                                     
                                                                               

                                                                        
                                             
                                                
                                                                                    

                                                                          
                                               
                                                   
                                                                                    

                                                                                                
                                       
                                                                         
                                      
                                                                              
                                                      
                                                                                         
                                                                                 
                 
                                                                                   
                                                   
           

                                                                      
                                      
                                                    
                                                       
                                                                                               
                                                                 
                                                  
                                       

                                                                                           
                                                         
                                 
                                                                                         
                                                                                                                 
                         

                                                                   
                                                                            
                                                                               
                 
                                                              
                                            

                                                                     
                                                                              
                                                                                 
                                                   
                                                              
                                                       
                                                                                               
                                                                 
                                                    
                                                
                                                                    
                           
                                          
      
                                                                    
                                                                           
                                                 
                                                        
                                                      

                                                                                          
                                                                            
                                             
      
                                                        
                                         
                                                          
                                    
                               
                             
                                              
                                         

                                                               
                                                                                        
                                                      
                                   
                             
                   
                                                                          
                                                                
                                              
                                                            
                                                                      
                                                                              
                         
                                                          
                                                                               
                                 
                                                                                          
                              
      
                                                           
                                                        
                                                           
                              

                                                                    
                                                                            
                                 
                                                                                       
                                                                      
                                                           
                                          
                                                               
                                                      
                
               

                                                                   
                                                              

                                                                       
                                                                  

                                                                                              
                                                                                          
                                                  
                                                                                      
                                                                         
                                                                                          
                                                                       
                            
                                                                 
                                                                             
                                         
                                                                        
                             
                                            
                                                                                 
                                         
                          
                                                                   
                                                                                 
                                                                     
                                                 
                                                                  
                                                                                       
           
                                                      
                                                                
                           
                    
                                         
                                               
                                                
                                                    
                                                           
           
                                           
                
                                           
                                                                          
                                         

                                                                                                   
                                                                                                
                                                                   
                                                                                    
                               
                                                                                    
                                                      
                                                                         
                                  
                                                                       
                              
                                                                         
                              
                                      
                                                            
                                                                   
                                                           
                                      
                                          
                                                                                   
                                         
                                                         
                                                            
                               
                                                                               
                                        
                                                        
                                               
                                                      
                                               
                
                                                                        
                                                                     
                                                        
                                                            
                                                                
                                                     
                                                                                       
                                                                           
                     
             
                    
           
                                          
           
                                          

end AVenhance.Infra.Parabolic.FourierGalerkin

end
