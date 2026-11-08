-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Torus
public import Mathlib

/-! Fourier definition of the periodic heat semigroup on the two dimensional torus. -/

@[expose] public section

noncomputable section

open MeasureTheory
open AVenhance.Infra.Torus

local instance avInfraHeatSemigroupMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraHeatSemigroupMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraHeatSemigroupIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Heat

                             

                                                                  
                                      
                            

                                                           
                                                 
                                                   

                                                                              
                    
                                                         

                                                                 
                                                 

                                                                              
                                
                                          
                                                 
                                                                                        

                                                                
                                                                            
                            
                                                         
                                              
                                                       
                 

                                                                         
                                         

                                                         
                                                                                     
                          
         
                                                 
                                  
                                             
                                                                              
                                              
                                                   

                                                                               
                                                                            
                                       
                                                                       
                           
                                                                 
                                               
                                                                          

                                                                            
                                                                                 
                                                                   

                                                                             
                                                                      
                     
                                                       
                                                                     
                                                               
                                                               
                                                
                                            

                                                                                  
                                                                   
                                                      
                                           
                                                              
                                                                
                                            

end AVenhance.Infra.Heat
