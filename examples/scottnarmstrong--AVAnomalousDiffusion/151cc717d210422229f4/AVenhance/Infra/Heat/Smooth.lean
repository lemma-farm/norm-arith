-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Heat.Analytic
public import Mathlib

@[expose] public section

open MeasureTheory
open AVenhance.Infra.Heat
open scoped ENNReal

namespace AVenhance.Infra.Heat

                                               
                                                           
                                                                         
                              
                                                                                           
                 
                    
         
         
            

                                                     
                                                                       
                                               
                                  
                                         
                                                                      
                                                                                                           
               
             
                                                   
                                                                  
                        
             
                                                                                
                                                                       
                        
          
                       
         
                                                                    
                                                             
                     
         
                                       
      

                                                 
                                                                            
                                                               
                                                                           
                   
         
                                                                             
          
                         
         
      

end AVenhance.Infra.Heat

noncomputable section

open MeasureTheory
open AVenhance.Infra.Torus
open scoped ComplexConjugate ENNReal

local instance avInfraHeatSmoothMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraHeatSmoothMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraHeatSmoothIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Heat

                                                                        
                                  
                                                                   
                                  
                                             
                                                                            
                                            
                                                                                          
                                                                  
                                                                     
                                                  
                                 
                       
         
                                      
               
                                                   
                                           
                                         
                                                                           
                                                    
           
             
        
              
                                  
      

end AVenhance.Infra.Heat

namespace AVenhance.Infra.Heat

                                                                            
                                 
                   
                                                                                  

                                                                       
                                                                                          
                                                            
                                                                                  
                                              
                                                                
                                  
                            
                                         
           
                                                   
                                                                              
                                   
                                                                                 
                                                   
                                                                          
                                                                      
                   

end AVenhance.Infra.Heat
