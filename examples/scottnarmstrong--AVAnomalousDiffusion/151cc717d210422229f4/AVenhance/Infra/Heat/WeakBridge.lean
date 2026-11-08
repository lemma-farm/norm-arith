-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Torus.FourierCalculus
public import AVenhance.Infra.Heat.ClassicalDerivative
public import AVenhance.Statements.Roots.IsPeriodicH1With
public import AVenhance.Infra.Heat.Energy
public import Mathlib
@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open AVenhance.Infra.Torus
open scoped ENNReal

local instance heatWeakMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance heatWeakIsAddHaarUnitAddCircle : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance heatWeakProbabilityUnitAddCircle : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Heat

                                                                   
                                                

                                                               
                                                
                                         
                                                               
                                                             
                                                                
                                             
                                                        
           
            
                                                                            
                                                                     
                                          
                                       
                                                                
                                                                
                                                    
                                                       
                              
                                            
                                                   
                                                 
                                                                               
            
       
          
          

                                                                      
                                                             
                                                     
                                                      
                                    
                                          

                                                     
                                                                  
                                                                        
                             

                                                                  
                                                                              
                                                        
                             

                                                                        
                 
                                                                                 
                                                                    
                                         

                                                                               
                                                                         
                                             
                                           
                                                       
             
                                                                        
                                                         
                                                         
                                                    
                                               
        
        
                         
                                                            
                                                
                               
                    
                                                                   
                                                                             
                                 
                                        
                                         
                        
               
                                
                             
                    
                               

                                                           
                 
                                                     
                                         
                                                             
                                                                   
      
                               
                                                      
                                 
                                                                  
             
                                             
                                            
                                  
                                        
                                                                            

                                                                   
                                        
                                                         
                                                         
                                                           
                                                             
                                                                          
                                  
                                               
      
                                                           
                                   
                                        
                                                                       
         
                                                                            
                             
                                              
                                       
                                   
                                                                                   
                             
                           
                                           
                                                 
                                  
                                                         
                                               
                                              
                                                            
                                            

                                                                                                    
                                                                 
                                        
                                                              
                     
                                  
                                                                           
                                                
                                                
                                                
                                                                             
                                               
                                                                                   
        
                                   
                                                           
                                                               
                                                                        
              
                                                           
                                 

end AVenhance.Infra.Heat
