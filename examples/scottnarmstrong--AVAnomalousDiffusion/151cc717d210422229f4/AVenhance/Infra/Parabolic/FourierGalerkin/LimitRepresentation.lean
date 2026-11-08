-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.SpacetimeCompactness
public import AVenhance.Statements.Roots.L2NormSq
public import Mathlib
/-!
# Physical representatives of weak scalar paths

Pulling a torus `L²` class back to the Euclidean covering space gives a periodic representative
with the exact unit-cell `L²` norm. These bridges are the pointwise-in-time part of the
eventual `IsWeakSolutionGrad` assembly.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Topology
open Homogenization
open scoped RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance representationMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance representationMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance representationProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

                                                                 
                                            

                                                                                                                           
                                                            
                                                      

                                                                      
                                                                           
            
                                                                                    
           
                                              

                                                                      
                                                                     
                                                                                     
                                                               
                                                                                                                                 

                                                                                      
                                                      
                                                                                           
                                                                                          
                                             

                                                                        
                                                                
                                                  

                                                                
                                                              
                                                           
                                                                     

                                                                   
                                                               
                                                                  
                                                            
                                            
                                                                                           
                                                                           
                                                                                       
                                                                            
                                                                  
                                        
                                                                            
                                                
                                                                          
                                                                                         
                                                           
                                                                            
                                                                                               
                                                                               
                   
                                                                                   
                         
                                                                                       
                                                                  
                                                  
                                                     
                           
                       
              
         
                                                                                              
                                                                            
              
                                                                                   
            
               
                                                    
                                                      
                              
                                                                                    
                                                           
                                                               
                                                                             
                                                                         
                                                 
                                                                             
                                  

                                                                               
                                                                
                                                                    
                                                       
                                                                      
                                                                            
                                                                           
                                                                 
                                                               
      
                                                      
                                                
                                                 
                                                                                          
                                       
                     
                                                                     
                             
                           
                                     

                                                                                              
                                                              
                                                                                 
                                           
                                                  

                                                                             
                                                                       
                                 
                                                                                        
              
                                       
             
                                                        
                                                                     
              
                                       
             
             
       

                                                                          
                         
                                                                 
                                                                                
            
                                             
           
                                               

                                                                           
                         
                                                                     
                                                                                
            
                                             
           
                                                

                                                                                                
           
                                               
                                                           
                                                
                                            
                                                                   
                                                             
                                                             
                                                 
                                                
                                                                                                  
                           
                                                                                        
                                                                                  
              
                                               
             
                  
                                                                                      
      
                                                
                                               
                                                                    
                    
                                               
                                                                      
                                                                           
                                         
                             
                                      
                                                    
                                                                   
                                                                                
                                                               
                     
                                                 
                             
                           
                     
                                                                      

                                                                                       
        
                                                           
                                            
                                                                         
                                                                  
                                                   
                                                             
                                                            
                                                      
                                                                    
                                               
                                                
                                                                                                  
      
                                 
                                                           
                                                               
                                                        
                                 
                               
                         
                    
                                               
                                                   
                                 
                                                
                                                        
                                               
                                                          
                                                               
                        
                                                                
                                                                  
                                                  
                                                           

                                                                                                 
                                                     
                                       
                                                                  
                                                
                                            
                
                                              
                                                                 
                                              
                                             
                                                                  
                                      
                                                                      
                                                                      
            
                                                                  
          
                                                           

end AVenhance.Infra.Parabolic.FourierGalerkin

end
