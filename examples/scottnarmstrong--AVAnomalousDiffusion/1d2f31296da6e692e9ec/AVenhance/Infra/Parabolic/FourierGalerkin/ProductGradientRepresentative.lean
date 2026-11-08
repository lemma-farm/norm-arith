-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.ProductWeakSlices
public import AVenhance.Infra.Torus.Basic
public import AVenhance.Statements.Roots.UnitCube
public import AVenhance.Statements.Roots.TimeCube
public import Mathlib
/-!
# Euclidean representatives of the synchronized gradient limit

The product gradient determines a spatial torus `L²` section for almost every time. Pulling its
coordinate representatives back to the Euclidean cover gives periodic gradients with the cellwise `L²` bounds.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open Homogenization
open scoped Topology RealInnerProductSpace

local instance gradientRepresentativeMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance gradientRepresentativeMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance gradientRepresentativeProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

                                                                                     
                                        
                                                    
                                                  
                                          
                                                       

                                                                     
                                                          
                           
         
                                                                        

                                                            
                                                

                                                                        
                                                
                                                           
                                                                         
                                                            
                                            
                                          
                                                    
                                                                           
                                                                                       
                                                                           
                                                                  
                                        
                                                                            
                                                
                                                                          
                                                                                         
                                                           
                                                                            
                                                       
                                             
                                                                               
                                                
                                                   
                         
                     
            
       
                                                                   
                                                                                 
                                              
                                                                                         
                                                       
                                                              
              
                           
             
                                   
                                                             
                                                                  
                     
                                                                                 
                                                                                 
                                                                          
                            

                                                                               
                              
                                                
                                          
                                          
                                                               
                                             
                                                                     
                              
                                                                 
                                         
                       
                                                                
                                                                    
                                                     
                                                
                                                  
                                                  
                                         
            
                                 
                                                                                              
              
                       

                                                                                                 
                                                                    
                                   
                                                  

                                                                                
                                                                                         
                                                                         
                                                     
                                                                          
                                                      
           
                                                                             
       
                                                   
                                               
                                                         
                                                      

                                                                                                                                                     
                                                             
                                       
                                                                             
                 
                              
                                                                 
                                           
                                               
                                                                
                                          

                                                                                     
                          
                                                         
                                 
                              
                                                                                   
                                                         
                                     
         
                                                                      

                                                                                    
                
                                                         
                                             
                                                                               
                                                  
                                           
                                               
                                                               
                                                            
                                       
                                                                                        
                                                                               
                                                                               
            
                                                                               
                      
            
                 

                                                                                               
                                                                                                
                                            
                                                                       
                                        
                                       
                                                                 
                               
                                                       
                            
                          
                                                          
                            
                          
                                                            
                            
                                                         
                                            
                                           
                                                  
                                            
                                      
                                 
                                                                                         
                                                
                                                                     
                                          
                                 
                                                 
                                                                                              
                                                 
                                                                                           
                                            
                                                            
                                                
                                   
                                                                        
                                                   
           
                                 
                                                                            
                                                                                       
                                                          
           
                                             
                                               
                                                                
                                          
                                    
                                                                   
                                        
                               
                                                         
                                                                           
                                                                        
                                                             
                                                                   
                                          
                                    
                                                                   
                                        
                               
                                                         
                                                                              
                   
           
                   
                                            

end AVenhance.Infra.Parabolic.FourierGalerkin

end
