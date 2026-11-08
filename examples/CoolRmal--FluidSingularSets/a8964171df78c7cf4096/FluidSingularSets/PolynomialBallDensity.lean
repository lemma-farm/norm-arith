-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PolynomialBallEnergy
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Genuine polynomial density in the ball `L²` space

Actual coordinate polynomials separate the points of the compact closed ball.
Stone-Weierstrass gives uniform approximation there, and bounded continuous
functions are dense in the actual ball-restricted `L²` space.
-/

@[expose] public section

open CKN MvPolynomial MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal Topology BoundedContinuousFunction

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

instance unitBallVolume_isFinite : IsFiniteMeasure (volume.restrict (vec3Ball (0 : Vec3) 1)) :=
  isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne

instance unitBallVolume_weaklyRegular :
    Measure.WeaklyRegular (volume.restrict (vec3Ball (0 : Vec3) 1)) :=
  Measure.WeaklyRegular.restrict_of_measure_ne_top volume_vec3Ball_lt_top.ne

instance weightedClosedUnitBall_compactSpace : CompactSpace weightedClosedUnitBall :=
  isCompact_iff_compactSpace.mp weightedClosedUnitBall_isCompact

                                                                          
                                     
                                                           
                                               
                                                                           
                                                  
                                                 
                                                     
                                                     
                                                                   

                                                                  
                                  
                                                                       

                                                                                 
                                                      
                                                               
               
                                                      
                                           
                                                                          
                                                                            

                                                                                             
                                                                             
                          
                         
                                                                            
                                                                                          
                                                                                      
                                                                                  
                              
                
            
                      
                
         

                                                                                         
                                
                                                                      
                               
                    
                
                                                      
                                                      
                                                             
                                                                                                
                           
                                             
                                             
                                                    
                  
                                     
                     
                
                                                      
                                                             
                                                                                          
                                             
                                                    
                                                                          
                   
                                 

                                                                            
                                                                     
                                                                  
                          
                                                                        
                                                                                  
                       
                                                             
                          
                                               
                                                                      
                
                                                 
                                                        
                                                              
                                                             
                                                                               
                                              
             
                                        
                                                              
                                            
                                                           
                                  
             
              
                                  

                                                                                     
                                                                               
                                                                
                            
                                                                                         
              
                                                           
                                    
              
                                                                           
                                                 
                                                    
                                                        
                                                                              
                                                                 
                                                                      
              
                           
                                                                        
                                             
                                                           
                                                  
                  
                                                                         
                                                  
              
                 
                                                                           
                                                                    
                                                                                        
                                   
         
                             

end FluidSingularSets
