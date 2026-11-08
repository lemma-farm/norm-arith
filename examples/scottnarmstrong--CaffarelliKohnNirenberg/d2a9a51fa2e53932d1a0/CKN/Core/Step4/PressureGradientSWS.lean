-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Endgame.Localization
import CKN.Core.Step4.PressureGradientMorrey
import CKN.Core.Endgame.WeakPressureSlice
import CKN.Core.Step4.SourceMorreyData
import CKN.Foundation.Harmonic.InteriorDisplays
import CKN.Statements.SuitableWeakSolutionIntegrable
import CKN.Foundation.Parabolic.BallDisplays
import CKN.Foundation.Parabolic.Morrey.Minkowski
import CKN.Pressure.DecompositionSWSBasic
import CKN.Pressure.DerivativeAdjoint
import CKN.Pressure.HarmonicPartDerivatives
import CKN.Pressure.Lin34Slices
import CKN.Pressure.HarmonicRemainderSlice
import CKN.Core.Step4.SliceSelectedGradientScaling

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

/-! The p₁ slot is supplied by the completed weak-gradient extension.  This
adapter deliberately consumes the D15 existential and never differentiates
the literal first-potential representative. -/

                                                    
                                     
                                               
                                        
                                                                         
                        
                                                     
                                      
                                                       
                                                                                  
                                  
                                                       
                                                                           
               
                                                      
                               
                                   
                                                   
                                         
                                
                                                          
                                            
                                              
                                                                         
                                                            
                                                                     
                   
                                      
                                     
                                                                   
                                                                           
                                             
                                                                             
                                                      
                                    
                                                                      
                                                              

                                                                            
                                                                           
                                                                 

                                            
                                      
                                                                    
                                                        
                                                            
                                             
                                                                       
                                                    
                                    
                                                          
                                                  
                                           
                                                                             
                                                             
                                             
                                                                             
                                                        
                                                           
                                                        
                                                            
                                           
                                                                                
                                                                  
                                                                           
                                                 
                                                              
                             
                    
                 
                                                                             
                                                                               
                                  
                                                                 
                                                 
                                             
                                                   
                                                               
                                                      
                    
                                 
                   
                                             
                                         
                                                                             
                                                         
                                         
                                                                           
                                                      
                                                      
                                                            
                                       
                                                                         
                                                        
                                         
                                                                             
                                                      
                                                            
                    

end CKN.Core.Step4
