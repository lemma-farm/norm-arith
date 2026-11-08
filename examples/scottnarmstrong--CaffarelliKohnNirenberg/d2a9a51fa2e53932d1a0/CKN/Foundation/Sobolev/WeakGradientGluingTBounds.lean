-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.PressureGradientGluedCell
import CKN.Core.Step4.SliceSelectedGradientInputsCentred
import CKN.Core.Step4.SliceSelectedGradientSymmetricGeometry
import CKN.Foundation.Sobolev.WeakGradientGluingTMeasurable

/-!
# Cellwise bounds for one measurable pressure gradient

The slice bounds in `paper/ckn.tex`, Section `sec:pressure`, are
transported from the derivative selected at a cell's scale to a fixed field.
Spatial a.e. uniqueness preserves the complete quantitative majorant. Time
windows are restricted only along an explicit subset inclusion.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

namespace CKN.Core.Step4

                                                                             
                                                                     
                                                     
                                                           
                                                          
                                               
                                                   
                                                           
                                                                           
                                                         
                                                                    
                                     
                                                                                     
                                                                            
                                         
                                                                      
                                                                                         
                                                  
                                                                     
                                   

                                                                              
                                                                   
                                                           
                                                       
                                                                  
                                                                             
                                                   
                                                           
                                                                           
                                                                                 
                                                        
                                                 
                                          
                                                           
                                                                           
                                               
                                                                         
                                                                   
                                                           
                                                                 
                                                    
                                                                  
              
                                                                       
                                                                   
                                                           
                                             
                                                                                              
                                                                                


                                                                      
                                                                          
                                                                                                              
                                                                  
                                                                             
                                                   
                                                           
                                                                           
                                                                                 
                                                        
                                                 
                                          
                                                           
                                                                           
                                               
                                                                         
                                                                   
                                                                           
                                                   
                                                                    
                                                                                         
                                                                                                 
         
                                                                                         
                                                       
                                                        

end CKN.Core.Step4
