-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.WeakDerivative
import CKN.Foundation.Sobolev.Cutoff.Basic
import CKN.Foundation.Sobolev.Measure.CompactMultiplier
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Product rules for compactly supported smooth multipliers

The statements here use the representative functions carried by the weak-derivative
predicate.  Compact support keeps every test-function product inside the open set, so
the resulting derivative is a global weak derivative of the zero extension.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CKN

                                                    
                                         
                                                                              
            
               
                                 
                                                                        
                                                       
                                                                  
                                              
          
                 
      

                                                   
                                             
                                  
                                         
                                           
                                            
                                                
                                                              
                                                         
                                                                     
                            
                                                            
                                                            
                                                                 
                                                                 
                                    
                                                                                
                                    
                                                                                
                                              
                                                                 
                                                             
                                 
                                                               
                                  
                                                               
                                  
                                                    
                                                          
                                              
                                                                  
                                    
                                                      
                                                       
                        
                                                      
                                                           
                             
                                                                        
                                                                  
                                                            
                                                     
                                                                  
                                                            
                                                     
                                                                  
                                                             
                                                         
               
                                                           
                                           
        
                                                           
                                                                                
                                                    
                  
                                                                       
                                            
                                                      
                  
             
                                              
                                                   
              
                                     
                                                  
                                                       
                                                                       
                                                        
                                                              
                 
                             
                                                  
             
                                      
                                                        
        
                                      
                                                               
                                              
                                                        
            
                                           
                                                          
                                                          
                  
                                                                 
                                              
                                               
                                                     
            
                                           
                                            
                                                
                                                        
                                                                      
                    
                                                              
                   
                                                        
                      
                
                                             
              
                                                                    
                                               
              
                                                        
                                                     
                                                             
              
                         
                                                                             
              
                                          
                                   
                                  
                                         
      
                                                              
          
                                                           
                        
                                                        
                                                           
                                                   
             
                                                           
                         
  

                                               
                                             
                                       
                                         
                                                             
                                     
                                                
                                                              
                                                   
                                                              
         
                                                                               
                    
                                                                

theorem HasWeakPartialDerivOn.mono {d : ℕ}
    {U V : Set (Vec d)} (hVOpen : IsOpen V) (hVU : V ⊆ U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn V i u gi :=
  h.restrict hVOpen hVU

theorem HasWeakGradientOn.mono {d : ℕ}
    {U V : Set (Vec d)} (hVOpen : IsOpen V) (hVU : V ⊆ U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn V u Du :=
  h.restrict hVOpen hVU

end CKN
