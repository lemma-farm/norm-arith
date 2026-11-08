-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.ProductGradientRepresentative
public import AVenhance.Statements.Roots.L2NormSq
public import Mathlib

/-!
# A pointwise scalar representative of the synchronized limit

The product-space scalar limit supplies good spatial representatives at almost every time. A
measurable full-measure set of those slices is used to keep the physical representative measurable
while retaining a defined periodic `L²` slice at every time.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance scalarRepresentativeMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance scalarRepresentativeMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance scalarRepresentativeCircleProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance scalarRepresentativeProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

                                                                                                   
  
                                                         
                                                         
                                                                
                                                         

                                                                             
                                                     
                                        
                                                                 
                               
                                                       
                            
                          
                                                          
                        
                                                           
                                                                       
                                                      
                                                       
                                                             
                           
                                                                                      
                 
                                                              
                              
                                           
                                                          
                                   
                                                   
              
                   
                               

                                                                                          
                                                    
                                                                            
                                                                         
           
                                                                             
                                     

                                                                                     
                                                                 
                                                                 
                          
                                                                     
                                         
                                                                     
                         
                                               
                                                 
                                          
                                  
                                                                                         
                                  
                                                                             
                                                        
                                                                                    
               
            
                                                                     
                                                              

                                                                                   
                                                     
                                                          
                                                                             
                        
                                                     
                               
                         
                                                                         
                                                                                
                                   
                                                                               
           
                        
              
                          
                               
                                             
                                                          
                                                              
                                                                                 
                  
                                                        
                                                
                 
                                                                 
                                                                                
                                            
                                                          
                                                     
                                                
                                      
                                                       
                                              
                                                       
                                                                             
                             
                                                                                             
                
                                                      
               
                                                   
                                                 
              
                          
                               
                                                                                   
                                             
                                                                      
                                                                                                    
          
                                                                       
                                                         
                                                    
                                       
                                       
                                               
                       
                                                  
                                              
                                                           
                       
                                                                             
                                                                                             
                
                                                      
                                                          
                                                             

                                                                         
                                                       
                                                                             
                                                                          
                               
                                                       
                                                
                                                            
                                      
                                                               
                                           
                                         
                                     
                           
                                
                                    
              
                    
                                                                           
                                     
                                                         
                                           
                                               
                                         
                                                                  
                                                                      
                                                                       
                                             
                                                                              
                                      

                                                                  
                              
                                     
                   
                                                            

                                                                                                
                                           
                                                    
                                                                             
                                                                          
                                                                             
                                         
                                               
                                                                                        
                                                                           
                                             
                                                                             
                                     
                           
                                
                                    
              
                    
                                                                           
                                       
                                                                
                                                                    

                                                                                                
                                                                                         
                                                         
                                                                             
                                                     
                                    
                                                
                                            
                              
                                                        
                                                                     
           
                        
                             
                                                                
                                                                          
                                                                                                             
        
                                
                                                            
                                  
                                                                                 
                                   
                                           
                   
                                    
                                                  
                                   
                                 
                      
                                             
                                                                    
                                                                      
                                                          
                                        
              
                                                    
             
                                                                        

                                                                                                
                 
                                                               
                                                                             
                                                     
                                                                  
                                                
                                            
                                                   
                                                                             
                          
                                                                                  
            
                                                                                          
                                                                        
                        

end AVenhance.Infra.Parabolic.FourierGalerkin

end
