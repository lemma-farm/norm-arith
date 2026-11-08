-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalChartKacRice
public import SlowEquilibration.SphericalForm
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Intrinsic geometry of the genuine round chart

The actual derivative spans the actual tangent plane, so scalar chart critical
points are exactly the intrinsic spherical critical points. Ordinary pullback
Hessian determinants carry precisely the actual derivative Gram determinant.
-/

@[expose] public section

namespace SlowEquilibration.SphericalChartGeometry

open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open scoped RealInnerProductSpace Topology ENNReal

noncomputable section

variable {n : ℕ}

                                                                        
                                                                                   
                                                                  
                                                 
                                                                                                  
                                   
           
         
                               
                                                                                
                                                 
                                                                               
                                                                          

                                                                                               
                                                                                 
                                                   
                                        
                                            
                                                                                                      
                                     
                                              
                                                                                      
                                              
                
                     
                                                                                          
             
          
                            

                                                                              
                                                                                  
                                                                   
                                         
            
                                        
                                                   
                                                    
            
                                                                     
                                                      

                                                                              
                                                                             
                                                                                    
                                                                                             
                     
                                                                
                        
                                                
                                            
                                                                                                   
      

                                                                              
                                                                   
                                                                        
                                                         
                                                          
                                                                              

                                                                                 
                                          
             
                
                                      
                                 
           
                                                                                
                                   
               
                        
                             

                                                                                         
                                                                     
                                                                        
                                                                                                                       

                                                                                   
                                    
                                                                                        

                                                                                 
                                                                                
                                    
                                                                               
                                           
                                                      
                                                                                                   
                                                                           
                                

                                                                           
                                                         
                                                                                  
                                                                                
                                                       
                                                       
                                                                            
                                     
         
             
            
                                                                                             
                                          
                                                                                                      
                                                                                                   
                                   
              
                        
                                          
                   
                              
                                             
                                                                                     
                                      
                                                                           
           
            
         
                                                                                   
                                                                                        

                                                                           
                                                              
                                                                  
                                                                            
                                                               
                                                              
                                                                                     

end
end SlowEquilibration.SphericalChartGeometry
