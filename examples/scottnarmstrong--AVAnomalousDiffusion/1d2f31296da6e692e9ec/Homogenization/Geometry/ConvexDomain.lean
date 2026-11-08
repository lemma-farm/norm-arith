-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.

module

public import Homogenization.Geometry.OriginCubeBoundaryPush
public import Homogenization.Geometry.Translation
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

namespace Homogenization

/-!
# Bounded Open Convex Domains

This file bridges the repository's custom bounded-domain predicate
`IsBoundedDomain` with Mathlib's bounded-set API, records the resulting finite
measure consequences for Lebesgue measure, and packages the domain class
`IsOpenBoundedConvexDomain`.

The intended analytic use is to give future Sobolev/Hodge results a stable
geometric target class that already contains the open cubes and metric balls
used downstream.
-/

                                                                     
                                                          
           
                     
                               
            
                
                     
                           
                 
                                                                                           
                       
                                                                               
             
                                                                   
                                                                   
                
                                             
                                        
                                                           
                                   
                         
                                                               
                               
                                                      
                                         
                                
                
                                                     
                            
                                                                            
                                                         

                                                                                      
                               
                               
                                               
            
                                                         
         
                                          

                                                                                          
                                 
                             

                                                       
                                                        
                                                                         
                                                               
                

                                      
                                                                  
                  
                                   
                                                                      
                                                                                     
                                                         
         
                                          

                                                  
                                                                    
                               
                                           
      
                                          
                                                       
                                                                        
                                          

                                                                            
                                                                            
                                                                    
                                     
              
                                                    
                                       
                                                      

                                                                            
def IsOpenBoundedConvexDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U

namespace IsOpenBoundedConvexDomain

                                                                             
               
      

                                                                                      
                        
        

                                                                             
                 
        

                                                                                    
                                 
                                  

                                                                 
                                        
                                                                      
                                                    

                                                        
                                        
                               
                                               

                                              
                                                    
                                                      
                     
                
                                                  
                                                             
                                                         
                                                 
                                
                
                  
                                                                   
                                                         
                                      
                                                          
                                            
            
          
                                                
                                                 
                                                
                                      
                                                                 
                                                        
                                                       

end IsOpenBoundedConvexDomain

namespace IsSobolevRegularDomain

                                                                                 
                                 
                                  

                                                                 
                                     
                                                                      
                                                    

end IsSobolevRegularDomain

                                                                                  
                                                     
                                                  
                                           
                                                                           

                                                                 
                                         
                            
                                              
                                   
                              
                
                                                                 
                                                                       
                                

                                                        
                                  
                            
                     
            
                      

                                                                           
                                                   
                                                                                   

end Homogenization
