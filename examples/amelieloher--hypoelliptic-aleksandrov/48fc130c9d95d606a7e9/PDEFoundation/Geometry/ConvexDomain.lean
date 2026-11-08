module

public import PDEFoundation.Geometry.Affine
public import PDEFoundation.Geometry.Domain
public import PDEFoundation.Geometry.EuclideanBall
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Bounded open convex domains

The shared domain class for mean-zero Poincaré and Sobolev--Poincaré
estimates. It contains explicit round balls and axis-aligned cubes.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

                                                   
                                                    
                           
           
                     
                               
            
                
                     
                           
                 
                                                                  
                              
                      
                                     
                                                   
             
                                                           
               
            
                                                              
                
                                             
                                       
                                                           
                                  
                         
                                                          
            
                                  
                                                            
                                         
                               
                
                             
                             
                               
                                                                          
                                                 

                                         
                                                
                               
                               
                                               
            
                                                 
         
                                          

                                                         

                                                                             
                                                                      
                                                                        
def IsOpenBoundedConvexDomain {d : ℕ}
    (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U

namespace IsOpenBoundedConvexDomain

                                        
                                        
               
      

                                                 
                                        
                        
        

                                        
                                        
                 
        

                                               
                                        
                      
                         

                                                        
                                        
                               
                                        

                                              
                                                    
                                                          
                     
                
                                                  
                                                             
                                                         
                                                 
                                
                              
                  
                  
                      
                                           
                                      
                          
                                      
                                                          
                                            
            
          
                                       
                  
                                                 
                                                
                             
                  
                
                                                        
                                                        
                                                       

                                                                      
                                             
                                                             
                                           
                                                       
                                               
                                      
              
                                                 
                                                                       
                                               

end IsOpenBoundedConvexDomain

                                                       
                                      
                                                       
                                                                 
                                              
                                
                                       

                                                    
                                       
                                                             
                 
               
                                      
                                                       
               
                                      
                                                       
                 
                                       
         
        
      
                              
                                                    
                   
                                   
                                    
                                 
                                   
                                       
                                         
                   
              

end PDE
