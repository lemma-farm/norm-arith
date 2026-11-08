/-
# Supporting normals of smooth convex Jordan domains

At a regular point of a smooth convex boundary, the tangent line is a
supporting line.  Its two possible normal orientations are distinguished by
the sign at any one point in the open carrier.  This file formalizes that
principle for the complex normal used by the Crouzeix--Palencia double-layer
kernel.

The proof obtains an abstract supporting functional from Hahn--Banach.  Its
composition with the boundary trace has a maximum at the chosen parameter,
so the functional annihilates the nonzero tangent.  In the real plane, two
linear functionals annihilating the same nonzero tangent are proportional.
The sign at one carrier point makes the proportionality factor positive and
therefore fixes the normal sign on the full frontier.

## Main declarations

* `SmoothJordanDomain.carrier_nonempty` -- every represented domain has a
  nonempty carrier;
* `SmoothJordanDomain.closure_support_and_carrier_strict_of_support_at_mem_carrier`
  -- weak support on the closure and strict support in the open carrier;
* `SmoothJordanDomain.canonicalNormal_support_all_of_support_at` -- the
  canonical-normal sign at one carrier point and one parameter fixes the
  orientation globally;
* `SmoothJordanDomain.frontier_support_of_support_at_mem_carrier` -- the
  oriented normal sign at one carrier point propagates to the entire
  frontier;
* `SmoothJordanDomain.reverseOrientation` -- reversal of the boundary trace
  without changing the represented carrier;
* `SmoothJordanDomain.canonicalOrientation` -- a canonical choice between a
  trace and its reversal that has the supporting-normal sign.
-/
import Operator.Crouzeix.SmoothApprox
import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue

open Complex Set
open scoped Real

/-- A smooth Jordan domain represented by a regular boundary trace has a
nonempty open carrier.  Otherwise its frontier would be empty, contradicting
the nonempty range of the trace. -/
theorem SmoothJordanDomain.carrier_nonempty
    (Omega : SmoothJordanDomain) : Omega.carrier.Nonempty := by
  have hfrontier : (frontier Omega.carrier).Nonempty :=
    ⟨Omega.boundaryParam 0, by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self 0⟩
  by_contra hnot
  have hempty : Omega.carrier = ∅ := not_nonempty_iff_eq_empty.mp hnot
  rw [hempty, frontier_empty] at hfrontier
  exact hfrontier.ne_empty rfl

                                      
                             
                                       
                                        
              
                                         
                                      
                               
                             
                       
                         

                                                                            
                                                                            
                                                                        
         
       
                                                                                   
                                                                 
           
             
                                                           
                                              
                                 
                                                           
                                              
                        
                                                           
                                                 
                                  
                        
                                                              
                                    
                          
                                                
              
                                             
                                                   
                                  
                
                                                    
                                                                    
                                                         
                                             
                                                                    
              
                      
                                          
                                    
                                      
                                                   
           
                                                
                                      
                              
                                           
                                     
                                            
                                                                            
                                                                
                          
                           
                              
                  
                 
                             
                                                  
                                                     
                                  
                                                 
                           
                    
               
                                       
                                       
                                           
                            
                           
                             
                    
                                            
        
                                           
                                               
                                                      
                                        
                                            
                            
                           
                             
                    
                                            
        
                                          
                                                  
                                                      
                                        
                           
                    
                                               
           
                                   
                                         
                      
                                                                
                                                                   
                                                     
        
                                         
                       
                
            
               
                                                             
                               
               
                                             
                            
                                 
                            
                                           
               
                                             
             
              
                                        
                  
                              
                              
                         
                                 
              
                                        
                  
                                 
                         
                                 

                                                                           
                                                                            
                                                                            
                                                                  
                                                                    
                                                                 
            
             
                                                            
                                               
            
                                                           
                                                 
                          
                                                         
                                     
                                                 
                                           
                                                         
                                                               
                                  
                  
            
                                
                 
                   
                                                                         
                  
                        
                                 
                             
                                  
                             
                   
                                                                         
                              
                 
         
                
              
                                         
                                    
                                                              
                            
                 

                                                                            
                                                                           
                                                  
                                                                     
                                                                 
           
             
                                                           
                                              
                                  
                                                           
                                                  
              
       
                                                                       
                                                       

                                                                     
                                                                     
                            
                                                       
                                                           
                          
                                        
                                                    
                                                                
                              
           
        
                                                             
                                        
                   
                   
                                                  
                                                 
                           
                                                                      
                           
                             
                       
                                      
                                            
                
                                            
                           
                                  
             
                           
                       
                                                                 
                                                  
                                             
                
                          
               
                                                         
                  
                                                               
                                             
                                                          
                                                  
                                               
                                         
                 
                          
               
                                       
                                                                  
                                      
                                
                                                                 
                                       
               
                        
                          
                                
               
                                                     
                                                      
                
                          
               
                                                     
                                                      
                
                                                  
                
                             
           
                             
                                                                         

                                                             
                                  
                                                           

                                                                   
                                          
                                              
                                                  

                                                                 
                                          
                                                    
                                                        
                                                                

                                                                    
                                       
                                         

                                                              
                                  
                                                    
                                              

                                                                             
                                                                     
             
                                                         
                                                        
                                                          
                                                                          
         
      
                            

                                                               
                                  
                                                            
                                                
               

                                                    
                                  
                                                                     
         
                                                                   
                               
            
                                        
                                                     
                                 

                                                                          
                                             
                                                                     
                                  
                                             
                      
                                                                   
                                                                      
                                        
                                                                  
                  
                                                           
                                           
                                                           
                                                                           
                
                        
                   
                                                             
                                                               
                                                                              
                                                                             
                
                                                                       
                                               
                                                 
                                                            
                                         
                                                                              
                
                                                
                                
                                                                 
                   
                                                             
                                         
                                                                
                                              
                                  
          
                         
                                
