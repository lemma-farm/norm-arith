/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Unfolding an integral over `ℝ³` onto the torus

For an integrable `H : ℝ³ → ℝ`, summing over integer translates and integrating over the torus
recovers the integral over `ℝ³`:
`∫_{ℝ³} H = ∫_{T³} ∑_{k ∈ ℤ³} H (torusRep u + k) du`.
This is the one-slice form of the periodisation identity used in `CanonicalBridgeConvolution`.
The proof splits `ℝ³` into the unit cubes `(k, k+1]` and uses the fundamental-domain formula
`UnitAddTorus.integral_preimage`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures.Phi43

open RegularityStructures

                                               
                                                      

                                                              
                                                              

                                                                           
                                                                               

                                                                                             
                                                                               

                                                 
                                                          
               
                                                     
                        
                 
                                               
               
             
            
                 
                    
                                                                              
                                                                              
                                           
                                                                                             
                           
                                                                                             
                           

                                                                                       
                             
         
                                       
                                                          
                             
             
                              
                                                                                               

                                                                          
                                                                                         
                                          
                                                                   
                                                                              
                                         
                                                          
         
               
              
                                           
                                      
                                                                 
                      
                                    
                                           
              
                                           
                                      
                                                           
                
                                           
                                                                                      
                      
               

                                                           
                                                                          
                                                                 
           
                                                                                            
                                                                                
                                               
                                  
                                                                              
                                          
                                                              
                  
                                           
            
                     
                                 

                                                                                                       
                                                                            
                                                                       
                                                        
                                               
         
                                                                              
                                              
           
            
                    
              
                                                                                   

                                                                
                                                                    
                                                                                 
                                               
        
                                           
                                                                 
                                                                             
                
                                                               
                                               
                                                                         
         
                         
                 
             
                                 
             
            

                                                               
                                                        
                                                                                   
                                                                                        
                                                                                    
                                                                        
                                                            
                                                 
                                                                
                                                                                
                          
                                                                         
                                                                             
                            
                                                           
              
                                                                                          
                                                 
                                           
                                                                                         
                                                                               
                            
                                                                                             
                      
                                                                                    
                                                     
                                                         
                                                        
                                                    
                                                                                           
                                                     
                               
                                                             
                                                                    
           
                 
                                                                 
                                                                   
                                                                
                                                         
                                                          
                     
                                                                                       
                                         
                                    
      
                                                                                     
                       
                                                                                         
               
                                                                          
                                                   

end RegularityStructures.Phi43

end
