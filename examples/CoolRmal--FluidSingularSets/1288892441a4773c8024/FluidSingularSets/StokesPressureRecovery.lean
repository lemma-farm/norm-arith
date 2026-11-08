-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalStokesEnergy
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Genuine Hilbert pressure recovery from bounded divergence lifts

The actual variational Stokes residual already factors through divergence.
A norm bound for genuine preimages makes this factor continuous. Hahn--Banach
and Riesz representation then construct an actual spatial L² pressure and its
quantitative norm estimate. Applying this theorem on a ball additionally
requires the genuine ball divergence preimage bound.
-/

@[expose] public section

open MeasureTheory Set CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

                                                                              
                                                                             
                                 
                                              
                                       
                                                    
                                        
                                                         
                               
                                                         
                                        
                                                                                  
                                                          
                                                      
                                       
                                     
                                            
                                                                  
                                                                 
                                                                  
            
        
                                                                    
                                            
                                  
                                                          
                                         
                                        
                                                      
                                       
                                     
                                                 
                                                    
                                       
                                       
                                                                       
                    
        
                     
                 
                                                 
                                                      
                        
                               
           
                                                   
                                                                              
                                                                     
                                          
                                                                            

                                                                            
                                                                            
           
                                                   
                                       
                                                    
                                        
                                                         
                               
                                                         
                               
                                                                      
                               
                                                               
                                                                        
                                                               
                                                                          
                    
         
                                               
                                     
                                                                              
                                                                 
                                   
           
                                                
        
                                              
                                                                
                   
      
                                                                       
                       
                                          
                                                                                    
               
                                       
                                                                      
                                   
          

end FluidSingularSets
