module

public import FalconerThetaGauge.RadialProjectionPolar
public import Mathlib
/-!
# Actual circle densities from positive rays

For a Lebesgue-density source, the radial pushforward has its explicit positive-ray
density including the polar Jacobian. The inverse-distance weighted source cancels
that Jacobian exactly, producing the one-sided line integral in Theorem 5.4.

The polar testing argument and bounded-Jacobian comparison follow
`FalconerPacking.RadialProjectionRay` (original source credits Yongxi Lin, Apache 2.0),
at commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/RadialProjectionRay.lean
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

       
                                                                  
      

                                                                              
                                                                                
                                                      
                                                     
                                                                              
                                              
                                          
             
                                  
                           
                   
                                     
                                                                             
                                                                          

                                                                                 
                                                                              
                                                                 

           
                                                                            
                                                            
                                          
          

                                                                                             
                                                                                     
                                                 
                                                           
                                                
                                                                            
                                            
                                                                      
                                                                         
                        
      
                                                           
                                                            
                                                                                             
                                                                                               
                                                                 
                           
             
                                                                                          
                           
             
            
                                                              
                              
                                                                                  
                                                          
          
                               
              
                                                              
                                                                   
                                                                             
                
                                            
                                                            
                                                      

                                                                                              
                                                                                  
                 
                                                     
                                                              
                   
            
                                                                       
                                                                         
                           
                                           
                                                        
                               
                                                                           
                        
                         
           
                                                        
                         
           
                                     

                                                                                    
                                                                                        
                                              

           
                                                                                      
                                                                      
                                                    
          

                                                                                 
                                                                                           
                                                                        
                                            
                                                
            
                                                     
                  
                                                                              
                                                                
            
                         
                                                                                          

                                                                                       
                                                                               
                                                                               
                                     
                                                                          
                              
                                                                        
                                                        
         
          
                                               

                                                                                 
                                                                     
                                  
                                                                           
                               

                                                                                       
                                                                                   
                                                                               
                                                                             
                                                                                       
      
                            
                                                                             
                                                
                
                                               
                 
                                                         
                      
                                                                                  
                                                                    
                                                             
                                                             
                                                              
                                         
                                                               
                                                                           

end FalconerThetaGauge
