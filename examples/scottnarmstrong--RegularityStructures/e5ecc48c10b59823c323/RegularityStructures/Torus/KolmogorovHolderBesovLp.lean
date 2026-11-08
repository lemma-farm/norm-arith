/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KolmogorovHolderBesovHeat
public import RegularityStructures.PDE.Semigroup
public import RegularityStructures.Torus.HeatKernelIntegrability
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Heat-kernel Hölder bounds on the torus

This file proves the (L^p)-to-(L^\infty) estimate used in the dyadic Kolmogorov
argument.  The pointwise heat-kernel majorant is the periodised Gaussian estimate in
`KolmogorovHolderBesovHeat`; the normalization is the one in Hairer [Hai14, (2.1)--(2.3)].
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

open PDE

                                                                   
                                                
                                                                 

                                                                          
                                
                                                       
                                         

                                                                                    
                                                
      
                                                 
                                    
                                                                  
                                       
            
                                  

                                                                           
                                
                                        
                                                                    
                                                           
                       
             
                                                                              
                                                     
           
                                              
                                                                           
                                   
                                                                        
                                                                                            
                                                                  
           
                                                         
                                                                          
                                                                           
                                                                
                                          
                                                                                
                                                                                
                           
                                                
                                                            
                                        
                                                              
                   
                                          
                                                     
                                             
      
                                        
                                                                
                                                     
                            
                                                           
                                                                       

                                                                     
                                
                                                    
                                                                    
                                                                      
                                                             
                               
                            
                                                     
                                        
                                               
                                                               
                                                                        
                                 
                                             
                                              
                                           
                   
            

                                                                          
                                                                
                           
                                                                      
                                                                             
                                     
                                      
                                          
                                                                   
             
                                         
           
        
                                                               
                                                                                
                                                             
                            
                                                                  
                                                
                                                    
                                                         
                                                                             
                         
                                                                                          
                                                                         
                                                               
                 
                                                            
                                                                            
                           
                                             
                           
                            
                                                                  
      
                                                                       
                                                                           
                                                              
                                         
                                                          
                                            
                                                                
                             
                              
                   
          
                                                   
                                                                  
                         
                                                   
                                                                            
                                                                                   
                                                                        
                                                                             
                   
             
                                               
                             
                              
               
                                        

                                                                                 
                                                                
                           
                                                                      
                                                                       
                                                     
                                                  
                                                                      
         

                                                   
                                                                
                        
                      
                                                            
                                                                 
                        
            
           
                                             
                                                                 
                                                                  
                       
             
                                                                                      
                       
             
                               
                            
              
                                                              
           
                                                                
                              
                                                   
                                     
                            
                                                    
        
                          
                                                           
                              
                     
                                                             
                                                  
                                                    
                    
                                              
      
                      
                                                
                                              
                                              
                         
             
                         
                   
                           
                                                              
                                                                     

end RegularityStructures

end
