/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.PositiveGoodOscillatory
import QuadraticCarleson.CalderonZygmundDyadicStopping
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The actual stopping-time good contribution

The stopping construction itself proves `∫ |g|² ≤ 5 ∫ |f|`. Combining it
with the genuine all-height oscillatory L² estimate closes the good-part
level-set estimate, both for full real and for dyadic modulations.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace PositiveGoodOscillatory

open OscillatoryReduction CalderonZygmundDyadicStopping

                                                                
                                   
                                                                                   
                                            

                                                                                
                                                                
                                                  
                                                            
                                                                                    
                                                                             
                         
           
                                                        
                                                               
                                                                              
                                                             
      
                                                               
                                                                   
                                                       
                                                                                    

                                                                                       

                                                                                       
                                                                                    

                                                                         
                                                              
                                                                                   
                                                          
                                                          
                                                                             
                                                                                 
                                        
      

                                                                                    
                                                                  
                                                          
                                   
                                                                      
                                                                  
               
                                                                                 
                                        
      

                                                                                    
                
                                                                             
                                                          
                                                                                     
                                                                                 
                                        
      

                                                                            
                                                                                  
                                                                     
                                                          
                                                                                       

                                                          
                                     
                                                                          
                                                          
                                   
                                                                              
                                                                  
               
                                                                                 
                                        
      

                                                            
                                                
                                                                                     
                                                          
                                                                                             
                                                                                 
                                        
      

                                                                                
                                                                                          
                                                                             
                                                          
                                                                                               

                                                                          
                                                   
                                                              
                                     
                                                             
                                        
                                                                                            
                                                                   

end PositiveGoodOscillatory
end QuadraticCarleson
