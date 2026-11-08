/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusIncrement
public import Phi43.BPHZ.TreeI3PsiSlab

/-!
# Pointwise bounds for the recentred kernel and the covariance

For abstract functions `K` (order `-3` with increments of order `-4`, time support `|t| ≤ 1`)
and `Q` (order `-1`, time support `|t| ≤ 2`) we bound, in terms of centred powers
`singularPow`,

* the recentred kernel `δK(z, w) = K(z - w) - K(-w)`, with and without a Hölder gain
  `s(z)^θ`;
* the covariance at a flipped argument, `|Q(w - u)| ≤ 2 B s(u - w)⁻¹`;
* the square and the cube of the covariance, the square with a loss `δ` of the exponent.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.18 and p. 167--168.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

                                              
                                             
                                                                                        
                                                           
                                           
                                                                            
                    
                          
                     
                                                                         
                      
        
                                                                             
                      
         
                                                                   
                        

                                                                                          
                                                                                               
                                                                                        
                                                         
                                                       
                                                                                         
                                                           
                                           
                                                              
                                                               
                                                            
                                                       
                                                                                                  
                   
                          
                                                     
                      
                                                             
                                                                              
                                     
                 
                                                
                 
                                

                                            
                                                              
                                                                                        
                                                            
                                                 
                                                        
                      
                                     
                                     
                                
                               
                                             
                              
                       
                                
                                            
                                    
                                                        
                    

                            
                                                 
                                                                                        
                                                     
                                                               
                    
                                                                       
                                        
                                                        
                                                     
                                                                           
                            
            
                      

end RegularityStructures

end
