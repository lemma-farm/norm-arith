-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.Mollify.Basic

/-!
# Mollifier radii and almost-everywhere convergence

The approximate-identity sequence underlying the paper's mollification input
(`ext:mollify`) is indexed by the outer radius `sliceRadius n = 1 / (n + 1)`,
which decreases to zero as `n` grows. The normalized kernel produced by
`standardMollifier` has inner radius equal to half its outer radius, so the
ratio of the two radii is bounded by the constant `2`. Mathlib's
almost-everywhere convergence theorem for mollifications of a locally
integrable function therefore applies: for any `g`, the functions
`mollify g (sliceRadius n) _` converge to `g` almost everywhere.
-/

open MeasureTheory Filter Topology

set_option autoImplicit false

noncomputable section

namespace CKN

                                                                                     
                                          

                                                         
                    
            

                                   
                                                                
                    
                                                        

                                                              
                                                                   
                                                                 
                                                                                   
                                       
                                         
                                                                  
                                                                         
                                                        
                                                        
                                                                
                                           
                                      
                              
                                                                       
                                                                       
                                                 

end CKN

end
