module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaAtkinsonSaddle

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Square-root coordinates for both actual Atkinson carriers

The divisor frequency enters linearly. The normalized phase has
curvature at most minus two, and its slope is factored at the
actual positive saddle. No stationary approximation is assumed.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonRootPhase (T b y : ℝ) : ℝ :=
  (T / Real.pi) * Real.log y - y ^ 2 + 2 * b * y

                                        
                                   

                                                             
                                                                               
                                                          
                          
            
      

                                                                     
                                                  
                          
                                  

                                                                     
                                                                        
                                                                       
                                                                        
                   
       
                            
                                                                          
        

                                                                     
                                                                           
                                                                                   
                                                       
                   
            
                            
         
        
                                                  
        

                                                                   
                                                      
                     
                        
                                                      
                                                                             
                          
          

                                                               
                          
                             
                                                          
                                                                      
                                                                                 
                                                                      
                                                              
                          
            
           

                                                                          
                                                             
                                      
                                         
                                                                                 
                                                                                   
                                           
                                                                           

                                                                      
                                                             
                                     
                                         
                                                                                 
                                                                                   
                       
                                                                           

end MathCollab.Density.Stronger.Atkinson
