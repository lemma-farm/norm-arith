-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.DegreeOneSymbol
import CKN.Foundation.Heat.Basic

/-!
# The spatial Fourier multiplier applied to the heat kernel

External Input `ext:heat-kernel` of `paper/ckn.tex` records the size, gradient
and time-derivative bounds of `ς(D)W₊`, where `W₊(t,x) = 1_{t>0}(4πt)^{-3/2}
e^{-|x|²/(4t)}` and `ς(D)` is the spatial Fourier multiplier of a symbol `ς`
smooth away from the origin and homogeneous of degree one; the display
`eq:heat-kernel-bounds` in the proof of Proposition `prop:heat-morrey-hoelder`
is the same list.

At each positive time the spatial Fourier transform of `W₊(·,t)` is
`e^{-t|ξ|²}` in the paper's normalization `ĝ(ξ) = ∫ g(y) e^{-i y·ξ} dy`, so
`ς(D)W₊(·,t)` is the inverse transform `(2π)^{-3} ∫ e^{i x·ξ} ς(ξ) e^{-t|ξ|²} dξ`.
This file records that kernel, its causal vanishing for nonpositive times, and
the fact that the defining frequency integral converges absolutely for every
symbol of the class.  The three pointwise estimates themselves are the content
of the external input and are not proved here.
-/

open scoped BigOperators
open Set MeasureTheory

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic CKN.Foundation.Heat

/-- The integrand of the frequency integral for `ς(D)W₊` at the space-time
point `(x,t)`: the phase `e^{i x·ξ}`, the symbol `ς(ξ)`, and the Gaussian
`e^{-t|ξ|²}` that is the spatial Fourier transform of `W₊(·,t)`. -/
def spatialMultiplierHeatIntegrand (σ : Vec3 → ℂ) (x : Vec3) (t : ℝ) (ξ : Vec3) : ℂ :=
  Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) * σ ξ *
    Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))

/-- The kernel `ς(D)W₊` of External Input `ext:heat-kernel`, written as the
inverse spatial Fourier integral at positive times and extended by zero to
nonpositive times, as `W₊` itself is.  The value on the time-zero hyperplane is
the causal one; a spatial multiplier is nonlocal, so no pointwise derivative
claim is made across that hyperplane. -/
def spatialMultiplierHeatKernel (σ : Vec3 → ℂ) (x : Vec3) (t : ℝ) : ℂ :=
  if 0 < t then
    (2 * Real.pi : ℂ) ^ (-3 : ℤ) * ∫ ξ : Vec3, spatialMultiplierHeatIntegrand σ x t ξ
  else 0

                                                                                    
                                                                     
                                       
                                                 
                                          
                                      
                         
           
                                                            
                                        
                                                                     
                                   
                                                   
                                 
                                                    
                                               
                       
                                                           
                                                  
                           
                                    
                                               
                                                    
                                                       
                             
                                                 
                                                 
                                                     
                                                
                                      
                                                 
                           
           
                                        
                                                     
                             
                                                        

                                                               
                                                                                           
                                                   
                                                          
                                                                      
                                                                 
              
                                                                                
                                                                          
                                        
            
                                                                                
                           
           
              
        
            
                       

                                                                       
                                                                             
                                                                   
                                                                
                                              
                                                                       
                                                                  
                                                                      
                                                   
                                                                                                 
                                                  
                                          
                                                                        
                                     
                              
                                        
                                                                          
                                          
                                                                  
                                     
                                         
                                                             
                                                                                    
                                                                            
                         
                                           
                                                    
                                                        
                       
                                                                                            
                         
        
                                                            
                                          
                                                 
                                                                              
                                                     
                              
                                                            
                                                                           
                                             
                                                                            
                    
                                                                           
                       
                                               
                                                               
                                             
                                                                
                                                                                   
              
                   
                                                                                        
                                                                               
              
                                                                                  

                                                                              
                    
                                                                               
                                                              
                                                   

end CKN.Foundation.Euclidean
