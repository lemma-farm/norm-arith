/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.ModelSpace
public import RegularityStructures.Analysis.Parabolic.Basic
public import RegularityStructures.Analysis.Parabolic.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic.FinCases

/-!
# The algebraic canonical lift from abstract kernel data

This file gives the algebraic, smooth fixed-regularisation version of Hairer's canonical lift in
§8.2, equations (8.18)--(8.21), specialised to the finite Φ⁴₃ sector.  The kernel record is
deliberately abstract: its function field, convolution operator, and Taylor-coefficient
functionals are independent inputs.  No theorem here identifies the latter with the value and
gradient of the former; a later heat-kernel module must provide that identification.

Only spatial Taylor terms are needed here: every retained integrated symbol has homogeneity below
two, while the parabolic time monomial has degree two.  Thus the displayed Taylor polynomial is
the truncation with parabolic degree strictly below the target homogeneity.  The source is Hairer,
arXiv:1303.5113v4, §8.2 (8.18)--(8.21), and the Φ⁴₃ kernel choice is described in §10.5 before
Theorem 10.22.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace RegularityStructures.Phi43

open RegularityStructures

open scoped ContDiff in
/-- A smooth spatially periodic realisation of the noise. -/
structure CanonicalNoise where
  /-- The smooth noise on space-time. -/
  zeta : ParabolicSpace → ℝ
  /-- Smoothness of the fixed regularisation. -/
  smooth : ContDiff ℝ ∞ zeta
  /-- Periodicity in the three spatial directions. -/
  periodic : ∀ (n : Fin 3 → ℤ) (z : ParabolicSpace),
    zeta (z.1, fun i => z.2 i + (n i : ℝ)) = zeta z

/-- Abstract kernel data for the finite algebraic lift.

The fields are intentionally independent.  A concrete module may set `convolutionOp` to
convolution by `kernel` and `taylorConstant`/`taylorSpatial` to the value/gradient of that
convolution, but the algebraic theorems in this file assume only the supplied operations. -/
structure CanonicalKernel where
  /-- A candidate translation-invariant kernel `K`; no relation to the other fields is assumed. -/
  kernel : ParabolicSpace → ℝ
  /-- Abstract convolution data, to be identified with `K * f` by a concrete analytic module. -/
  convolutionOp : (ParabolicSpace → ℝ) → ParabolicSpace → ℝ
  /-- Abstract constant Taylor data for the convolution. -/
  taylorConstant : (ParabolicSpace → ℝ) → ParabolicSpace → ℝ
  /-- Abstract spatial first Taylor data for the convolution. -/
  taylorSpatial : (ParabolicSpace → ℝ) → Fin 3 → ParabolicSpace → ℝ

namespace CanonicalKernel

variable (K : CanonicalKernel)

                                                       

                                                                                             
                                         
                                                                                          
                     

                                                                                            
                                                     
                                 
                                               
                  
                                          
                                                             
           

       
                                                       
                                                     
                                        
                                   
                                  

end CanonicalKernel

/-- The fixed-`κ` data used by the finite canonical lift. -/
structure CanonicalData (κ : Kappa) where
  noise : CanonicalNoise
  kernel : CanonicalKernel

namespace CanonicalData

variable {κ : Kappa} (D : CanonicalData κ)

local notation "E" => ParabolicSpace

                                                          
                                                  
                                                                              

                                         
                                           

                                                                
                                                                     
             
                                                      
                                               
                    

                                                               
                                                                               
             
                                                                
                                                         
                    

                                                  
                                                            

                                                           
                                                    

                                                      
                             

                                                        
                               

                                                                  
                                             

                                                                    
                                               

                                                             
                                                        

                                                               
                                                            

                                                         
                                         

                                                           
                                           

                                                           
                                           

                                                             
                                             

                                                             
                                             

                                                               
                                               

                                                            
                                                    

                                                        

                                                                                               
                                                                                            
                                         
                      
                          
                                  
                                        
                                                      
                      
                          
                          
                              
                              
                                  
                              
                                  
                                
                                    
                                    
                                        
                                        
                                            
                                      

                                                   
                                                   

                                                    
                                                    

                                                       
                               

                                                         
                                 

                                                           
                                                   

                                                             
                                                     

                                                      
                                                      

                                                        
                                                        

                                                         
                                

                                                           
                                  

                                                           
                                  

                                                             
                                    

                                                             
                                    

                                                               
                                      

                                                            
                                         

                                                                
                                  
                      
                          
                                       
                                             
                                                     
                       
                         
                           
                               
                             
                                 
                             
                                 
                               
                                   
                                   
                                       
                                       
                                           
                                     

                                                                      
                                        
                                                

                                                                        
                                 
                                             

       
                                            
                                                    
                       

       
                                     
                                                  
                        

end CanonicalData

end RegularityStructures.Phi43

end
