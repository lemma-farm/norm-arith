-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import CKN.Foundation.Sobolev.W1p.Basic

/-!
# Representative-level `H¹`

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port is the exact `p = 2` facade over the independent CKN
representative-level `W1pFunction` API.

## Main definitions

* `MemL2On` and `GradMemL2On`: scalar and coordinatewise `L²` membership.
* `H1Function`: a concrete scalar representative with a chosen weak gradient.

## Main results

* `H1Function.restrict`: restriction to an open subset.
* The conversion lemmas preserve values and gradients definitionally.
-/

open scoped ENNReal

namespace CKN

/-- Scalar `L²` membership on a restricted domain. -/
abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MemLpOn U (2 : ℝ≥0∞) u

/-- Coordinatewise gradient `L²` membership on a restricted domain. -/
abbrev GradMemL2On {d : ℕ}
    (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  GradMemLpOn U (2 : ℝ≥0∞) Du

/-- A concrete scalar representative and a chosen coordinate weak gradient in
`L²(U)`. -/
structure H1Function {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (H1Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toFun

                                                                         
                                                             
                                 

namespace H1Function

@[ext]
theorem ext {d : ℕ} {U : Set (Vec d)} {u v : H1Function U}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) :
    u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl

                                                                         
                                                       
                                    
                                                              
                     

                                                              
                                            
                                    
                                      
               

                                                                             
                                                            
                      
          

                                                                            
def toW1pFunction {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) : W1pFunction U (2 : ℝ≥0∞) where
  toFun := u.toFun
  grad := u.grad
  memLp := u.memL2
  gradMemLp := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

       
                                                     
                        
                                      
     

       
                                                    
                        
                                    
     

       
                                                     
                                    
                              
     

end H1Function

namespace W1pFunction

/-- Regard a `W1pFunction` at `p = 2` as the corresponding `H1Function`. -/
def toH1Function {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) : H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memLp
  gradMemL2 := u.gradMemLp
  hasWeakGradient := u.hasWeakGradient

       
                                                    
                                    
                                     
     

       
                                                   
                                    
                                   
     

       
                                                    
                                                
                             
     

end W1pFunction

namespace H1Function

       
                                                            
                        
                                          
                              

                                                  
def restrict {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    H1Function V :=
  (u.toW1pFunction.restrict hVOpen hVU).toH1Function

       
                                                  
                                                          
                                              
     

       
                                                 
                                                          
                                            
     

       
                                                  
                                                        
                 
                                    
     

end H1Function

namespace W1pFunction

       
                                                            
                                    
                                          
                               

end W1pFunction

end CKN
