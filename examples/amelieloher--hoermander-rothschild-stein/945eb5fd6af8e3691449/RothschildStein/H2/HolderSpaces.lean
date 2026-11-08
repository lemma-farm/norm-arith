-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]

/-- Hölder seminorm on a set, using Mathlib's least Hölder constant.
BB Definition 7.6, p. 298. An infinite value records failure of Hölder boundedness. -/
def holderSemi (δ : ℝ≥0) (A : Set X) (f : X → ℝ) : ℝ≥0∞ :=
  eHolderNorm δ (fun x : A => f x)

/-- Supremum term of the bounded Hölder norm, including the empty set. -/
def holderSup (A : Set X) (f : X → ℝ) : ℝ≥0∞ := ⨆ x : A, ENNReal.ofReal |f x|

/-- The full norm is the supremum plus the Hölder seminorm. -/
def boundedHolderNorm (δ : ℝ≥0) (A : Set X) (f : X → ℝ) : ℝ≥0∞ :=
  holderSup A f + holderSemi δ A f

                                                                             
                                                             
                             

                                                                     
                                                                        
                                                                                
                                             
                                                                   
             
                                                         
                                                                          
                                                                                      
                                                                 
                                                            

                       
                                                                  
                                                             
                                                                   
                                                             

                       
                                                        
                                                                         
                                                               
                                                                                                       
                                                                                 

                                                                      
                                                           
                                                                     
                                                                      
                                                                      
                                                                                                       
                                                     

                                                       
                                                             
                                                                               
                                                                             

end RothschildStein.H2
