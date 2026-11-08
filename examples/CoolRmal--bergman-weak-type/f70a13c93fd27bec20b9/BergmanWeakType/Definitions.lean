/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Bergman projections and their weak type constants -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

/-- The open unit disk in the complex plane. -/
def disk : Set ℂ := Metric.ball 0 1

/-- Euclidean area divided by π. -/
def area : Measure ℂ := ENNReal.ofReal Real.pi⁻¹ • volume

/-- Probability area on the unit disk. -/
def diskArea : Measure ℂ := area.restrict disk

                                                                     
                                       
                                                                             

                                                                       
def kernel (z w : ℂ) : ℂ := (1 - z * star w)⁻¹ ^ 2

                                                       
                                                                         

                                                      
                                                    
                                                      

                                                                                             
def weightedKernel (α : ℝ) (z w : ℂ) : ℂ := (1 - z * star w) ^ (-(α + 2) : ℂ)

                                                        
                                                         
                                                 

                                                                                        
                                                                    
                                                                      

                                                                                     
                                                                                 
                                                
                                                                             

                                                                                            
                                                                       
                                  

                                                          
                                                                                

                                                                               
                                   
                                     

end BergmanWeakType
