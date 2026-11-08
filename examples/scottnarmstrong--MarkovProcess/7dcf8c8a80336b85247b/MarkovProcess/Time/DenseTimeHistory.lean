/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Finite dense-time histories

This file provides measurable coordinate equivalences for histories indexed by an initial
segment of the natural numbers. It makes no probability-law, kernel, or stochastic-process claim.
-/

namespace MarkovProcess

/-- A history through natural-number time `n`, including both endpoints. -/
abbrev DenseTimeHistory (α : Type*) (n : ℕ) := Set.Iic n → α

namespace DenseTimeHistory

variable {α : Type*} [MeasurableSpace α]

/-- The value-preserving equivalence from natural numbers at most `n` to `Fin (n + 1)`. -/
def iicEquivFin (n : ℕ) : Set.Iic n ≃ Fin (n + 1) where
  toFun i := ⟨i, Nat.lt_succ_iff.mpr i.property⟩
  invFun i := ⟨i, Nat.le_of_lt_succ i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

       
                                                                                        
     

       
                                                              
                                           
     

                                                                                  
def historyEquiv (n : ℕ) : DenseTimeHistory α n ≃ᵐ α × (Fin n → α) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) ↦ α) (iicEquivFin n)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) 0)

       
                                                                   
                                                              
     

       
                                                                                     
                                                              
     

       
                                                                         
                                                             
     

       
                                                                                     
                                                                
     

                                                                          
def splitLast (n : ℕ) : (Fin (n + 1) → α) ≃ᵐ (Fin n → α) × α :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) (Fin.last n)).trans
    MeasurableEquiv.prodComm

       
                                                                          
                                                  
                                                          
                               

       
                                                        
                                               
     

       
                                                                                      
                                                          
                                                                  
                                            
              

       
                                                                      
                                                       
                                                          
                                            
              

end DenseTimeHistory

end MarkovProcess
