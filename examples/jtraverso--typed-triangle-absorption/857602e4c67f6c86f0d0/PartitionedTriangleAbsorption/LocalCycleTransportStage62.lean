/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Tactic.Ring

/-! # Integer identities for local same-part vertex transport

These identities hold at every edge coordinate over arbitrary vertex types.
They do not assert the global CN5 supply, cycle assembly or norm contract.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.LocalCycleTransportStage62

def tri {V : Type*} (e : V → V → ℤ) (a b c : V) : ℤ :=
  e a b + e a c + e b c

                                                                            
                           
                                               
                                                   
            
      

                                                                            
                                   
                                                             
                                               
                                                   
            
      

def mixed (a b c : Bool) : Prop := a ≠ b ∨ b ≠ c

instance (a b c : Bool) : Decidable (mixed a b c) := by
  unfold mixed
  infer_instance

                                        
                                     
                                            
        

                                                
                                 
                                                       
                                             
       

end PartitionedTriangleAbsorption.LocalCycleTransportStage62
