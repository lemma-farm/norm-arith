/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.AdaptiveAverage
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedSupply

@[expose] public section

/-!
# Sequential placement with bounded earlier neighbours

A plan may have arbitrarily many auxiliary vertices. Each step requests
only its listed earlier neighbours. Coincidences between unrelated vertices
are permitted; an edge request in a loopless host ensures that its own two
endpoints are distinct. This is the geometry needed for weighted octahedron
and prism refinements, whose auxiliary set need not embed injectively.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset StructuralF3General

universe u

inductive SequentialPlan (t : ℕ) : (R : Type u) → (R → Fin t) → ℕ → Type (u + 1)
  | nil {R : Type u} {label : R → Fin t} : SequentialPlan t R label 0
  | step {R : Type u} {label : R → Fin t} {n : ℕ}
      (target : Fin t) (parents : Finset R)
      (tail : SequentialPlan t (R ⊕ Unit) (Sum.elim label (fun _ => target)) n) :
      SequentialPlan t R label (n + 1)

namespace SequentialPlan

variable {t : ℕ}

                                                    
                                                                                    
                         
                                             
                                                                                         

variable {V : Type u} [Fintype V] [DecidableEq V]
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]

                        
                                                  
                                                           
                             
                                            
                                                            
                                                      

                                                                   
                                        
                                                                             
                                                                        
                                           
                  
                  
                                             
                                                                        
                                                                       
                                                                   
                
                                            
               
                       
                                    
              
                                             
           
                
                         
                                           

def Realizes : {R : Type u} → {label : R → Fin t} → {n : ℕ} →
    SequentialPlan t R label n → (R → V) → (Fin n → V) → Prop
  | _, _, _, .nil, _, _ => True
  | _, _, _, .step target parents tail, φ, f =>
      p (f 0) = target ∧ (∀ r ∈ parents, G.Adj (φ r) (f 0)) ∧
        Realizes tail (Sum.elim φ (fun _ => f 0)) (fun i => f i.succ)

end SequentialPlan

namespace ChoiceTree

variable {V : Type u}

def Supports : {n : ℕ} → ChoiceTree V n → (Fin n → V) → Prop
  | _, .leaf, _ => True
  | _, .step choices next, f => f 0 ∈ choices ∧ Supports (next (f 0)) (fun i => f i.succ)

end ChoiceTree

namespace SequentialPlan

variable {V : Type u} [Fintype V] [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]

                                                                  
                                                                  
                                                                   
                  
              
                                  
                                                                                  
                                                          

                                                                            
                                                                       
                                                                          
                                                     
                                                                             
                                                                      
                              
                                                           
                                                                       

                        
                               
                               

end SequentialPlan

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
