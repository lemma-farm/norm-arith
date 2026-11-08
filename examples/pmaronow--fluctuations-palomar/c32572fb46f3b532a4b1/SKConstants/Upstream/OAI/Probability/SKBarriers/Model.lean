module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Model.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib

@[expose] public section

namespace SKConstantsOAI

section

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK
abbrev Config (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ

def spin (b : Bool) : ℝ := if b then 1 else -1

def hamiltonian {n : ℕ} (J : Disorder n) (x : Config n) : ℝ :=
  (∑ e : Edge n, J e * spin (x e.val.1) * spin (x e.val.2)) / Real.sqrt n

def partition {n : ℕ} (β : ℝ) (J : Disorder n) : ℝ :=
  ∑ x : Config n, Real.exp (β * hamiltonian J x)

def gibbs {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) : ℝ :=
  Real.exp (β * hamiltonian J x) / partition β J

                                                          
                                      
                                          

                                                                         
                                                          

                                                                     
                                                     
                                                  
                                                        

                                                                                 
                                     
                                                                              

                                                             
                           
                                                          
                                                     

                                                     
                                 
                                                                        

                                                       
                                 
                                                                          

def disorderLaw (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 1)

                          

                                                       

                                            
                                                                                      
                                           

                                          
                                                                                     
                                           

end SK
end
end
end

end SKConstantsOAI
