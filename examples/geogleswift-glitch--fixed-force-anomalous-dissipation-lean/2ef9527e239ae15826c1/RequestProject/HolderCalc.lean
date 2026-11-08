module

public import RequestProject.PulseCalc

/-!
# Real Hölder bounds

A real-valued bookkeeping device for `C^α` norms: `HolderBd α h B` says `|h| ≤ B` and
`[h]_α ≤ B`.  It is stable under sums, scalar multiples, series and affine changes of variable,
and controls `holderNorm`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace AnomDiss

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]

/-- `‖h‖_∞ ≤ B` and `[h]_α ≤ B`. -/
def HolderBd (α : ℝ) (h : Pt d → E) (B : ℝ) : Prop :=
  (∀ x, ‖h x‖ ≤ B) ∧ ∀ x y, ‖h x - h y‖ ≤ B * ‖x - y‖ ^ α

                                                                                     
                                

lemma HolderBd.mono {α : ℝ} {h : Pt d → E} {B B' : ℝ} (hh : HolderBd α h B) (hB : B ≤ B') :
    HolderBd α h B' :=
  ⟨fun x => (hh.1 x).trans hB, fun x y => (hh.2 x y).trans
    (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg (norm_nonneg _) _))⟩

lemma HolderBd.add {α : ℝ} {f g : Pt d → E} {B C : ℝ} (hf : HolderBd α f B) (hg : HolderBd α g C) :
    HolderBd α (fun x => f x + g x) (B + C) := by
  refine ⟨fun x => (norm_add_le _ _).trans (add_le_add (hf.1 x) (hg.1 x)), fun x y => ?_⟩
  calc ‖f x + g x - (f y + g y)‖ = ‖(f x - f y) + (g x - g y)‖ := by congr 1; abel
    _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
    _ ≤ B * ‖x - y‖ ^ α + C * ‖x - y‖ ^ α := add_le_add (hf.2 x y) (hg.2 x y)
    _ = (B + C) * ‖x - y‖ ^ α := by ring

                                                                                                    
                                                 
                                     
                                                                                             
                                                           
                                                             

lemma HolderBd.zero {α : ℝ} : HolderBd α (fun _ : Pt d => (0 : E)) 0 :=
  ⟨fun _ => by simp, fun _ _ => by simp⟩

                                                                                    
                                            
                                                             
           
                                            
                                                                   
                       
                                    
                                                                                                     

                                                                                            
                                     
                                                         
                      
                                                
                                                                                
                                                                            
                                                                                        
                                     
                                                                     
                                                      
            

                                            
                                                                                             
                                                 
                      
                                                           
                                                                                
                                                                        
                                      
          
                                                                 
                                                               
                                                                                      
                                                               
                                                                            
                                                      
                                             

variable [CompleteSpace E]

                                                                                             
                                                                           
                                                    
                                                   
                                                                                     
                               
                                                      
                             

end AnomDiss
