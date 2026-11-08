module
-- Reversible module-visibility port of the audited development.
public import MathCollab.Density.Reflection
public import Mathlib

-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY

open Real Complex Set
open scoped BigOperators ContDiff

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- The source polynomial has support (N,2N], distinct from the auxiliary [M,2M). -/
def detectingPolynomial (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), a n * dirichletPhase ((n : ℝ)/N) t

                                                                     
                                           

def oneSeparated (U : Finset ℝ) : Prop :=
  ∀ t ∈ U, ∀ u ∈ U, t ≠ u → 1 ≤ |t-u|

                                      
                                                   

                                                          

                                 
                                                           

                                                  
                                  

                                                                                            
structure LargeValueData (κ : ℝ) where
  T : ℝ
  N : ℕ
  V : ℝ
  a : ℕ → ℂ
  W : Finset ℝ
  t₀ : ℝ
  T_ge_two : 2 ≤ T
  N_pos : 0 < N
  V_pos : 0 < V
  scale_lower : T ^ (1/3 : ℝ) ≤ (N : ℝ)
  scale_upper : (N : ℝ) ≤ T
  height : (N : ℝ) ^ (3/4+κ) ≤ V
  coefficients : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ 1
  location : ∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T
  separated : oneSeparated W
  large : ∀ t ∈ W, V ≤ ‖detectingPolynomial N a t‖

                                                       
                                                        
                                         
      
                                                                                         
                                               
                             
                
                                                                       
                           

                                                                                            
                   
                      
                                                                           

                                                                           
                             
                                                                           

                                                                                                   
                                                 

end MathCollab.Density
