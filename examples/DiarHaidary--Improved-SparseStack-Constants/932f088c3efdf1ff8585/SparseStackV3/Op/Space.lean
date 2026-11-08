/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
import SparseStackV3.Base.MatrixTail
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

/-!
# The concrete state space and the exact multiplication operator

This file realizes Section 2 of the manuscript *SparseStack Is an Optimal
Oblivious Subspace Embedding* (Version 3.0), subsection `new:local`, at the
level of the ambient Hilbert space and the exact error multiplication
operator of equation `new:operator`.

The manuscript tensors the local spaces `L²({±1} × [b])` over the sites
`(g,i) ∈ [s] × [n]` and then with `ℝ^d`.  Because the tensor product of the
local `L²` spaces *is* `L²` of all the independent hash/sign variables (this
is the first sentence of the proof of Proposition `new:cutoff`), the whole
space is realized **concretely**, with no abstract tensor products, as the
space

  `Vec d s b n = RawSample s b n → (Fin d → ℝ)`

of `ℝ^d`-valued functions on the finite sample space, equipped with the
`L²(Ω ; ℝ^d)` inner product `ip` taken against the product law
`rawSampleLaw`.  Under this identification the manuscript's operator

  `𝓜 = (1/m) ∑_{g,a} ∑_{i≠j} U_{ij} ⊗ J_{a,gi} J_{a,gj}`      (`new:operator`)

"acts on vector-valued functions by multiplication by `E`", where
`E = UᵀΠᵀΠU - I_d` is the Gram error.  `M` is therefore *defined* to be that
multiplication operator, which is the content of the displayed sentence; the
local Jacobi expansion `new:Jacobi` is not needed for the statements proved
here.

The main result is `moment_identity`, the un-truncated form of
Proposition `new:cutoff` (equation `new:moment-identity`):

  `𝔼 tr E^{2q} = ∑_{a=1}^{d} ‖𝓜^q (v_a ⊗ Ω)‖²`.

The manuscript's projected operator `M_q = Q_q 𝓜 Q_q` is omitted here: the
proof of Proposition `new:cutoff` shows `M_q^j(v_a ⊗ Ω) = 𝓜^j(v_a ⊗ Ω)` for
`0 ≤ j ≤ q`, so the two sides of `new:moment-identity` agree with the
un-truncated ones, and the un-truncated identity is exactly what the
downstream majorant argument (Lemma `new:majorant`) consumes; see
`moment_le_of_nrm2_le`.
-/

open scoped BigOperators

namespace SparseStackV3.Op

open SparseFock
open SparseFock.ParsevalFrame
open SparseFock.SparseStackModel
open SparseFock.SparseStackDistribution

variable {d s b n : ℕ}

/-! ## The concrete state space -/

/-- The concrete realization of `ℝ^d ⊗ L²(Ω)`, where `Ω` is the signed-bucket
probability space of the manuscript's subsection `new:local`: since the tensor
product of the local spaces `L²({±1} × [b])` over the sites `(g,i)` is `L²` of
all the independent hash/sign variables, a state is simply an `ℝ^d`-valued
function on the sample space. -/
abbrev Vec (d s b n : ℕ) := RawSample s b n → (Fin d → ℝ)

/-- The `L²(Ω ; ℝ^d)` inner product: the expectation, under the SparseStack
product law, of the Euclidean inner product of the two values.  This is the
manuscript's inner product `⟨·,·⟩` "extended to tensor products in the usual
way". -/
noncomputable def ip (hb : 0 < b) (F G : Vec d s b n) : ℝ :=
  (rawSampleLaw s b n hb).expect (fun z => ∑ a : Fin d, F z a * G z a)

/-- The squared `L²(Ω ; ℝ^d)` norm `‖·‖²` of the manuscript. -/
noncomputable def nrm2 (hb : 0 < b) (F : Vec d s b n) : ℝ := ip hb F F

                                                               
                                                             
                                                             
                               
                          

                                                                            
                                                               
                                             

                                                                         
                                                                  
                                                     
                                                                      
                                 

                                                                         
                                                                        
                                                                    
                 
def vac (a : Fin d) : Vec d s b n := fun _ => Pi.single a (1 : ℝ)

/-! ## Elementary properties of the inner product -/

/-- The `L²(Ω ; ℝ^d)` inner product is symmetric. -/
theorem ip_comm (hb : 0 < b) (F G : Vec d s b n) : ip hb F G = ip hb G F := by
  refine FiniteLaw.expect_congr _ ?_
  intro z
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The `L²(Ω ; ℝ^d)` inner product is additive in its first argument. -/
theorem ip_add_left (hb : 0 < b) (F G H : Vec d s b n) :
    ip hb (fun z a => F z a + G z a) H = ip hb F H + ip hb G H := by
  simp only [ip, FiniteLaw.expect]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => add_mul _ _ _

/-- The `L²(Ω ; ℝ^d)` inner product is additive in its second argument. -/
theorem ip_add_right (hb : 0 < b) (F G H : Vec d s b n) :
    ip hb F (fun z a => G z a + H z a) = ip hb F G + ip hb F H := by
  rw [ip_comm, ip_add_left, ip_comm hb G F, ip_comm hb H F]

/-- The `L²(Ω ; ℝ^d)` inner product is homogeneous in its first argument. -/
theorem ip_smul_left (hb : 0 < b) (c : ℝ) (F G : Vec d s b n) :
    ip hb (fun z a => c * F z a) G = c * ip hb F G := by
  simp only [ip, FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ =>
    Finset.sum_congr rfl fun a _ => by ring

/-- The `L²(Ω ; ℝ^d)` inner product is homogeneous in its second argument. -/
theorem ip_smul_right (hb : 0 < b) (c : ℝ) (F G : Vec d s b n) :
    ip hb F (fun z a => c * G z a) = c * ip hb F G := by
  rw [ip_comm, ip_smul_left, ip_comm hb G F]

/-- The squared `L²(Ω ; ℝ^d)` norm is nonnegative. -/
theorem nrm2_nonneg (hb : 0 < b) (F : Vec d s b n) : 0 ≤ nrm2 hb F := by
  refine FiniteLaw.expect_nonneg _ ?_
  intro z
  exact Finset.sum_nonneg fun a _ => mul_self_nonneg _

/-! ## Linearity and self-adjointness of the multiplication operator -/

                                                               
                                                                       
                 
                                                                    
                                           
                               
                                                     

                                                                  
                                                                              
                 
                                                        
                                                           
                                               

                                                                       
                                                        
                            
                                                          
                       
                                  
                                                                 

                                             
                                                                      
                                
                            

                                                             
                                                                  
                   
                                                
                                    

                                                                             
                                                                              
                                                               
                                           
                                    
         
                                           
                                                                
                                                                
                                                            
                                                                
                       
                                                                   
                                                 
                           
                                                 
                             
            

                                

                                                                            
                                                                  
                                                                       
                            
                                                                   
                                       
                                                     
                                 
                                                         
                
                                       
                                               
                                      
                                                        

                             

                                                                      
                                                                           
theorem expect_sum {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (f : β → α → ℝ) :
    ∑ i : β, μ.expect (f i) = μ.expect (fun x => ∑ i : β, f i x) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_comm

                                                                           
                                                                     
                            
                                                                         
                                        
                                      
                                                    
                                    
         
                                                                   
                                                                    
                                                 
                                                           
                                                                          
                                                               

                                                                             
                               
                                                
                                                              
                                  
                                                               
                                                               
                                   
                 
                                    
         
                                        

                                                              
                                                                       
                                                                            
                                  
                                                                         
                                                                 
                                  
                                                               
                         
                             
                                                          
                                                           
                         
                                                               

end SparseStackV3.Op
