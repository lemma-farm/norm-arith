/-
Copyright (c) 2026 Diar Heidary. Released under the MIT license.
-/
import SparseStackV3.Op.Norm
import SparseStackV3.Op.LocalTransfer

/-!
# Concrete one-site operators

Local kernels are lifted to the actual independent signed-bucket probability
space. Composition and adjunction below are finite expectation identities.
-/

open scoped BigOperators

namespace SparseStackV3.Op.SiteLeg

open SparseFock SparseFock.SparseStackDistribution Occupation

variable {d s b n : ℕ}
noncomputable section

abbrev LocalKernel (b : ℕ) := SignedHash b → SignedHash b → ℝ

def identity : LocalKernel b := fun x y => ∑ l : Level, Kernel.kern l x y

def tensorKernel (A : Site s n → LocalKernel b) (z w : RawSample s b n) : ℝ :=
  ∏ t, A t (z t) (w t)

def tensorApply (hb : 0 < b) (A : Site s n → LocalKernel b)
    (X : Vec d s b n) : Vec d s b n :=
  fun z c => (rawSampleLaw s b n hb).expect (fun w => tensorKernel A z w * X w c)

def localComp (hb : 0 < b) (A B : LocalKernel b) : LocalKernel b :=
  fun x z => (selectorLaw b hb).expect (fun y => A x y * B y z)

                                                
                                                       

def apply (hb : 0 < b) (t : Site s n) (A : LocalKernel b)
    (X : Vec d s b n) : Vec d s b n :=
  tensorApply hb (fun u => if u = t then A else identity) X

                                                                         

                                                                           
                                                                               

theorem identity_symm (x y : SignedHash b) : identity x y = identity y x := by
  exact Finset.sum_congr rfl fun l _ => Kernel.kern_symm l x y

theorem identity_left (hb : 0 < b) (A : LocalKernel b) :
    localComp hb identity A = A := by
  funext x z
  unfold localComp identity
  simp only [Finset.sum_mul]
  rw [Kernel.expect_sum]
  exact Kernel.expect_sum_kern hb x (fun y => A y z)

                                                         
                                     
            
                                                                         
                                                                               
          
                              
         
                        
      

theorem tensor_composition_kernel (hb : 0 < b) (A B : Site s n → LocalKernel b)
    (z v : RawSample s b n) :
    (rawSampleLaw s b n hb).expect
        (fun w => tensorKernel A z w * tensorKernel B w v) =
      tensorKernel (fun t => localComp hb (A t) (B t)) z v := by
  simp only [tensorKernel, ← Finset.prod_mul_distrib]
  exact FiniteLaw.expect_independentProduct_factorizes
    (fun _ : Site s n => selectorLaw b hb) (fun t y => A t (z t) y * B t y (v t))

theorem tensor_comp (hb : 0 < b) (A B : Site s n → LocalKernel b)
    (X : Vec d s b n) :
    tensorApply hb A (tensorApply hb B X) =
      tensorApply hb (fun t => localComp hb (A t) (B t)) X := by
  funext z c
  have h : tensorApply hb A (tensorApply hb B X) z c =
      (rawSampleLaw s b n hb).expect (fun w =>
        (rawSampleLaw s b n hb).expect
          (fun v => tensorKernel A z w * (tensorKernel B w v * X v c))) := by
    unfold tensorApply
    exact FiniteLaw.expect_congr _ fun w => (FiniteLaw.expect_smul _ _ _).symm
  rw [h, Projection.expect_expect_comm]
  apply FiniteLaw.expect_congr
  intro v
  rw [← tensor_composition_kernel hb A B z v, mul_comm,
    ← FiniteLaw.expect_smul]
  exact FiniteLaw.expect_congr _ fun w => by ring

                                                        
                                                  
                                                                          
                                                 
                                                                                        
            
                    
                                                   
                                                   
                                                   

                                                                    
                       
                                                                         
              
                  
         
          
                    
            
                           

theorem tensor_adjoint (hb : 0 < b) (A : Site s n → LocalKernel b)
    (X Y : Vec d s b n) :
    ip hb (tensorApply hb A X) Y =
      ip hb X (tensorApply hb (fun t x y => A t y x) Y) := by
  simp only [ip, tensorApply, FiniteLaw.expect, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun w _ => ?_
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [tensorKernel]
  ring

                                                                     
                         
                                                                              
              
                     
         
              
                    
            
                           

                                                             
                                        
                                                                                    
            
                       
                                        
                                                 

                                                                
                                                               
                                                       
                    
      

                                                          
                          
                                                             
                       
                                                                               
                                                                      
                    
                                                                                        
                                                   

                                                             
                          
                                                             
                       
                                                       
                                               
                                                    
                                                     
                             
                 
           

                                               
                            
                                                             
                       
                                                                               
                                                                      
                    
                                                                                        
                                    
      

                                                  
                            
                                                             
                                                             
                       
                                                     
                         
                                                                      
                                             

end
end SparseStackV3.Op.SiteLeg
