-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalModel
public import SphericalAging.HamiltonianTangentHessianGaussianLaw
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

/-!
# Genuine Gaussian spatial jets of the finite mixed field

Every variable below is an actual spatial derivative of the tensor Hamiltonian
constructed in `SphericalModel`, under its actual product disorder law.
The pure-block derivative coefficient and covariance identities are imported
from the pinned proof provider, then combined using independent degree blocks.
-/

namespace SlowEquilibration.SphericalGaussianJet

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open SphericalModel
open scoped BigOperators InnerProductSpace NNReal

abbrev PureDisorder (N p : ℕ) := SphericalAging.FiniteModel.Disorder N p
abbrev PureLaw (N p : ℕ) := SphericalAging.FiniteModel.disorderLaw N p
abbrev UpperIndex (k : ℕ) := SphericalAging.HamiltonianTangentHessianGaussianLaw.UpperIndex k

/-- The actual derivative evaluated in an ordered list of directions. -/
def jet {N P : ℕ} (c : Degree P → ℝ) (n : ℕ) (x : Vector N)
    (a : Fin n → Vector N) (J : Disorder N P) : ℝ :=
  iteratedFDeriv ℝ n (field c J) x a

def pureJetCLM (N p n : ℕ) (x : Vector N) (a : Fin n → Vector N) :
    PureDisorder N p →L[ℝ] ℝ :=
  ∑ I : SphericalAging.FiniteModel.TensorIndex N p,
    SphericalAging.HamiltonianDerivativeCovariance.coefficientDerivative n I x a •
      ContinuousLinearMap.proj I

theorem pureJetCLM_apply {N p n : ℕ} (x : Vector N) (a : Fin n → Vector N)
    (J : PureDisorder N p) :
    pureJetCLM N p n x a J =
      iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p J) x a := by
  rw [SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_tensorLinear]
  simp [pureJetCLM, SphericalAging.FiniteModel.tensorLinear]

def jetCLM {N P : ℕ} (c : Degree P → ℝ) (n : ℕ) (x : Vector N)
    (a : Fin n → Vector N) : Disorder N P →L[ℝ] ℝ :=
  ∑ p : Degree P, Real.sqrt (c p) •
    (pureJetCLM N p.val.val n x a).comp (ContinuousLinearMap.proj p)

theorem jet_sum {N P : ℕ} (c : Degree P → ℝ) (n : ℕ) (x : Vector N)
    (a : Fin n → Vector N) (J : Disorder N P) :
    jet c n x a J = ∑ p : Degree P, Real.sqrt (c p) *
      iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val (J p)) x a := by
  unfold jet
  rw [field_iteratedFDeriv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rfl

@[simp] theorem jetCLM_apply {N P : ℕ} (c : Degree P → ℝ) (n : ℕ)
    (x : Vector N) (a : Fin n → Vector N) (J : Disorder N P) :
    jetCLM c n x a J = jet c n x a J := by
  simp [jetCLM, pureJetCLM_apply, jet_sum]

                                                               
                                           
                                                        
                                                                  
               

                                                      
                                           
                                              
                                        

                                                                            
                                                     
                                                      
                                                          
                                          
                                                                               
                             
                                                 
                                                                  
               

def blockJet {N P : ℕ} (p : Degree P) (n : ℕ) (x : Vector N)
    (a : Fin n → Vector N) (J : Disorder N P) : ℝ :=
  iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val (J p)) x a

theorem blockJet_memLp {N P : ℕ} (p : Degree P) (n : ℕ)
    (x : Vector N) (a : Fin n → Vector N) :
    MemLp (blockJet p n x a) 2 (disorderLaw N P) := by
  exact (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp n x a).comp_measurePreserving (measurePreserving_eval
      (fun q : Degree P => PureLaw N q.val.val) p)

                                                      
                                           
                                                      
                             
                                                                                
                                             
                                                                                    
                                                                                
                                                   
                                                                                        

                                                     
                                           
                                                 
                   
                         
                                
                                            
                                                    
                        
              
                                                                         

theorem blockJet_covariance {N P : ℕ} (p q : Degree P) (n m : ℕ)
    (x y : Vector N) (a : Fin n → Vector N) (b : Fin m → Vector N) :
    cov[blockJet p n x a, blockJet q m y b; disorderLaw N P] =
      if p = q then
        cov[fun J : PureDisorder N p.val.val =>
              iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x a,
            fun J => iteratedFDeriv ℝ m (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) y b;
          PureLaw N p.val.val]
      else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    rw [ite_eq_left rfl]
    have hmap := (degree_block_hasLaw (N := N) p).map_eq
    have hcov := covariance_map_fun
      (X := fun J : PureDisorder N p.val.val =>
        iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x a)
      (Y := fun J : PureDisorder N p.val.val =>
        iteratedFDeriv ℝ m (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) y b)
      (by rw [hmap]; exact
        (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp n x a).aestronglyMeasurable)
      (by rw [hmap]; exact
        (SphericalAging.HamiltonianDerivativeCovariance.Hamiltonian_derivative_memLp m y b).aestronglyMeasurable)
      (degree_block_hasLaw p).aemeasurable
    rw [hmap] at hcov
    exact hcov.symm
  · rw [ite_eq_right hpq]
    have hX : Measurable (fun J : PureDisorder N p.val.val =>
        iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x a) := by
      have heq : (fun J : PureDisorder N p.val.val =>
          iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x a) =
          pureJetCLM N p.val.val n x a := by
        funext J
        exact (pureJetCLM_apply x a J).symm
      rw [heq]
      exact (pureJetCLM N p.val.val n x a).measurable
    have hY : Measurable (fun J : PureDisorder N q.val.val =>
        iteratedFDeriv ℝ m (SphericalAging.FiniteModel.Hamiltonian N q.val.val J) y b) := by
      have heq : (fun J : PureDisorder N q.val.val =>
          iteratedFDeriv ℝ m (SphericalAging.FiniteModel.Hamiltonian N q.val.val J) y b) =
          pureJetCLM N q.val.val m y b := by
        funext J
        exact (pureJetCLM_apply y b J).symm
      rw [heq]
      exact (pureJetCLM N q.val.val m y b).measurable
    exact ((independent_degree_blocks N P).indepFun hpq |>.comp hX hY).covariance_eq_zero
      (blockJet_memLp p n x a) (blockJet_memLp q m y b)

/-- The actual mixed-jet covariance is the coefficient-weighted sum of the
actual pure-block covariances. Cross-degree contributions vanish by independence. -/
theorem jet_covariance {N P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (n m : ℕ) (x y : Vector N) (a : Fin n → Vector N) (b : Fin m → Vector N) :
    cov[jet c n x a, jet c m y b; disorderLaw N P] =
      ∑ p : Degree P, c p *
        cov[fun J : PureDisorder N p.val.val =>
              iteratedFDeriv ℝ n (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) x a,
            fun J => iteratedFDeriv ℝ m (SphericalAging.FiniteModel.Hamiltonian N p.val.val J) y b;
          PureLaw N p.val.val] := by
  classical
  have heqX : jet c n x a = fun J => ∑ p : Degree P, Real.sqrt (c p) * blockJet p n x a J :=
    funext (jet_sum c n x a)
  have heqY : jet c m y b = fun J => ∑ p : Degree P, Real.sqrt (c p) * blockJet p m y b J :=
    funext (jet_sum c m y b)
  rw [heqX, heqY]
  change cov[fun J => ∑ p : Degree P, Real.sqrt (c p) * blockJet p n x a J,
      fun J => ∑ p : Degree P, Real.sqrt (c p) * blockJet p m y b J; disorderLaw N P] = _
  rw [covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left, covariance_const_mul_right, blockJet_covariance]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_eq_single p]
    · simp only [ite_true]
      have hroot : Real.sqrt (c p) * Real.sqrt (c p) = c p := Real.mul_self_sqrt (hc p)
      rw [← mul_assoc, hroot]
    · intro q hq hqp
      simp [Ne.symm hqp]
    · simp
  · intro p
    exact (blockJet_memLp p n x a).const_mul _
  · intro p
    exact (blockJet_memLp p m y b).const_mul _

/-- The ordinary second derivative covariance polynomial. -/
def secondCovariance {P : ℕ} (c : Degree P → ℝ) (r : ℝ) : ℝ :=
  ∑ p : Degree P, c p * (p.val.val : ℝ) * ((p.val.val : ℝ) - 1) * r ^ (p.val.val - 2)

                                                                              
                                                              
                                                                  
                         

                                                                            
                                                             
                                                                                  
                                                         
                                                           

                                                              
                                                                   
                                                  

                                                                           
                                                                  
                                                                 
                                           
                                                            
                                                              
                                         

                                                                        
                                                                  
                                                        
                                                                 
                                                       
                                                                                
                                                                          
                                        
                                                              
                                                                    
           
                     
                          
                             
                                             
                                                                                                  
                                   
                                                                                                      
                                                                                 
                                                              
                                                                    
                                                                                         
                                                           
                                                  
                                                                                                 
                                                                                                        
                                   
                                                                                                         
                 
                         
                                     
                            
            
      

                                                                              
                                                         
                                                                 
                                                       
                                                              
                                                                         
                             
                                                                          
               
                                                
                                                            
                                                     
                                                                                                  
             

                                                          
                                                              
                                
                                     
                                                    

                                                  
                                                                 
                                                       
                                                                                  
                                                            
                                                                       
           
                                                       
                              
                             
                                                                   
                                            
            
         
                              
                                        
                                                  
                                                              
                                                     
                                      
                    
                                   

                                                                         
                                                                         
                                                                  
                                                                 
                                                       
                                                              
                               
                                                                                     
                          
                                                             
                                              

                                                                            
                                                                  
                                                                                
                                                                       
                                                  
           
                                                                        
              
                                                                         
                                                                                        
                                                                
                          
                              
              
                    
         
                                                      
      
                                                                                 
                                               
                                                            
                                                           
                                             
                                                                       
                                                                
                                                            
                                                                                 
                     

                                                                          
                                                           
                                                                                
                                                              
                         
                                  
                                                    
      
                                                                                      
                                    
                     
                                                                                               
                                
                
                                    
                                             
              

                                                                             
                                                                                   
                                                          
                                                                  
                                                                  
                                                                
                                                                              
                             
         
                                                                                
      

                                                                           
                                   
                                                                           
                              

                                                                 
                                              
                                                                                     

                                                          
                                                             
                                                                                          
                               
                                              
                                                                              
                           
                                                                        
                             

                                                                           
                                                   
                                                       
                                                                                
                                                                          
                         
                            
            
                                                         
      

                                                                   
                                                                    
                                                                                    
           
                                            
                     
                            
            
                              
                                                               
                                                
      
                                                                                
                                 

                                                                       
                                                      
                                                               
                                                              
                                           
                                                                                     
                                                                            
                                                          
                                       
                                                             
                                       
                                                
                                                  
                                                                             
                                            
                                                                                       

                                                                        
                                                                    
                                                                                   
                                                                       
                                   
                                                   
                                                                
                                                        
                                                                                                     

                                                                       
                                                                         
                                                                 
                                                                      
                                   
                                                                                    
                                                                                  
                                                      
                       
                                                                                             
                                                                                    
                              
                                                                                        
                                     
                                                                                            
                                                                                  
                                                        
                                                           
                                                           
                                                                              
                                                                               
                                                                                           
           
      

                                                                         
                                                           
                                                                    
                                                                        
                                   
                                                                                    
                                                                                  
                                            
                       
                                                                                             
                                                                                                   
                                                                                        
                                     
                                                                                            
                                                           
                                                                                        
                                                                                                  
                                                              
                                                                                          
                                                                                      
                                                                                    
                                                                                                 
                                                             
                
                                                                                     
                                                     
                             
                                                                         
                                    
                                                       
                                                                                  
                                                                                 
                                                    
            
                                                                                                      
                                                                                           
                                                          
                                                                               
                    
                     
                                                                      
                                                                       
                                                                               
                                                
                                                           
                 

                                                                    
                                                             
                                                     
                                                                                            
                     
                          
                          
            
                                                                                              

                                                                       
                                                             
                                                                    
                                                                                  
                     
                          
                          
            
                                                                                                   

                                                                     
                                                                             
                                                               
                                                                  
                                              
                                        

                                                                  
                                                                       
                                               
                                                 
                                            

                                                                                    
                                               
                                                          
          
                                                    

                                                                       
                                                                           
                                                                                  
                                                                          
                                                             
                                                              
                                                                               
                                                    
                                                      
                                                                               
                           
                                                                                
                                             
          
               
           
                                          
            
              
                                                                               
                                                                                          

                                                                 
                                                                         
                                                                                      
                                                                    
                               
                                                                             
                                                                                                   
                                                                           
         
                                
              
                                                                         
                                                                
      

                                                                            
                                                                        
                                                                                       
                                              
                                                                
              
                           
                   
                            
            
      

def firstCovariance {P : ℕ} (c : Degree P → ℝ) (r : ℝ) : ℝ :=
  ∑ p : Degree P, c p * (p.val.val : ℝ) * r ^ (p.val.val - 1)

                                                                               
                                                             
                                                                                    
                                                           

                                                                   
                                                                              
           
                                           
                     
                            
            
                              
                                                           
                                                                      
      
                                                        
                                 

                                                                            
                                                                                    
                                                
      

                                                                           
                                             
                                                                                   
                                                                                           
                                                                       
                                                                    
                                                                                             

                                                                        
                                             
                                                      
                                                                                
                                                                                  
                                                            
                                                      
                                                                                       

                                                                  
                                             
                                                      
                                                                      
                                                                                  
                                                                
                           
                                                            
                                               
      

                                                                           
                                                                         
                                                                 
                                                                                    
                                         
           
                          
                                                                            
                      
                 
                        
                              
                     
                            
            
      

                                                                   
                                                                 
                                                                          
                                                                  
           
                          
                                                                      
                      
                 
                                         
                              
                                               
                            
            
      

                                                                    
                                                                           
                                                            
                                                              
                                             
                                                         
                                                                           
                                                     
                                                                 
                                                            
                                                       
                                                                                  
                                                       
                                                                                                   
                     
                                                                                         
                                                                                        
                                   
                                                                                              
                                                                                        
                                                        

                                                                            
                                                                        
                                                      
                                                                      
                                                                                  
                                                                
                       
                                                                                                  
                                                                                                   
                                                                                        
                                     
                                                                                            
                                                                                  
                             
                                                                                                   
                                                                               
      

                                                                    
                                               
                                                          
                                          
                                                                        
                                                                          
                                             
           
                          
                                                                                
                             
                 
                        
                              
                     
                            
            
      

                                                                            
                                                            
                                     

                                                                               
                                           
                                                                          
                                                                        

                                                                       
                                                         
                                                                          
                                       
                                                                                              
                                                                                        
               
                                                                                     
                                                                    
                                                            

                                                                 
                                                         
                                                                          
                                                   
                                                                         
                                                                             
                                                                    
                              
                             
                                                                                
                                 
            
         
                              
                                        
                                                                                     
                                                                    
                                
      

                                                                       
                                                                         
                           
                                                                       
                                                         
                                                                          
                                       
                                             
                                                                                   
                          
                                                                           
                                                             

                                                                            
                                                              
                                           
                                                                                     
                                                                                          
                                                                           
                                       
                                                     
                                                  
                                                                                            
                                                                      

                                                     
                                             
                                                      
                                                                                
                                                                                  
                                            
                      
                       
                                                                                                  
                                                                                    
                              
                                                                                        
                                     
                                                                                            
                                                                                  
                                                        
                                                                                    
                 

                                                      
                                             
                                                      
                                                                      
                                                                                  
                                            
                                                               
                                          
                           
                                             

                                                                           
                                                                 
                                                                                            
                          
                          
            
                                                           

                                                                            
                                                                 
                                                                                  
                          
                          
            
                                                            

                                                                     
                                                                             
                                                                              
                                                             
                                       
                                                     
                                                                
                                                    
                                                     
                                                                              
                           
                                 
                                                                                     
                                             
          
           
                                          
           
              
                                                                              
                                                                                 

                                                                       
                                                             
                                                             
                                                     
                                                                               

                                                                               
                                                               
                                                                           
                                     

                                                              
def symmetricMatrix {k : ℕ} (a : UpperIndex k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => if h : i ≤ j then a ⟨(i, j), h⟩ else a ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

theorem symmetricMatrix_measurable (k : ℕ) : Measurable (symmetricMatrix (k := k)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold symmetricMatrix
  split_ifs <;> exact measurable_pi_apply _

/-- A genuine GOE law constructed as a symmetric matrix of independent
centered Gaussian upper entries, with off-diagonal variance `s/N`. -/
def goeLaw (k N : ℕ) (s : ℝ) : Measure (Matrix (Fin k) (Fin k) ℝ) :=
  (Measure.pi (fun ij : UpperIndex k => gaussianReal 0
    (((s / (N : ℝ)) * (if ij.val.1 = ij.val.2 then 2 else 1)).toNNReal))).map symmetricMatrix

                                                                       
                                                              
                                                                        
         
                                      
           
       
                                       

                                                                         
                                                                    
                                                              
                                                                 
                                                       
                                                              
                                                                                            
                                                                  
                                                                                                 
                                                              
               
                                                                                       

                                                           
                                                              
                                           
                                                                                     
                                                                             
                                                                      
                                            
                                                  
                                                                             
                                            
                                                                        

                                                                                
                                                                                       
                               
         
              
                                                                                
                                                                          

instance goeLaw_probability (k N : ℕ) (s : ℝ) : IsProbabilityMeasure (goeLaw k N s) := by
  unfold goeLaw
  exact (hasLaw_map (P := Measure.pi (fun ij : UpperIndex k => gaussianReal 0
      (((s / (N : ℝ)) * (if ij.val.1 = ij.val.2 then 2 else 1)).toNNReal)))
    (symmetricMatrix_measurable k).aemeasurable).isProbabilityMeasure_iff.mp inferInstance

/-- The GOE marginal admits this explicit everywhere-defined constant
conditional kernel. This is a kernel for the Hessian marginal; it does not
assert that the whole-field coefficient regression version has been built. -/
def hessianConditionalKernel (k d N : ℕ) (s : ℝ) :
    Kernel (Option (Fin d) → ℝ) (Matrix (Fin k) (Fin k) ℝ) :=
  Kernel.const _ (goeLaw k N s)

instance hessianConditionalKernel_markov (k d N : ℕ) (s : ℝ) :
    IsMarkovKernel (hessianConditionalKernel k d N s) := by
  unfold hessianConditionalKernel
  infer_instance

                                                                            
                                                                             
                                                              
                                                                              
                                                                 
                                                       
                                                                                     
                                                    
                                                               
                                                                                           
                                                                      
                                                                             
                                                
                                                                               
                               
            
                                                         
                                       
                                                                                
                   
                                                                                                      
                                 
                             
                              
                  

                                                                      
                                                            
                                                                                     
                                                            

end
end SlowEquilibration.SphericalGaussianJet
