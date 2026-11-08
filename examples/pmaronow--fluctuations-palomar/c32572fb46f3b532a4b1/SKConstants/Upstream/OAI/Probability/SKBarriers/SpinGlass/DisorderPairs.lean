module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/SpinGlass/DisorderPairs.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.SpinGlass.Basic

@[expose] public section

namespace SKConstantsOAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK
def disorderPairLaw (n : ℕ) : Measure (Disorder n × Disorder n) :=
  (disorderLaw n).prod (disorderLaw n)

instance disorderLaw_isGaussian (n : ℕ) : IsGaussian (disorderLaw n) := by
  have h := (disorder_gaussian n).isGaussian_map
  change IsGaussian (Measure.map id (disorderLaw n)) at h
  rwa [Measure.map_id] at h

instance disorderPairLaw_probability (n : ℕ) : IsProbabilityMeasure (disorderPairLaw n) := by
  unfold disorderPairLaw
  infer_instance

                                      
                                                            
                                            
                              

                                      
                                                            
                                            
                              

                                          
                                                              
                                        
                                                                 
                               
                 

                                       
                                                                                
                                                                                     
                                           

                                                              
                                                     
                                               
                                                               

                                                              
                                                     
                                               
                                                               

                                                            
                                                 
                                                                    
                                  
                                                  
                                                                                      
                               

                                                            
                                                 
                                                                    
                                  
                                                  
                                                                                      
                               

                                                              
                                                 
                                                                            
                                                                  
                                               
                                                                  
                                                                  

                                                                     
                                                         
                                                                               
                   
                                                                    
                                                   
                                                       
                                                     
                                                   
                                                           
                                              
                                                                            
                                                                            
                                                                   
      

                                                                               
                   

                                                                                    
                                                           
                                                         

                                                                                      
                                                     

                                                
                                                                    
                                                          

                                                         
                                                           
                                                                                      
                  
                                                                               
                                                                                
                                           
                                                    
                                                    
      

                                                                     
                                                                                        
                                                      
                                                                      
                                                                                    
                                   
                                                                
                                                                
                                                                
                                                                 
                                                                                            
                                                                 
                                  
      

                                                                              
                  
                                                                                      
                                                
                              
                                               
                                                              
                               
                                                  
        
          

                                                                     
                                                                               
                                                                           
                                                                    
               
                                                         

                                                                  
                              
                                           
                                              

                                       
                                                              
                                                   
                                                  

                                                                                       
                                                       

                                                 
                                                                     
                                                           

                                            
                                                                                    
                                                                       
                                                                         
                                                                   
             
                               
        
                        
                                                                   
                                                                   

def directionalEnergy {n : ℕ} (β : ℝ) (J K : Disorder n) : ℝ :=
  β * ∑ x : Config n, gibbs β J x * hamiltonian K x

theorem directionalEnergy_exp_le {n : ℕ} (β ℓ : ℝ) (J K : Disorder n) :
    Real.exp (ℓ * directionalEnergy β J K) ≤
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x) := by
  have h := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := gibbs β J) (p := fun x => ℓ * β * hamiltonian K x)
    (fun x _ => le_of_lt (gibbs_pos β J x)) (gibbs_sum β J)
    (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, ← Finset.mul_sum, directionalEnergy, mul_assoc,
    mul_left_comm (gibbs β J _)] using h

theorem continuous_hamiltonian {n : ℕ} (x : Config n) :
    Continuous (fun J : Disorder n => hamiltonian J x) := by
  unfold hamiltonian
  fun_prop

theorem continuous_partition {n : ℕ} (β : ℝ) :
    Continuous (partition (n := n) β) := by
  unfold partition
  exact continuous_finsetSum _ (fun x _ =>
    Real.continuous_exp.comp (continuous_const.mul (continuous_hamiltonian x)))

theorem continuous_gibbs {n : ℕ} (β : ℝ) (x : Config n) :
    Continuous (fun J : Disorder n => gibbs β J x) := by
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_hamiltonian x))).div
    (continuous_partition β) (fun J => ne_of_gt (partition_pos β J))

                                                                      
                         
                      
                                                                                        

                                                         
                                                                        
                                                                                    
                          
                                                                                      

theorem continuous_directionalEnergy {n : ℕ} (β : ℝ) :
    Continuous (fun p : Disorder n × Disorder n => directionalEnergy β p.1 p.2) := by
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun x _ =>
    ((continuous_gibbs β x).comp continuous_fst).mul
      ((continuous_hamiltonian x).comp continuous_snd))

theorem directionalEnergy_exp_integrable {n : ℕ} (β ℓ : ℝ) (J : Disorder n) :
    Integrable (fun K : Disorder n => Real.exp (ℓ * directionalEnergy β J K))
      (disorderLaw n) := by
  have hsum : Integrable (fun K : Disorder n =>
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x))
      (disorderLaw n) :=
    integrable_finsetSum _ (fun x _ =>
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _)
  apply hsum.mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_directionalEnergy β).comp (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · filter_upwards [] with K
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ J K

theorem directionalEnergy_exp_integral_le {n : ℕ} (hn : 0 < n)
    (β ℓ : ℝ) (J : Disorder n) :
    (∫ K : Disorder n, Real.exp (ℓ * directionalEnergy β J K) ∂disorderLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hsum (x : Config n) : Integrable (fun K : Disorder n =>
      gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) (disorderLaw n) :=
    (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _
  calc
    _ ≤ ∫ K : Disorder n, (∑ x : Config n,
        gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) ∂disorderLaw n :=
      integral_mono (directionalEnergy_exp_integrable β ℓ J)
        (integrable_finsetSum _ (fun x _ => hsum x)) (directionalEnergy_exp_le β ℓ J)
    _ = _ := by
      rw [integral_finsetSum _ (fun x _ => hsum x)]
      simp_rw [integral_const_mul, hamiltonian_exp_integral hn]
      rw [← Finset.sum_mul, gibbs_sum, one_mul]

                                                                 
                                                  
                                                                           
                                                            
                                                                           
                               
                              
             
                                         
                                                                
                  
                                   
                                                                                   
                            
                                                                    
                                          

                                                                               
                                   
                                                                      
                                                      
                                                                                   
      
                          
                                                                    
                                                                                  
                                                                       
                    

                                                                                        
                                       
                                                         
                                                                                
                                                                          
      

end SK
end
end
end

end SKConstantsOAI
