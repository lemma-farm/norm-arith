-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGibbs
public import Lemmas.SpinGlass.gaussian_concentration

@[expose] public section

namespace SlowEquilibration.SphericalModel

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators InnerProductSpace

/-- All actual ordered tensor coordinates, with the degree label retained. -/
abbrev Coordinate (N P : ℕ) :=
  (p : Degree P) × SphericalAging.FiniteModel.TensorIndex N p.val.val

abbrev EuclideanDisorder (N P : ℕ) := EuclideanSpace ℝ (Coordinate N P)

def flatDisorder {N P : ℕ} (J : Disorder N P) : Coordinate N P → ℝ :=
  fun k => J k.1 k.2

def euclideanDisorder {N P : ℕ} (J : Disorder N P) : EuclideanDisorder N P :=
  WithLp.toLp 2 (flatDisorder J)

def unpackDisorder {N P : ℕ} (g : EuclideanDisorder N P) : Disorder N P :=
  fun p I => g ⟨p,I⟩

@[simp] theorem unpack_euclideanDisorder {N P : ℕ} (J : Disorder N P) :
    unpackDisorder (euclideanDisorder J)=J := rfl

theorem flatDisorder_measurable (N P : ℕ) : Measurable (flatDisorder (N:=N) (P:=P)) := by
  apply Measurable.of_eval
  intro k
  exact (measurable_pi_apply k.2).comp (measurable_pi_apply k.1)

/-- Flattening is proved to preserve the actual independent Gaussian law;
no isotropic Euclidean disorder law is substituted without identification. -/
theorem flatDisorder_hasLaw (N P : ℕ) :
    HasLaw (flatDisorder (N:=N) (P:=P))
      (Measure.pi (fun _ : Coordinate N P => gaussianReal 0 1)) (disorderLaw N P) := by
  refine ⟨(flatDisorder_measurable N P).aemeasurable,?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (flatDisorder_measurable N P) (MeasurableSet.pi Set.countable_univ (fun k _=>hs k))]
  have hpre : flatDisorder (N:=N) (P:=P) ⁻¹' Set.pi univ s =
      Set.pi univ (fun p : Degree P => Set.pi univ (fun I => s ⟨p,I⟩)) := by
    ext J
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,true_implies,flatDisorder]
    change (∀ k : Coordinate N P,J k.1 k.2 ∈ s k) ↔
      ∀ p : Degree P, ∀ I,J p I ∈ s ⟨p,I⟩
    constructor
    · exact fun h p I => h ⟨p,I⟩
    · exact fun h k => h k.1 k.2
  rw [hpre,disorderLaw,Measure.pi_pi]
  simp only [SphericalAging.FiniteModel.disorderLaw,Measure.pi_pi]
  exact (Fintype.prod_sigma (fun k : Coordinate N P => (gaussianReal 0 1) (s k))).symm

theorem euclideanDisorder_hasLaw (N P : ℕ) :
    HasLaw (euclideanDisorder (N:=N) (P:=P))
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N P)) (disorderLaw N P) := by
  have hm : Measurable (WithLp.toLp 2 : (Coordinate N P → ℝ) → EuclideanDisorder N P) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable
  exact (hasLaw_map hm.aemeasurable).fun_comp (flatDisorder_hasLaw N P)

                                                                      
                                                                                       
                                                             
                                                           
                                                    

                                                       
                                                
                                                                   
                                                                           
                                                                           
                        
                            
           
                                    
                            
           
      

                                                                      
                                                          
                                                             
                                  
                                                                           
                        
                             
                     
                            
           
                                                                           
                                                                            
                                                       
                                                                            
                                                        
                                                                          
                                                                                                           
            
        
                                                                                     
                                                                                                                
                                          
                                                                              
                                                                            
                                                       
                                                                            
                                                              
                                                                         
                                  
                                                                                              
                                                               
                                          
                                                                               
                                                                          
                                                           
                                                     
                             
      
                                                                                               
                            

                                                                   
                                                          
                                                                       
                                                                      

                                                                     
                                                                            
                                                               
                                                                       
                                       
                                                                 
                                                               
                                                              
                                                            
                                           
                                             

                                                             
                                                              
                                   
                                                
                                                                       
                                                        
                                                                                                 
                                                                                                 
                                                                                           
                                                                                
                                                       
                                                   
                      
                             
                                                                
                                         
                                                                                             
            
                                                    
                                                    

                                                              
                                                                                            

                                                           
                                                              
                                   
                                                             
                                                                 
                                                                                 
                                                                                 
                                                                                
                                                                   
                              
          

                                                                        
                                                         
                                                              
                                                                
                                                                         
                                              
                                    
           
                                                                            
                  
                                                         
                                                        
                          
          

                                                                  
                                                                            
                                                         
                                                                               
                                         
                                                               
                                                                           
                                                                                     
                                           
                                                           
                                                                               
                                                                      
                                                                                         
                                           
                                                                                          
                                                                            
                                                                 
                                                                           
                                                        
                                                                                      
                                                                                         
                              
                                                                    
                                                         
             
                                                                      
        
            
                                                                                                            

end
end SlowEquilibration.SphericalModel
