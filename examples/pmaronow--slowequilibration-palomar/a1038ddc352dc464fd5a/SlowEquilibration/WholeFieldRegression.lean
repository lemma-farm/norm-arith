-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFiberDensity
public import SlowEquilibration.SphericalConcentration
public import SlowEquilibration.SphericalGaussianJet
public import SlowEquilibration.ScoreCovariance
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Canonical regression of the actual tensor disorder

Flattening is proved to preserve the genuine finite tensor Gaussian law.
The regression kernel retains every disorder coordinate, so its disintegration
applies to arbitrary Borel marks of the whole random field.
-/

@[expose] public section

namespace SlowEquilibration.WholeFieldRegression

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

/-- Actual unflattening, as a continuous linear map. -/
def unpackCLM (N P : ℕ) : EuclideanDisorder N P →L[ℝ] Disorder N P :=
  ContinuousLinearMap.pi (fun p => ContinuousLinearMap.pi
    (fun I => EuclideanSpace.proj ⟨p, I⟩))

@[simp] theorem unpackCLM_apply {N P : ℕ} (g : EuclideanDisorder N P) :
    unpackCLM N P g = unpackDisorder g := rfl

                                                                             
theorem actual_flattened_gaussian (N P : ℕ) :
    HasLaw (euclideanDisorder (N := N) (P := P))
      (stdGaussian (EuclideanDisorder N P)) (disorderLaw N P) := by
  simpa only [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian] using
    euclideanDisorder_hasLaw N P

/-- Actual derivative of the random field as a linear observation of all coefficients. -/
def flatJetCLM {N P : ℕ} (c : Degree P → ℝ) (n : ℕ) (x : Vector N)
    (a : Fin n → Vector N) : EuclideanDisorder N P →L[ℝ] ℝ :=
  (jetCLM c n x a).comp (unpackCLM N P)

@[simp] theorem flatJetCLM_apply {N P : ℕ} (c : Degree P → ℝ) (n : ℕ)
    (x : Vector N) (a : Fin n → Vector N) (g : EuclideanDisorder N P) :
    flatJetCLM c n x a g = jet c n x a (unpackDisorder g) := by
  simp [flatJetCLM]

                                                                        
                                                         
                                                                           
                                                     

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Canonical whole-field conditional kernel, with the original tensor
coordinates retained at every target observation. -/
def coefficientKernel {N P : ℕ} (A : EuclideanDisorder N P →L[ℝ] F) :
    Kernel F (Disorder N P) :=
  (GaussianRegression.regressionKernel A).map (unpackCLM N P)

                                                 
                                                 
                                                                         
                           
                                                                                   

instance coefficientKernel_markov {N P : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] F) : IsMarkovKernel (coefficientKernel A) := by
  exact Kernel.IsMarkovKernel.map _ (unpackCLM N P).continuous.measurable

                                                                            
                                                           
                                                                           
                                                                                 
                                                             
                                                   
                                                  
                                                                                       
                                                                                    
                                                                          
                                                            
                                                                      
        
                                                                                             
                                                                                                 
                                                                   
                                                                                    
         
                       
         
                              
                                                       
                                             
                                                       
                                               

                                                                          
                                                        
                                                             
                                
                                                                                        
                                                                   
                 
                                                                        
                                                                    
                                                  
                                                            
                                                                     
                                             

                                                                           
                                             
                                                  
                                                                     
                                                                
                              
                                               
                                                                                                                                                               
                                                                      
                                                  
                                                                                                
                                                                                                                           

                                                                                          
def jetFamilyCLM {N P : ℕ} (c : Degree P → ℝ)
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (x : ι → Vector N)
    (a : (i : ι) → Fin (n i) → Vector N) :
    EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => flatJetCLM c (n i) (x i) (a i)))

@[simp] theorem jetFamilyCLM_apply {N P : ℕ} (c : Degree P → ℝ)
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (x : ι → Vector N)
    (a : (i : ι) → Fin (n i) → Vector N) (g : EuclideanDisorder N P) (i : ι) :
    jetFamilyCLM c n x a g i = jet c (n i) (x i) (a i) (unpackDisorder g) := by
  simp [jetFamilyCLM]

                                                                                        
                                                                
                                                                    
                                                        
                                                                         
                                                                       
                                                               
                                               
                               
                                                
                                                            
        
                                                              
                                                                          
            
                                                            
                                                                         
                                                                           
                                  
     

                                          
                                                                               
                                                  
                                                                          
                                                                                   
                                                                                               
         
                                   
                                                          
                                                                 
                                           
                              
          

                                                                                      
def gradientCLM {N P k : ℕ} (c : Degree P → ℝ) (u : Vector N)
    (e : Fin k → Vector N) : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  jetFamilyCLM c (fun _ => 1) (fun _ => u) (fun i _ => e i)

@[simp] theorem gradientCLM_apply {N P k : ℕ} (c : Degree P → ℝ) (u : Vector N)
    (e : Fin k → Vector N) (g : EuclideanDisorder N P) (i : Fin k) :
    gradientCLM c u e g i = jet c 1 u (fun _ => e i) (unpackDisorder g) := by
  simp [gradientCLM]

                                                                                        
                                                                 
                                                               
                                                                                     
                                                 
                                                                                     
                                         
                                                       
         
                
         
                                                          
                                                                                 
                                                                    
                                   
                                                                                              
                                                                               
                                             
          
                                               

                                                                           
                                                                                 
                                                                       
                                                               
                                                                                   
                                                                         
                                      
                                           
                                                                           
                                                                              
                            

                                                                                          
                                                          
                                                           
                                                                                       
                                                   
                                                                                  

                                                                               
                                 
                                                                                
                 

                                                                              
                                 
                                                                      
                 

                                                                            
                                                                         
                                                                  
                                                                  
                                                 
                                                                                                         
                                         
           
                                                       
                                                         
         
                               
                                                                                           
                               
                             
                                                                       
                                                                         
                        
                                                                         
                                                                         

                                                                          
                                                                      
                                                                  
                                                                                               
                                                   
                                                                                                    
                                                           
      

                                                                             
                                                                        
                                                          
                                             
                                                                                
                                      
                                            
                                                      
                                           

                                                                         
                                     
                                                                                    
           
                          
                      
              
                                                                                                      
                    
                            

                                                                                   
                                                                             
                                                                
                                                                                     
                                                                                     
                                
                                                                                               
                                                      
                                         

                                                                       
                                                        
                                                                                      
                                                                
                                                                                   
                                                                                              
                                                                           
                                                                       
                                                   
                                               
                                                                                      

                                                                             
                                                                                   
                                                                                 
                                                          
                                           
                                                                                              
                                                                      
                                                                       
                                                   
                                               
                                                                             

                                                                            
                                                                           
                                                                
                                                                                     
                                                                                                    
                             
                                                                                                  
                                                                    
                                                                      
                                                   

                                                                              
                                                                        
                                                                           
                                                                
                                                                                     
                                     
                                                                          
                                                                             
                                            
                                                                                              

                                                                                 
                                                                             
                                                                      
                                                                  
                                     
                                                                     
                                                                             
                                                                  
                                                                                 

end
end SlowEquilibration.WholeFieldRegression
