-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Pressure.DecompositionPotentials

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

set_option autoImplicit false
noncomputable section

namespace CKN

                                                                
                                                           
                                                          
                                                                    
            
                                                                 

                                                                              
                                                           
                                                           
                                                           
                                 
                                                         
                                                             
                                                     
                                                           
                                              
           
                                           
                                                                              
                      
                    
                                      
      
                                           
                                       
                             
                              
          
                  
                    

structure PressureP1DistributionalData
    {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {η ψ : Vec3 → ℝ} (s : ℝ) : Prop where
  hcut : ∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x) =
      (∫ x in Ω, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) +
        (∫ x in Ω, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) +
        (∫ x in Ω, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j *
            (spatialDeriv η i x * spatialDeriv ψ j x)) +
        (∫ x in Ω, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j *
            (spatialDeriv η j x * spatialDeriv ψ i x)) -
        (∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x)) -
        2 * (∫ x in Ω, (spatialGradDot η ψ x) * p (x, s)) -
        (∫ x in Ω, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) -
        (∫ x in Ω, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x))
  hA : Integrable (fun x => η x * p (x, s) * spatialLaplacian ψ x) volume
  hAΩ : tsupport (fun x => η x * p (x, s) * spatialLaplacian ψ x) ⊆ Ω
  hB0 : Integrable (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) volume
  hB0Ω : tsupport (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) ⊆ Ω
  hB1 : Integrable (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) volume
  hB1Ω : tsupport (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) ⊆ Ω
  hB2 : Integrable (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j *
      (spatialDeriv η i x * spatialDeriv ψ j x)) volume
  hB2Ω : tsupport (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j *
      (spatialDeriv η i x * spatialDeriv ψ j x)) ⊆ Ω
  hB3 : Integrable (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j *
      (spatialDeriv η j x * spatialDeriv ψ i x)) volume
  hB3Ω : tsupport (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j *
      (spatialDeriv η j x * spatialDeriv ψ i x)) ⊆ Ω
  hC5 : Integrable (fun x => p (x, s) *
    (ψ x * spatialLaplacian η x)) volume
  hC5Ω : tsupport (fun x => p (x, s) *
    (ψ x * spatialLaplacian η x)) ⊆ Ω
  hC6 : Integrable (fun x => spatialGradDot η ψ x * p (x, s)) volume
  hC6Ω : tsupport (fun x => spatialGradDot η ψ x * p (x, s)) ⊆ Ω
  hF7 : Integrable (fun x => ∑ i,
    f (x, s) i * (η x * spatialDeriv ψ i x)) volume
  hF7Ω : tsupport (fun x => ∑ i,
    f (x, s) i * (η x * spatialDeriv ψ i x)) ⊆ Ω
  hF8 : Integrable (fun x => ∑ i,
    f (x, s) i * (ψ x * spatialDeriv η i x)) volume
  hF8Ω : tsupport (fun x => ∑ i,
    f (x, s) i * (ψ x * spatialDeriv η i x)) ⊆ Ω
  hQ : Integrable (fun x => (pressureP2 η u c s x + pressureP3 η u c s x +
    pressureP4 η u c s x + pressureP5 η p s x + pressureP6 η p s x +
    pressureP7 η f s x + pressureP8 η f s x) * spatialLaplacian ψ x) volume
  hP2 : Integrable (fun x => pressureP2 η u c s x * spatialLaplacian ψ x) volume
  hP3 : Integrable (fun x => pressureP3 η u c s x * spatialLaplacian ψ x) volume
  hP4 : Integrable (fun x => pressureP4 η u c s x * spatialLaplacian ψ x) volume
  hP5 : Integrable (fun x => pressureP5 η p s x * spatialLaplacian ψ x) volume
  hP6 : Integrable (fun x => pressureP6 η p s x * spatialLaplacian ψ x) volume
  hP7 : Integrable (fun x => pressureP7 η f s x * spatialLaplacian ψ x) volume
  hP8 : Integrable (fun x => pressureP8 η f s x * spatialLaplacian ψ x) volume
  hPair2 : ∫ x, pressureP2 η u c s x * spatialLaplacian ψ x =
    ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
      (mixedSecond η i j x * ψ x)
  hPair3 : ∫ x, pressureP3 η u c s x * spatialLaplacian ψ x =
    ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
      (spatialDeriv η i x * spatialDeriv ψ j x)
  hPair4 : ∫ x, pressureP4 η u c s x * spatialLaplacian ψ x =
    ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
      (spatialDeriv η j x * spatialDeriv ψ i x)
  hPair5 : ∫ x, pressureP5 η p s x * spatialLaplacian ψ x =
    -∫ x, p (x, s) * (ψ x * spatialLaplacian η x)
  hPair6 : ∫ x, pressureP6 η p s x * spatialLaplacian ψ x =
    -2 * ∫ x, spatialGradDot η ψ x * p (x, s)
  hPair7 : ∫ x, pressureP7 η f s x * spatialLaplacian ψ x =
    -∫ x, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)
  hPair8 : ∫ x, pressureP8 η f s x * spatialLaplacian ψ x =
    -∫ x, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)

                                                    
                                                             
                                                                
                    
                                                               
                            
                                                                           
                              
                                                                           
                              
                                            
                                                          
                              
                                            
                                                          
                                                               
                                                             
                                                                    
                                                                   
                                                                             
                                                                         
                                         
                                                                           
                                        
                                                                        
                                         
                                                                           
                                        
                                                                        
                                         
                                      
                                                          
                                        
                                      
                                                       
                                         
                                      
                                                          
                                        
                                      
                                                       
                                          
                                           
                                         
                                        
                                                                        
                                                                    
                                    
                                                      
                                   
                                                   
                                    
                                                      
                                   
                                                   
                                                                             
                                                                      
                                                                              
                                                                                    
                                                                                    
                                                                                    
                                                                                  
                                                                                  
                                                                                  
                                                                                  
                                                                
                                                     
                                    
                                                                
                                                     
                                                  
                                                                
                                                     
                                                  
                                                              
                                                    
                                                              
                                                
                                                              
                                                         
                                                              
                                                           
                                                          
                                                           
                                 
                                                                    
                                         
                                                                
                                         
                                                                
                                         
                                                                              
                                         
                                                                              
                                                                       
                                                               
                                                                            
                                                                            
                                                                     
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                   
                                                              
                                               
                                               
        
                                            
                                            
                               
                                
                 
            
                   
                                               
                                               
                                                   
                                                   
           
                                                         
                                               
                                                       
        
                                            
                                               
                                               
                                                   
                                                      
                                                   
                                                       
                                                               
                                         
                                        
                                                         
                                                                        
                                                                             
                                                             
                                                     
                     
                                                            
                                                            
                                                            
                                                          
                                                          
                                                          
                                                              
                                                                 
          
                                                                       
                                                                        
                                                                         
                                                            
                                                            
                                                            
                                                          
                                                          
                                                          
                                                              
          
                                                              
                                                         
                                                         
                                                       
                                                       
                                                       
                                                           
                                 
                                  
              
                                                                         
        
                                                            
                                                       
                                              
                                                    
                                                              
                                                              
                                                            
                                                            
                                                            
                                                            
                                     
            
                           
                                                        
                                               
                                                     
                                                               
                          
                                                    
                                                                            
                                                                         
                                    
            
                           
                                                                   
                                                                    
                                                                    
                                                                  
                                                                  
                                                                  
                                                                            
                                                                    
                                                                             
                                                                      
                                                                     
                                                                          
                 
            
                                              
        
                                                                 
                                                        
                                                                     
                     
                      
             
                 
        
      
                                                                             
                                                             
                                 
                             
                              
                    
                                
                
                                
                
          

end CKN
