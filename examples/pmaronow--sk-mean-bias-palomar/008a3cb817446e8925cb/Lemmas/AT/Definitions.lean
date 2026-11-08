module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Lemmas.AT.FixedPoint
public import Lemmas.SpinGlass.SKModel
public import Mathlib
@[expose] public section

open MeasureTheory ProbabilityTheory Real BigOperators
open scoped ProbabilityTheory NNReal

set_option autoImplicit false

namespace SpinGlass.AT

universe u

/-!
# Definitions for the strict Almeida-Thouless argument

The declarations below follow
`refs/latalaArgumentsStrictAlmeidaThoulessCondition.tex`.  The canonical
replica-symmetric fixed point `rsQ`, its fourth moment `rsR`, and the AT
parameter `atParameter` are imported from `fixed_point`.
-/

/-! ## Replicas over the existing SK model -/

/-- An indexed family of replicas from `SpinGlass.Config`. -/
abbrev Replicas (N n : ℕ) :=
  Fin n → SpinGlass.Config N

/-- A function of finitely many replicas. -/
abbrev ReplicaFun (N n : ℕ) :=
  Replicas N n → ℝ

/-- Product Gibbs expectation formed from `SpinGlass.gibbs_pmf`. -/
noncomputable def replicaGibbsAverage {N n : ℕ}
    (H : SpinGlass.EnergySpace N) (F : ReplicaFun N n) : ℝ :=
  ∑ σs, (∏ a, SpinGlass.gibbs_pmf N H (σs a)) * F σs

/-- Disorder-averaged product Gibbs expectation. -/
noncomputable def quenchedReplicaAverage
    {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {N n : ℕ} (H : Ω → SpinGlass.EnergySpace N)
    (F : ReplicaFun N n) : ℝ :=
  ∫ ω, replicaGibbsAverage (H ω) F ∂(volume : Measure Ω)

/-- The overlap of two selected replicas, using `SpinGlass.overlap`. -/
noncomputable def replicaOverlap {N n : ℕ}
    (σs : Replicas N n) (a b : Fin n) : ℝ :=
  SpinGlass.overlap N (σs a) (σs b)

/-- The overlap centered at the replica-symmetric parameter. -/
noncomputable def centeredOverlap {N n : ℕ} (q : ℝ)
    (σs : Replicas N n) (a b : Fin n) : ℝ :=
  replicaOverlap σs a b - q

/-! ## Compact parameter data -/

                                                                        
          
                                               
                         
          
          
         
                     
                     
                   
                          
                          
                               
                                       
                                                   

                                                

                                      
                                      
                                                                  
                                                                

                                                              
                                                                        
                                                                      
               

                                                                   
                                                  
                                       
                       
                                                     
                                 

                                                      
                                                   
                                       
                                                          

                                                         
                                       
                                      
               
                                                     
      
                             
                                                     

                                  
                                              
                                                             
                                 
                                       

                                                                   
                                                                  
                                        

                                                                        
             
                                                       
                                                    
                     
                                              
                               

                                                       
                                                  
                                          
                                                               
                               

                                                   

                                                                       
                                                        
                                     
                                       
             
                                                          

                                                                           
structure RSSmartPathDisorder (Ω : Type u) [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (N : ℕ) (β h q : ℝ) where
  sk : SpinGlass.SKDisorder (Ω := Ω) N β h
  simple : SpinGlass.SimpleDisorder (Ω := Ω) N β q
  independent : IndepFun sk.U simple.V (volume : Measure Ω)

/-- The full smart-path Hamiltonian, including the deterministic field. -/
noncomputable def fullPathHamiltonian {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) (ω : Ω) :
    SpinGlass.EnergySpace N :=
  Real.sqrt s • path.sk.U ω +
    Real.sqrt (1 - s) • path.simple.V ω +
    SpinGlass.magnetic_field_vector N h

                                                             
                                                              
                                                                   
                                                         
                                    
                                             
                         

                                                                      
                                               
                             

                                                                          
                                                            
                                                                   
                                                 
                       

                                               
                                                               
                                                                   
                                                         
                                             

                                                
noncomputable def A {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  quenchedReplicaAverage (fullPathHamiltonian path s)
    (fun σs : Replicas N 4 => centeredOverlap q σs 0 1 ^ 2)

                                             
                                                 
                                                                   
                                                         
                                                     
                             
                                                          

                                               
noncomputable def C {Ω : Type u} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] {N : ℕ} {β h q : ℝ}
    (path : RSSmartPathDisorder Ω N β h q) (s : ℝ) : ℝ :=
  quenchedReplicaAverage (fullPathHamiltonian path s)
    (fun σs : Replicas N 4 =>
      centeredOverlap q σs 0 1 * centeredOverlap q σs 2 3)

                                    
                                                                   
                                                                   
                                                         
          

                                                  
                                                           
                                                                   
                                                         
                                                     
                                                             

                                                             
                                                            
                                                                   
                                                             
                                                     
                             
                                                        

                                               
                                                    
                     

                                

                                          
                                         

                                            
                                                             
                                   
                                                    

                                                 
                             

                                                         
                                                    

                                              

                                                                            
                                                          
                   
                                                       
                                  

                                                      
                                              
                                                
                                                
                                           
                                 
          

                                                        
                                               
                                 
                                               
                       
                                                           
                      
                                                                    
                           

                                      
                                                           
                                                 

                                                
                                           
                         

                                                    
                                                                          
                          
                                              

                                                   
                                                    
                                                   

                                                                       
                                    
                                                 
                         
                                                         
                                      

                                                            
                                                       
                                       
                                  

                                                                 
                                                   
                                       
                              
                               
                                   

                                                                
                                                 
                             

                                                                     
                              

                                                             
                                  
                                
                                             

                                          
                                
                                                  
              
                 
                                            
                                              
                                                 
        
                                                                
                                              
                         
                                                   

                                                                      
                               
                                                       
              
                 
                                           
                                                   
        
                                                               
                       
                                                     

                                                                       
                                     
                                    
                  
                              
                                             
                                            
                                                            
               
                                   
                           
                                                               
                 
                   
                      
                                                                     
        
                                                               
      
                                   
                           
                                                     
                 
                   
                      
                                                           
        
                                                               

                                                                          
                                                         
                                                        
                                     
                                           
                                              
                                

                                                
                                                   
                                                              

                          

                                                                
                                                   
                                                    
                                                
                                
                                                                

                                                                        
                                                   
                                                            
                                               
                                       
                                 
                                                    
                                        
           
                                                       
      
      
                                
                                                    
                                                        
                                                   
                                                   
                                   
                                                        
                                                        
                                                      
                                                         
                                  
                                                      
                                     
                                                        
                                                      
                                                         
                              
                                                      
                                      
                               
                                                          
                                
               
                                                             
                                                           
                     
                       
                  
                       
                                   
                                                                       

                                                 
                                          
                                 
                                               
                       
                                                             
                            
            
                                                                      
                           

                                                             
                                          
                                 
                                               
                       
                                                             
                                                             

                                    

                                                           
                                                            
                                                                   
                                                                 
                                 

                                          
                                  
                                    

                                                            
                                                          
                               
                               
                               
                         
                                               
                                                

                                               
                                                                 
                            

                                                               
                                                    
              
              
              

                                                    
                                                                     
               
                             
               

                                                      
                              
             

                                       
                                                       
                                                                   
                                                         
                                        

                                              
                                                       
                                                                   
                                                         
                             

                                      
                                                       
                                                                   
                                                         
                                    

                                                
                                
                   

                                                     
                               
                       

                                          
                             
                                  

                                              
                      
         
             
            
                      

                                                  
                                                                
                      
                                         
                                        
              
      
             

                                                                      
                                                         
                       
                           
                          

                                                                      
                                                               
                                                                   
                                                                 
                       
                                                                   
                                     

                                     
                                                                
                                                                   
                                                         
                                               

                                                                             
                                                         
                                                                 
                                              
                                             
                                                      
                                           
                                                            


end SpinGlass.AT
