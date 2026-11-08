-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Flow.JointSmoothBootstrap
public import AVenhance.Infra.Flow.FirstJet
public import Mathlib
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.MetricSpace.ProperSpace

/-! Recursive finite spatial-jet state spaces and their smooth augmented ODE fields. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- The state of the `n`th spatial-jet system: at each stage append the
derivative of the preceding jet with respect to the original base point. -/
def SpatialJetState : ℕ → Type
  | 0 => Vec 2
  | n + 1 => SpatialJetState n × (Fin 2 → SpatialJetState n)

instance (n : ℕ) : NormedAddCommGroup (SpatialJetState n) := by
  induction n with
  | zero => change NormedAddCommGroup (Vec 2); infer_instance
  | succ n ih =>
      change NormedAddCommGroup (SpatialJetState n × (Fin 2 → SpatialJetState n))
      letI : NormedAddCommGroup (SpatialJetState n) := ih
      infer_instance

instance (n : ℕ) : NormedSpace ℝ (SpatialJetState n) := by
  induction n with
  | zero => change NormedSpace ℝ (Vec 2); infer_instance
  | succ n ih =>
      change NormedSpace ℝ (SpatialJetState n × (Fin 2 → SpatialJetState n))
      letI : NormedAddCommGroup (SpatialJetState n) := inferInstance
      letI : NormedSpace ℝ (SpatialJetState n) := ih
      infer_instance

instance (n : ℕ) : CompleteSpace (SpatialJetState n) := by
  induction n with
  | zero => change CompleteSpace (Vec 2); infer_instance
  | succ n ih =>
      change CompleteSpace (SpatialJetState n × (Fin 2 → SpatialJetState n))
      let : CompleteSpace (SpatialJetState n) := ih
      infer_instance

instance (n : ℕ) : FiniteDimensional ℝ (SpatialJetState n) := by
  induction n with
  | zero => change FiniteDimensional ℝ (Vec 2); infer_instance
  | succ n ih =>
      change FiniteDimensional ℝ (SpatialJetState n × (Fin 2 → SpatialJetState n))
      let : FiniteDimensional ℝ (SpatialJetState n) := ih
      infer_instance

instance (n : ℕ) : Nontrivial (SpatialJetState n) := by
  induction n with
  | zero => change Nontrivial (Vec 2); infer_instance
  | succ n ih =>
      change Nontrivial (SpatialJetState n × (Fin 2 → SpatialJetState n))
      let : Nontrivial (SpatialJetState n) := ih
      infer_instance

                                                                            
                                                                              
                                             
                                                          
                           
                      
                                                    
                                                                    

                                                                              
                                                                                  
                              
                                                          
                                                                    
         
                  
           
                                              
                     
                
                                                                              
                                                       
                          
                                
                                           
                                               
                                     
                                                                                  
                                                       
                                                           
                                    
                                 
                                             
                                                    
                                                                     
                                        
                   
                                
                                           
                                                               
                
                               
                                           
                                                           
                      
                                 
                                           
                                                              
                      
                              
                                                                           
                                                    
                           
               
                                      
                                                                             
                                     
                                          
                         
                                                                         
                                                           
                             

                                                                        
                                                                            
                                                                    
                                                 
                                                                
                                                
                                     
                                                                              
                                                      
                                          
                                                         
                                                     
                                      
                                             
                                         
                                        
                                                        
                                                      
                               
                                                                   
                                              
                                                                 
                                     
                                                                    
                                         
                                   
                                                              
                         
                        
                
            
                                                           
              
                                                            
                                                                          
                
                        
                                                 
              
                                                             
                                                          
                                                                 
                                                    
                                 
                                                                    
                                                
                                 
                                                                          
                    
                     
                                              
                                                            
                                 
          
                                 
                                                                
                                              
                                     
                                                    
                                                       
                                

                                                                            
                                                                              
                                                                                
                                             
                                                                
                                                         
                                           
                                           
                                      
                             
                                                  
                                                   
                                         
           
                                   
                                                   
                                         
           
                                   
                                                                  
                                                                  
                                                  
                                                        
                                                  
                                                        
                                                                                        
                                                                          
                                             
                                           
            
                               
                                             
                                           
            
                               
            
                      
                                                       
                                                                      
                                                              
                       
                                            
                                       
                                                    
                                                 
                                               
                                       
                                                    
                                                 
                                               
                                       
                                  
                              
                                        
                                                     
                                                                      
                                                              
                       
                                                       
                            
                                                    
                                                 
                                                          
                            
                                                    
                                                 
                                                          
                            
                                  
                             

                                                                          
                            
                                            
                             
                                               
            
                            
                
       
            
                                                      
                                                           
                                          
       

end

end AVenhance.Infra.Flow
