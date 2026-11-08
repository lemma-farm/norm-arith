-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Lean module/public-import adaptation).
module

public import SlowEquilibration.Upstream.OAI.MathematicalPhysics.CriticalSK.GaussianMoments

@[expose] public section


namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open scoped BigOperators NNReal
open scoped BigOperators
open scoped BigOperators InnerProductSpace
open Module
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
open Metric Set MeasureTheory
open scoped ENNReal Pointwise
open MeasureTheory Filter Set Real
open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK

section

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

                                                      
                                                     
                                           
                                              
                                        
                                                                                      
                                         
      

                                                                 
                                                                                        
                      
                           
                                                                 

                                                          
                                                     
                                                          
                           
                                        
                                                                      
                                                    
         
      

                                                             
                                           
                                                                     
                                                        
                                                                        
                                               
                                                    
                       
         
            
      

                                                         
                                                                        
                                                          
                                 
                                                                         
                                    
                                     
            
                                                                       
                                                                          
                                                        

                                                                       
                                                                        
                                                          
                                                                        
                                    
                                     
            
                                                                       
                                                                          
                                                       

                                              
                                                    
                                                              
                                
                                

                                                                     
                                          

                                                                                     
             
            
            
                                                                                           
                         
                  
                                                                 
              
                    

                                                   
                                                               
                                      
                                                                                               
                                                                                        
                      

                                                       
                                             
                                                                             
                                                
                                                   
                                
             
                    
              
                                     
              

                                                                
                                                                                        
                                 
                                                
                                                          
                                
                                           
                                                                                       
                                                           
                                        
      
                                                                                                    
                                                       
                
                 
                                                     
                        
                                  
                                                                              
                                                                                                   
                                 
                                   
                               
                                                                                          
                                             
                                                                                  
                       
                     
               

                                                                
                                                                                        
                                 
                                                
                                                          
                                      
                                  
                                             
                                                                                        
                                                         
                                                             
                                                                   
                                          
        
                                                                                                      
                                                         
                  
                   
                                                       
                          
                                    
                                                                                
                                                                                                     
                                       
                                     
                                 
                                                                
                                      
                                                                                    
                         
                       
                 
                                                 
                                                                   
                                                                 
                  
                                                                     
                                                                           
                                                              
                                                        
              
              

                                                          
                                                                                          
                                     
                                                                   
                                                         
                                                             
         
                                                        
                                                                                                
           
                                            
                                    
                                    
             

                                                                

                                                       
                      
          

                                                                     
                                     

                                                                                               
                                                                     
                                                                                
                                                  

                                                                                   
                                                          
                                                                            
                                                      
                                                
                                                                           

                                                                               
                                                                          
                                                  

                                                
                                                                             
                                                 
                                                                 

                                                  
                                                                           
                                                                             
                                                         
                                                                 
                                                                               
              
                                                       
                                                         
           
                                                                                   
             
                                                              
                                                                                       
      
                                                           
                                   
                                                                       
                                                                                         
                                                                                      
               
                                                                                      
              

                                                                             
                                                                                       
                                                                            
                                                                                    

                              
                                                             
                                                                    
                                            
                                                                                           
                                 
                                          
                                                                                      
                                                                                           
                          
                                                                                          
                                                                            
                              
                                  
                                                                                                

                                                                              
                                             

                                                                                            
                                                                          
                                              
                                                        
                                                                                

                                          
                                                                 
                                                                                     
                                                
                                       
                                                        
                                                                          
            
                                                         
        
                                                                                    
                                                         
                                                           
                                                                             
                                                                
                                                             
                                                       
                                                                   
                                              

                                                                           
                                                                            
                                       
                                                     
                                                       
         
                                                                                 
           
                                                                                
                                                    

                                                   
                                                                    
                                       
                                                                     
                                   
                                                                                     
                             
                                     
           
                                                                      
                             
                                               
                                       
                         
                                               
                            
                                

                                                           
                                                    
                                           
                                                  
                                                                              
           
                                                          
                                                                               
                                
                                                                
                                                
                                                                                     
                                              
                                                                      
                                                                                                         
                                                    
                                               
                                                                                  
                                                        
                                                                        
                                                                                                                
                                                          
                          
                                                                                                                                        
                                                
                                                                               
                                                          
           
        
                                                                                               
                               
                                                                    
                                                         
                                                       
                                      
            
                                                                                
                  
                                                        
                                                     
                                                                               
                
                                
                                                 
                                                                                             
                                                                 
                                                                                        
                
                                                                              
                                                                             
                                                           
                                                                        
          

                                       
                                                   
                                                              
                                                                 
                                          
                                                                                 
                                                                                 
                            
          

                                          
                                  
                                                                      
                                                  
                    
                                                                                    
                                                    
                                            
            
      
                                                                               
                                                                                
                                                                                          
                       
          
                                                    
                                                                         
               
                                                                         
          

                                                                                     
                                                               
      
                                                         
            
                                              
                                                 
                                                 
            
                                                        
                                                  

                                                                  
                                                                
                                                   
                                                           
                                                                       
                                                                        
                                                          
      
                                                                  
                                       
                                   
                                                                        
                                                                                
                                                
                                                 
                                              
                                                  
                                                                                    
                                                                       
                                                                    
                                                                                             
          
                                                           
                                             
                                                                   
                                                                                                     

                                                                  
                                                               
                                                                     
                                                    
                                                     
                                                                        
                                     
           
                                                                      
                             
                                                            

                                            
                                                                     
                                       
                                                    
                                                           
      
                                                 
                                                                 

                                                                            
                                                                              
                                                                   
                     
                           
                                    
                                  
                                                                                    
             
                                               
                                                               

                                                             
                                                                                                  
                                       
                                                                              
                                                                                     
                             
                                     
           
                                                      
                                                

                                                        
                                                                                  
                                                        
      
                                                                    
                                        
                                   
                                                                        
                                                                            
                                                                                
                                                                     
                                                             
               
                                                                                                   
               

                                                       
                                                                                    
                                                                                  
                                                                                     
                                                                                
                                                                     
                                           
                                                                                           
                                              
        
                                                              
                                                
         
                                                                                      
                                                        
                                                               
                   
         
         

def chiRowDim (n i : ℕ) : ℕ := max 1 (n - i)

abbrev ChiRows (n : ℕ) := (i : ℕ) → (Fin (chiRowDim n i) → ℝ)

def chiRowLaw (n : ℕ) : Measure (ChiRows n) :=
  Measure.infinitePi (fun i => standardGaussianProduct (chiRowDim n i))

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

                                                   
                                                                                                 

                                                                              
                                                                        

                                                                                            
                                                                               

                                            
                                          
                                                                    
                                                                                 
                             
                                       
                                                                            
                                                
                                              
                                                               
                                                                                   
                                           

                                                                                        
                                                                
                                                                       
                                                                            
                                                 
                                                                  
                                        
           
                                                    
                
                                                           
      

                                                 
                                              

                                          
                                        
                                                                              
                                                                            
                                   
         
                       
                    
         
                         
                                                            
                                                                         
                                                                 
      

                                                                                     
                                                                             
                                                 

                                                                          
                                             

                                                                                    
                                                                             
                                                        

def diagonalMarginal (n _i : ℕ) : Measure ℝ :=
  gaussianReal 0 ⟨2 / (n + 1), by positivity⟩

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

def diagonalLaw (n : ℕ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (diagonalMarginal n)

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

                                                                                         
                                                                  
                                                   
      

                                          
                                                                                               
                                                            
                                                
                                                                                 
                                                          
                                                                                 
                                          

                                        
                                                           
                                               

                                                                       
                                                                          
                                                                                       
                                           
           
                                                                        
                                

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

                                                       
                                                               
                                                                           
                                                            
                                      
                                                                
                                       
                                                       
                                                          
           
                                         
                                                                 
                
                                                          
                                                                                     
                                                                            
         
                                 
                                   
         
                                                               
                                                                    
            
                                 
          
                                                               
                                     
                                                                           
                                               
         
                          
         
                              
                                                              

                                                             
                                                               
                                             
                                              
                                             
                                                                                           
                                                      
                                                     
                                                                    
                                                                              
                                                                       
                                                                            
                                                                   
                                                                       
            
                                               
                                                                                     
            
                                                                                            
                                           
                                                                                        
                                                        
                                                       
                                                                            
                                       
                 
                                      
                                                               
                                       
                   
          
                    

                                                               
                                                               
                                             
                                    
                                    
                                                                 
                                                             
                                                                      
                                                                                  
                                          
                                                                               
                                                                        
                                                    
                                                           
                                                                                    
                                                                   
                                 
                                        
                                                        
                                        
                                                                               
                         
                                                                        
                                                                                     
                                 
                                                    
                                                      
                                                               
                          
                                  
                                                                   
                                                    
                                                                                          
                                                            
                                                                    
      
                                                                      
                                                                                
                                                  

                                                        
                                                               
                                             
                                                 
                                  
                                                                 
                                                       
                              
                                            
                                                                
                                                           
                   
         
            
      

                                                            
                                                               
                                             
                                                 
                                  
                                                                   
                                                           
                                                                
                                                              
                                                                               
                                                                                    
                                                                       
                                                                        
                                                                                
                         
                                   
                             
                                                                          
                                                                           
                                            
                           
                           
          

                                                 
                                                               
                                             
                                                 
                                        
                                                                             
                                                           
                                                              
                                                       
                                                                    

                                                                     
                                                                         

                                                       
                                  
                                                                       
                    
            

                                                        
                                                               
                                             
                                                 
                               
                                                   
                                                      
                                                          
                                                            
                                                        
                              
                                       
                                            
                                                                            
                                                                           
              
        
                                                                                                                      
                                          

                                         
                                                     
                                                                                                     
                                               
                                                                                                    
                 
         

                                
                                                            
                                                           
                                                               
                                                    
                                                       
                                                                               
                                     
                                                      
                                                             
        
                                                                            
                                                                         
                                                      
                                                                                    
                                   
                                                             
                                                              
                 
                                                                                          
                        
                  
            
                                                                                                 
                             
      
                                                                                    
                                       
                                                                                       
                                                                          
                                                   
                                                               
                                                                             
                                   
                                                 
                                                     
                                                                        
                           
                                               
            
                                         
                                         
                    

                                     
                                 
                                                                   

                                 
                                                             
              
                             
             
                                                                                    
                                                                                   
                                                      
                                                                               
              
           
                                     
             
                                  
                                                                       
        
                                                                                    
                                                                              

                                   
                                     
                             
                                                   
                                              
                                                                                   
                                  
                                                 
                                   
                                                                                      
                                         
                                                                            
                                                                     
                                                                       
                         
                                                                                  

                                                                           
                           
                                                                     
                                

                                                       
                                
                                                                         
                                                  
                                                            

                                                                           
                                             
                                                   
                      
                            
         
                            
         
                            
         
                            
         
                            
         
                            
         
                                               
                            
         
                                     
                                                                                       

                                                         
                                                               
                                             
                                                 
                                   
                                                                     
                                                                     
                                  
                                                                  
                                                               
                                                      
                                                                                               

                           
                                                                  
                                                                  
                                         
                                            
                                                             
                                          
                                              
                                              
                 
          
                                                              
                                                                                             

                           
                                                                      
                                                                  
                                                                                            
                                                                                              
                
                 
          
                                                              
                                                                                            

end

                                                      
                                     
                                         
                                                                                         
                  
                
                
                                  
                                     
        

                                                        
                                                  
                                                              
                                             
                                                       
                                                           
                                                      
      
                             
                                                                  
                                   
                                                         
                             
                
                                      
                                                                                        
                      
                                     

                                                                          
                                                              
                                             
                                                         
                                                             
                                                            
                                            
                                       
               
                               
                                                           
                                                         
                                                 
                                                                                         
                                                             
           
               
             
              
        
                                                                                        
           
                                                                           
                                              
                                                                   
          
                                                                                     
                                                                                     
                              
                                                                            
             
                                             
                                                                
                                                      
                                               
                                                             
                                                 
                              
             
        
          
                                                  
              
                                                                                      

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

instance (m : ℕ) : IsProbabilityMeasure (standardGaussianProduct m) := by
  unfold standardGaussianProduct
  infer_instance

instance (n : ℕ) : IsProbabilityMeasure (chiRowLaw n) := by
  unfold chiRowLaw
  infer_instance

instance (n i : ℕ) : IsProbabilityMeasure (diagonalMarginal n i) := by
  exact instIsProbabilityMeasureGaussianReal _ _

instance (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance

end CriticalSK

end

end OAI
