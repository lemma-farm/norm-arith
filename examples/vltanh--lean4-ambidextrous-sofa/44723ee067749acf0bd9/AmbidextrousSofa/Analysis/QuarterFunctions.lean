module

public import AmbidextrousSofa.Analysis.DirichletEnergy

@[expose] public section

/-!
# Pairs of continuously differentiable quarter-interval functions

These data record functions and their actual right derivatives. They impose
no convexity, support, maximization, area, or calibration conclusion. The
quarter interval is closed for continuity and open for differentiation, so
piecewise twice differentiable reference coordinates belong to this domain.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa.Analysis

structure QuarterPair where
  f : ℝ → ℝ
  g : ℝ → ℝ
  fD : ℝ → ℝ
  gD : ℝ → ℝ
  continuous_f : ContinuousOn f (Icc 0 (Real.pi / 2))
  continuous_g : ContinuousOn g (Icc 0 (Real.pi / 2))
  continuous_fD : ContinuousOn fD (Icc 0 (Real.pi / 2))
  continuous_gD : ContinuousOn gD (Icc 0 (Real.pi / 2))
  hasDeriv_f : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt f (fD t) (Ioi t) t
  hasDeriv_g : ∀ t ∈ Ioo 0 (Real.pi / 2), HasDerivWithinAt g (gD t) (Ioi t) t

                                                                          
                                                      
                                                                       

                                                                       
                                                        
                                 
                                                                                 

def QuarterPair.sub (p q : QuarterPair) : QuarterPair where
  f := fun t => p.f t - q.f t
  g := fun t => p.g t - q.g t
  fD := fun t => p.fD t - q.fD t
  gD := fun t => p.gD t - q.gD t
  continuous_f := p.continuous_f.sub q.continuous_f
  continuous_g := p.continuous_g.sub q.continuous_g
  continuous_fD := p.continuous_fD.sub q.continuous_fD
  continuous_gD := p.continuous_gD.sub q.continuous_gD
  hasDeriv_f := fun t ht => (p.hasDeriv_f t ht).sub (q.hasDeriv_f t ht)
  hasDeriv_g := fun t ht => (p.hasDeriv_g t ht).sub (q.hasDeriv_g t ht)

                                                                             
                           
                                                                                        

                                                                          
                                                                            
                                                           
                                                                   
                                                                   
                                                                        
                                                             
                                                                        
                                                             
                                                                             
                                                                             
                     
                                                                           
                                     
                     
                                                                           
                                     
                  
              
                                                                                
                                                                                
                                                                                     
                               
                  
              
                                                                                
                                                                                
                                                                                     
                               

                                                                           
                            
                                                      

                                                             
                                                                   
                                
                                                                             

                                                                       
                                                                    
                                                                     
                                         
                                                     
                                                             
                                               
                                
                                                                             
                                                                       

end AmbidextrousSofa.Analysis
