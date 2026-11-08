module

public import GinibrePoincare.Analysis.GinibreWeightedRadialInteriorMollification
public import GinibrePoincare.Analysis.RadialSobolevSpace

@[expose] public section

/-! # Smooth radial core approximation of interior weak-Sobolev pairs

Actual weak functions with compact radial symmetric representatives, and compact
weak-gradient representatives, supported away from collisions admit simultaneous
weighted smooth radial core approximation. This proves reverse inclusion and the
sharp LSI for that interior class, without assuming the initial value smooth.
-/

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section

variable (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | CollisionFree z}) (hhs : tsupport h ⊆ {z | CollisionFree z})
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))

include hn u g hg hf hh hfc hhc hfs hhs hs hr

                                                                               
                                                                   
                                                   
                                         
                                                                 
                                                                              
                                                                         
                                         
                                                                                    
                                                 
                                      
         
                                                          
                                                              
                               

                                                                                   
                                                                                       
                                                                 
                                               
                                          
                                                             

                                                                                  
                                                                           
                                  
                                                                           
                                                           
                                
                                                                                         

end
end GinibrePoincare
