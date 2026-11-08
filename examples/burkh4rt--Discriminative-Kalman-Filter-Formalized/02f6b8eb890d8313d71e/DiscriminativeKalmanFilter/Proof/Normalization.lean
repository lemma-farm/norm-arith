module
public import DiscriminativeKalmanFilter.Proof.KernelTools

@[expose] public section

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof
variable {d : ℕ}

theorem l1Norm_eq_integral {f : Density d} (hi : Integrable f volume)
    (hn : ∀ᵐ z ∂volume, 0 ≤ f z) :
    l1Norm f = ENNReal.ofReal (∫ z, f z ∂volume) := by
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  apply lintegral_congr_ae
  filter_upwards [hn] with z hz
  rw [abs_of_nonneg hz]

                                                                   
                                                      
                                                                   
                                                
                                                          
                                       
           
                                                             
                                             
                                                                          
                             
           
                                   
           
                               
            
                                            
                                           

end DiscriminativeKalmanFilter.Proof
