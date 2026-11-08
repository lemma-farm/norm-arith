module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Field.GeomSum

/-!
# The analytic large sieve inequality

Lab proof, unit U-5000. AI wrote this file. Known mathematics, a weak constant form of the
large sieve of Linnik, Renyi, Roth, Bombieri, Davenport and Halberstam. No cited input.

For points `α r`, `r ∈ s`, pairwise at distance at least `δ` modulo one, and any complex
`a n` on `M < n ≤ M + N`,

  `∑ r, ‖∑ n, a n e(n α r)‖² ≤ (N + 2/δ) ∑ n, ‖a n‖²`.

The proof is the dual form with a Fejer type majorant: average the interval sum over `L`
shifts of a longer interval, so the kernel is a product of two geometric sums, each at most
`1/(2‖θ‖)`; then sum `1/‖θ‖²` over the spaced points by an injective floor map. The sharp
constant `N - 1 + 1/δ` is not needed for Bombieri-Vinogradov type uses.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Complex Finset Real

/-- `e x = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (I * ((2 * π * x : ℝ) : ℂ))

/-- Distance from `x` to the nearest integer. -/
noncomputable def dist0 (x : ℝ) : ℝ := |x - round x|

lemma dist0_nonneg (x : ℝ) : 0 ≤ dist0 x := abs_nonneg _

                                                                

lemma dist0_le_abs_sub_int (x : ℝ) (z : ℤ) : dist0 x ≤ |x - z| := round_le x z

lemma dist0_neg (x : ℝ) : dist0 (-x) = dist0 x := by
  apply le_antisymm
  · have := dist0_le_abs_sub_int (-x) (-round x)
    rw [show (-x - ((-round x : ℤ) : ℝ)) = -(x - round x) by push_cast; ring, abs_neg] at this
    exact this
  · have := dist0_le_abs_sub_int x (-round (-x))
    rw [show (x - ((-round (-x) : ℤ) : ℝ)) = -(-x - round (-x)) by push_cast; ring,
      abs_neg] at this
    exact this

                                                                    
                           

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

                                     

lemma e_neg (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  unfold e
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

lemma e_int (z : ℤ) : e z = 1 := by
  unfold e
  rw [show I * ((2 * π * (z : ℝ) : ℝ) : ℂ) = (z : ℂ) * (2 * π * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I z

lemma e_sub_round (x : ℝ) : e (x - round x) = e x := by
  rw [sub_eq_add_neg, e_add, show (-(round x : ℝ)) = ((-round x : ℤ) : ℝ) by push_cast; ring,
    e_int, mul_one]

lemma e_nat_mul (k : ℕ) (x : ℝ) : e (k * x) = e x ^ k := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `|sin(πt)| ≥ 2|t|` for `|t| ≤ 1/2`. -/
lemma two_abs_le_abs_sin {t : ℝ} (ht : |t| ≤ 1 / 2) : 2 * |t| ≤ |Real.sin (π * t)| := by
  have key : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 → 2 * u ≤ Real.sin (π * u) := by
    intro u hu0 hu1
    have h1 := Real.mul_le_sin (x := π * u) (by positivity) (by nlinarith [Real.pi_pos])
    have : 2 / π * (π * u) = 2 * u := by field_simp
    linarith
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact (key t h ht).trans (le_abs_self _)
  · rw [abs_of_neg h] at ht ⊢
    have := key (-t) (by linarith) ht
    rw [show π * -t = -(π * t) by ring, Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

lemma four_dist0_le (θ : ℝ) : 4 * dist0 θ ≤ ‖e θ - 1‖ := by
  rw [← e_sub_round]
  set t := θ - round θ with ht
  have hb : |t| ≤ 1 / 2 := abs_sub_round θ
  unfold e
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  have := two_abs_le_abs_sin hb
  rw [show 2 * π * t / 2 = π * t by ring]
  unfold dist0
  rw [← ht]
  linarith

/-- The geometric sum bound `|∑_{k<m} e(kθ)| ≤ 1/(2‖θ‖)`. -/
lemma norm_geom_le (m : ℕ) {θ : ℝ} (h : 0 < dist0 θ) :
    ‖∑ k ∈ range m, e (k * θ)‖ ≤ 1 / (2 * dist0 θ) := by
  have hpos : 0 < ‖e θ - 1‖ := lt_of_lt_of_le (by linarith) (four_dist0_le θ)
  have hne : e θ ≠ 1 := by
    intro h1; rw [h1, sub_self, norm_zero] at hpos; exact lt_irrefl _ hpos
  simp_rw [e_nat_mul]
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖e θ ^ m - 1‖ ≤ 2 := by
    calc ‖e θ ^ m - 1‖ ≤ ‖e θ ^ m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  calc ‖e θ ^ m - 1‖ / ‖e θ - 1‖ ≤ 2 / ‖e θ - 1‖ :=
        div_le_div_of_nonneg_right hnum hpos.le
    _ ≤ 2 / (4 * dist0 θ) := div_le_div_of_nonneg_left (by norm_num) (by linarith)
        (four_dist0_le θ)
    _ = 1 / (2 * dist0 θ) := by field_simp; ring

                                                                             
                                                                                
                             
                                                        
                                          
                                              
                                   
              
                                                                                       
                                                
              
                                                                     
                                 
                                 
                       
                 
                                 
                                                                        
                                                                        
                               
                                             
                               
                                             
                                                                      
                                        
                                           
                                                                 
            
                                                                                          
                    
              
                                                          
                                                              
                                                  
                                                        
                                                                                     
                                                             
                             
                                             
              
                
                                         
                                                             
                                                                                         
                                                                    
                                                    
                                
                                                                                   
                           
                                                         
                                                         
                
                            

                                                           
                                                                   
                                                    

                                                                  
                                                                                 
                                                           
                                                                  
                                                                    
                                                    
                                      
                                               
                
              
                                                                      
                                                                                   
                         
                                                                    
                        
                                                
                                               
                     
                  
             
        
                                                                       
                                                                                      
                       
                                                                         
         
                  
                             
                          
                                      
         
                           
                                                                   
                                                 
              
                    
                                                                                        
                       
                                                                                           
         
                  
                             
                             
                                          
                                   
                 
         
                           
                                                                    
                                                               
                                                 
              
                            
                                                    
                            

end LeanLab.PNTPort.LargeSieve
