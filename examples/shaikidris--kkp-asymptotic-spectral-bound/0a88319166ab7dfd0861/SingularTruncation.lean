module
public import OrthogonalSplitting
public import BipartiteEnergy
@[expose] public section

/-!
# Right singular truncation

The retained right space is constructed from the spectral theorem for the
Gram matrix. This works for rectangular matrices, including empty dimensions.
All matrix norms in this module are Euclidean operator norms.
-/

namespace KKPAsymptotic
open Matrix Unitary
open scoped Classical Matrix.Norms.L2Operator
variable {H R : Type*} [Fintype H] [DecidableEq H] [Fintype R] [DecidableEq R]

/-- Diagonal functional calculus in the fixed orthonormal eigenbasis. -/
noncomputable def spectralMap {C : Matrix R R ℝ} (hC : C.IsHermitian)
    (f : ℝ → ℝ) : Matrix R R ℝ :=
  conjStarAlgAut ℝ (Matrix R R ℝ) hC.eigenvectorUnitary
    (diagonal (fun i => f (hC.eigenvalues i)))

theorem spectralMap_mul {C : Matrix R R ℝ} (hC : C.IsHermitian) (f g : ℝ → ℝ) :
    spectralMap hC f * spectralMap hC g = spectralMap hC (fun x => f x * g x) := by
  unfold spectralMap
  rw [← map_mul, diagonal_mul_diagonal]

theorem spectralMap_sub {C : Matrix R R ℝ} (hC : C.IsHermitian) (f g : ℝ → ℝ) :
    spectralMap hC f - spectralMap hC g = spectralMap hC (fun x => f x - g x) := by
  unfold spectralMap
  rw [← map_sub, ← diagonal_sub]

theorem spectralMap_one {C : Matrix R R ℝ} (hC : C.IsHermitian) :
    spectralMap hC (fun _ => 1) = 1 := by
  simp [spectralMap]

theorem spectralMap_id {C : Matrix R R ℝ} (hC : C.IsHermitian) :
    spectralMap hC id = C := by
  simpa [spectralMap, Function.comp_def] using hC.spectral_theorem.symm

theorem spectralMap_transpose {C : Matrix R R ℝ} (hC : C.IsHermitian) (f : ℝ → ℝ) :
    (spectralMap hC f)ᵀ = spectralMap hC f := by
  have h := Matrix.isHermitian_mul_mul_conjTranspose
    (hC.eigenvectorUnitary : Matrix R R ℝ)
    (isHermitian_diagonal (fun i => f (hC.eigenvalues i)))
  exact (isHermitian_iff_isSymm.mp (by
    simpa only [spectralMap, conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose] using h)).eq

theorem spectralMap_norm_le {C : Matrix R R ℝ} (hC : C.IsHermitian)
    (f : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ i, |f (hC.eigenvalues i)| ≤ c) : ‖spectralMap hC f‖ ≤ c := by
  simp only [spectralMap, conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hc).mpr (fun i => by simpa using hf i)

theorem spectralMap_trace {C : Matrix R R ℝ} (hC : C.IsHermitian) (f : ℝ → ℝ) :
    (spectralMap hC f).trace = ∑ i, f (hC.eigenvalues i) := spectralConjugate_trace _ _

omit [DecidableEq H] in
/-- The Euclidean operator norm is bounded by the Frobenius mass, for rectangular matrices. -/
theorem rectangular_opNorm_sq_le (B : Matrix H R ℝ) :
    ‖B‖ ^ 2 ≤ ∑ i : H, ∑ j : R, B i j ^ 2 := by
  let C := Bᴴ * B
  have hC : C.PosSemidef := posSemidef_conjTranspose_mul_self B
  have ht : C.trace = ∑ i : H, ∑ j : R, B i j ^ 2 := by
    simp only [C, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      conjTranspose_eq_transpose_of_trivial, transpose_apply, ← pow_two]
    exact Finset.sum_comm
  have hn : ‖C‖ ≤ C.trace := by
    conv_lhs => rw [← spectralMap_id hC.isHermitian]
    apply spectralMap_norm_le hC.isHermitian id hC.trace_nonneg
    intro i
    simp only [id_eq, abs_of_nonneg (hC.eigenvalues_nonneg i)]
    rw [hC.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hC.eigenvalues_nonneg j) (Finset.mem_univ i)
  change ‖Bᴴ * B‖ ≤ _ at hn
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, ht] at hn
  simpa only [pow_two] using hn

/-- The right spectral projection retaining singular values strictly above `a`. -/
noncomputable def rightCutProjection (B : Matrix H R ℝ) (a : ℝ) : Matrix R R ℝ :=
  spectralMap (isHermitian_conjTranspose_mul_self B)
    (fun x => if a ^ 2 < x then 1 else 0)

/-- The inverse Gram operator on the retained space and zero on its complement. -/
noncomputable def rightCutInverse (B : Matrix H R ℝ) (a : ℝ) : Matrix R R ℝ :=
  spectralMap (isHermitian_conjTranspose_mul_self B)
    (fun x => if a ^ 2 < x then x⁻¹ else 0)

omit [DecidableEq H] in
theorem rightCutProjection_transpose (B : Matrix H R ℝ) (a : ℝ) :
    (rightCutProjection B a)ᵀ = rightCutProjection B a := spectralMap_transpose _ _

                       
                                                           
                                                                                  
                                          
         
          
                        

                       
                                                               
                                      
                                           
         
                        

                       
                                                               
                                          
                                                               
                                        
                                           
         
                        

omit [DecidableEq H] in
/-- Retaining the right singular space does not increase the squared rectangular mass. -/
theorem rightCut_mass_le (B : Matrix H R ℝ) (a : ℝ) :
    (∑ i : H, ∑ j : R, (B * rightCutProjection B a) i j ^ 2) ≤
      ∑ i : H, ∑ j : R, B i j ^ 2 := by
  let hC := isHermitian_conjTranspose_mul_self B
  let P := rightCutProjection B a
  have htrace (T : Matrix H R ℝ) : (Tᵀ * T).trace =
      ∑ i : H, ∑ j : R, T i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, transpose_apply, ← pow_two]
    exact Finset.sum_comm
  rw [← htrace (B * P), ← htrace B]
  have hPt : Pᵀ = P := rightCutProjection_transpose B a
  have hspec : Bᵀ * B = spectralMap hC id := by
    simpa using (spectralMap_id hC).symm
  have hprod : (B * P)ᵀ * (B * P) =
      spectralMap hC (fun x => if a ^ 2 < x then x else 0) := by
    rw [transpose_mul, hPt]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᵀ B P, hspec]
    dsimp [P, rightCutProjection]
    rw [spectralMap_mul, spectralMap_mul]
    congr 2
    funext x
    split_ifs <;> simp
  rw [hprod, spectralMap_trace, hspec, spectralMap_trace]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · rfl
  · exact (posSemidef_conjTranspose_mul_self B).eigenvalues_nonneg i

omit [DecidableEq H] in
theorem gram_mul_rightCutInverse (B : Matrix H R ℝ) (a : ℝ) :
    Bᵀ * B * rightCutInverse B a = rightCutProjection B a := by
  have hC := isHermitian_conjTranspose_mul_self B
  have hspec : Bᵀ * B = spectralMap hC id := by
    simpa using (spectralMap_id hC).symm
  rw [hspec, rightCutInverse, spectralMap_mul, rightCutProjection]
  congr 2
  funext x
  by_cases hx : a ^ 2 < x
  · have hn : x ≠ 0 := ne_of_gt ((sq_nonneg a).trans_lt hx)
    simp [hx, hn]
  · simp [hx]

omit [DecidableEq H] in
/-- The discarded rectangular block has operator norm at most the singular cutoff. -/
theorem rightCut_discard_norm_le (B : Matrix H R ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ‖B * (1 - rightCutProjection B a)‖ ≤ a := by
  let hC := isHermitian_conjTranspose_mul_self B
  let P := rightCutProjection B a
  let Q := 1 - P
  have hQt : Qᵀ = Q := projection_complement_transpose (rightCutProjection_transpose B a)
  have hQspec : Q = spectralMap hC (fun x => if a ^ 2 < x then 0 else 1) := by
    dsimp [Q, P, rightCutProjection]
    rw [← spectralMap_one hC, spectralMap_sub]
    congr 2
    funext x
    split_ifs <;> norm_num
  have hspec : Bᵀ * B = spectralMap hC id := by
    simpa using (spectralMap_id hC).symm
  have hprod : (B * Q)ᴴ * (B * Q) =
      spectralMap hC (fun x => if a ^ 2 < x then 0 else x) := by
    have hQstar : Qᴴ = Q := by simpa using hQt
    rw [conjTranspose_mul, hQstar]
    simp only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᵀ B Q, hspec, hQspec,
      spectralMap_mul, spectralMap_mul]
    congr 2
    funext x
    split_ifs <;> simp
  have hn : ‖(B * Q)ᴴ * (B * Q)‖ ≤ a ^ 2 := by
    rw [hprod]
    apply spectralMap_norm_le hC _ (sq_nonneg a)
    intro i
    have hi := (posSemidef_conjTranspose_mul_self B).eigenvalues_nonneg i
    split_ifs with h
    · simp only [abs_zero]; exact sq_nonneg a
    · rw [abs_of_nonneg hi]
      exact le_of_not_gt h
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  change ‖B * Q‖ ≤ a
  nlinarith [norm_nonneg (B * Q)]

omit [DecidableEq H] in
/-- Retained inversion costs at most the reciprocal singular cutoff. -/
theorem rightCut_inverse_norm_le (B : Matrix H R ℝ) {a : ℝ} (ha : 0 < a) :
    ‖B * rightCutInverse B a‖ ≤ a⁻¹ := by
  let hC := isHermitian_conjTranspose_mul_self B
  let T := rightCutInverse B a
  have hTt : Tᵀ = T := spectralMap_transpose _ _
  have hspec : Bᵀ * B = spectralMap hC id := by
    simpa using (spectralMap_id hC).symm
  have hprod : (B * T)ᴴ * (B * T) =
      spectralMap hC (fun x => if a ^ 2 < x then x⁻¹ else 0) := by
    have hTstar : Tᴴ = T := by simpa using hTt
    rw [conjTranspose_mul, hTstar]
    simp only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᵀ B T, hspec]
    dsimp [T, rightCutInverse]
    rw [spectralMap_mul, spectralMap_mul]
    congr 2
    funext x
    by_cases hx : a ^ 2 < x
    · have hn : x ≠ 0 := ne_of_gt ((sq_nonneg a).trans_lt hx)
      simp [hx, hn]
    · simp [hx]
  have hn : ‖(B * T)ᴴ * (B * T)‖ ≤ (a⁻¹) ^ 2 := by
    rw [hprod]
    apply spectralMap_norm_le hC _ (sq_nonneg _)
    intro i
    split_ifs with h
    · have hp : 0 < hC.eigenvalues i := (sq_nonneg a).trans_lt h
      rw [abs_of_nonneg (inv_nonneg.mpr hp.le)]
      simpa only [inv_pow] using (inv_le_inv₀ hp (sq_pos_of_pos ha)).mpr h.le
    · simp only [abs_zero]; exact sq_nonneg _
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  change ‖B * T‖ ≤ a⁻¹
  nlinarith [norm_nonneg (B * T), inv_pos.mpr ha]

/-- Applying a residual operator to the retained right space gains one inverse cutoff. -/
theorem mul_rightCutProjection_norm_le (B : Matrix H R ℝ) (D : Matrix R R ℝ)
    {a : ℝ} (ha : 0 < a) :
    ‖D * rightCutProjection B a‖ ≤ ‖D * Bᵀ‖ / a := by
  rw [← gram_mul_rightCutInverse B a]
  have hfactor : D * (Bᵀ * B * rightCutInverse B a) =
      (D * Bᵀ) * (B * rightCutInverse B a) := by simp only [Matrix.mul_assoc]
  rw [hfactor]
  apply (Matrix.l2_opNorm_mul _ _).trans
  simpa [div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_left (rightCut_inverse_norm_le B ha) (norm_nonneg (D * Bᵀ)))

                                                                                       
                                                             
                                                   
                                          
                                            
             
                                                                                      
                                                       
                              
                                  

                                                                            
                                                                    
                                                   
                                          
                                            
                     
                                    
                                                       
           
                                             
                                                        
               
                                                       
                                                    
                                         
                                                         
                                                                                 
                                                    

end KKPAsymptotic
