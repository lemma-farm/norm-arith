module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/TensorBundle/MusicalIso.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream package-option restoration, and pinned API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Mathlib
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.TensorBundle.SmoothOrthoFrame

@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain the upstream independent metric binders rather than changing theorem contracts.
set_option linter.overlappingInstances false


/-!
# Smoothness of the musical isomorphism

For a smooth Riemannian metric $g$, the musical isomorphism
$\sharp_g : T^*M \to TM$ at $x$ sends $\varphi \in T_x^*M$ to the unique
tangent vector $V$ with $g_x(V, W) = \varphi(W)$ for all $W$. This is
`g.metricRiesz x φ` in DoCarmoLib.

This file establishes smoothness of $x \mapsto \sharp_g\,\varphi(x)$ via
the chart-local representation
$$\sharp_g\,\varphi(x) = \sum_{i,j} G^{ij}(x)\,\varphi_j(x)\,e_i(x),$$
where $e_i$ is the chart-basis frame, $G_{ij} = g_x(e_i, e_j)$ is the
chart Gram matrix, and $G^{ij}$ is its entrywise inverse. The Gram matrix
is symmetric positive-definite on the trivialization base set, so its
determinant is strictly positive and its inverse is smooth via the
cofactor / adjugate formula.

**Ground truth**: do Carmo §3 ex. 8 (Riesz duality); Lee 2018 §13
(musical isomorphisms). The chart-Gram-matrix machinery is ported from
the `differential-geometry` external library (`Integral/Measure/ChartDensity`,
`Geometry/Gradient`).
-/

noncomputable section


open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Stage 1: the chart Gram matrix -/

/-- **Math.** The Gram matrix of the chart-basis family
`chartBasisVecFiber α · x` at $x$ under the inner product `g.inner x`. -/
def chartGramMatrix (g : RiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner x
      (chartBasisVecFiber (I := I) α i x)
      (chartBasisVecFiber (I := I) α j x)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartGramMatrix_apply
    (g : RiemannianMetric I M) (α : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) g α x i j =
      g.inner x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The Gram matrix is Hermitian (symmetric, real entries). -/
lemma chartGramMatrix_isHermitian
    (g : RiemannianMetric I M) (α : M) (x : M) :
    (chartGramMatrix (I := I) g α x).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (chartGramMatrix (I := I) g α x j i)
    = chartGramMatrix (I := I) g α x i j
  rw [chartGramMatrix_apply, chartGramMatrix_apply, star_trivial]
  exact g.symm x
    (chartBasisVecFiber (I := I) α j x)
    (chartBasisVecFiber (I := I) α i x)

/-! ## Stage 2: positive-definiteness on the base set -/

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The Gram-matrix quadratic form equals the metric-inner-product
squared norm of the corresponding linear combination of chart-basis vectors. -/
lemma chartGramMatrix_dotProduct_mulVec
    (g : RiemannianMetric I M) (α : M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    star c ⬝ᵥ (chartGramMatrix (I := I) g α x) *ᵥ c =
      g.inner x
        (∑ i, c i • chartBasisVecFiber (I := I) α i x)
        (∑ j, c j • chartBasisVecFiber (I := I) α j x) := by
  have hexpand :
      g.inner x
          (∑ i, c i • chartBasisVecFiber (I := I) α i x)
          (∑ j, c j • chartBasisVecFiber (I := I) α j x)
        = ∑ i, ∑ j, (c i * c j) *
            g.inner x
              (chartBasisVecFiber (I := I) α i x)
              (chartBasisVecFiber (I := I) α j x) := by
    have hL :
        g.inner x (∑ i, c i • chartBasisVecFiber (I := I) α i x)
          = ∑ i, c i • g.inner x (chartBasisVecFiber (I := I) α i x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
    rw [hL, sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [smul_apply]
    have hR :
        g.inner x (chartBasisVecFiber (I := I) α i x)
            (∑ j, c j • chartBasisVecFiber (I := I) α j x)
          = ∑ j, c j *
              g.inner x
                (chartBasisVecFiber (I := I) α i x)
                (chartBasisVecFiber (I := I) α j x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand]
  simp only [dotProduct, Matrix.mulVec, chartGramMatrix_apply, Pi.star_apply,
    star_trivial]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The Gram matrix of the chart-basis family is positive-definite
on the trivialization base set. -/
lemma chartGramMatrix_posDef
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (chartGramMatrix (I := I) g α x).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (chartGramMatrix_isHermitian (I := I) g α x) ?_
  intro c hc
  set w : TangentSpace I x :=
    ∑ i, c i • chartBasisVecFiber (I := I) α i x with hw_def
  have heq := chartGramMatrix_dotProduct_mulVec (I := I) g α x c
  rw [heq]
  have hwnz : w ≠ 0 := by
    intro hw0
    have hli := chartBasisFamily_linearIndependent (I := I) α hx
    rw [Fintype.linearIndependent_iff] at hli
    have : c = 0 := funext (hli c hw0)
    exact hc this
  exact g.pos x w hwnz

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The determinant of the Gram matrix is strictly positive on
the trivialization base set. -/
lemma chartGramMatrix_det_pos
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    0 < (chartGramMatrix (I := I) g α x).det :=
  (chartGramMatrix_posDef (I := I) g α hx).det_pos

/-! ## Stage 3: smoothness of Gram-matrix entries -/

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** Each Gram-matrix entry is smooth on the trivialization base set,
via `ContMDiffOn.clm_bundle_apply₂` on `g.contMDiff` and two `chartBasisVec`. -/
lemma chartGramMatrix_entry_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (g.inner b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    g.contMDiff.contMDiffOn
  have hv := chartBasisVec_contMDiffOn (I := I) α i
  have hw := chartBasisVec_contMDiffOn (I := I) α j
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            g.inner m
              (chartBasisVecFiber (I := I) α i m)
              (chartBasisVecFiber (I := I) α j m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hv hw
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** The determinant of the Gram matrix is smooth on the
trivialization base set. Expands `Matrix.det` as a finite sum of
finite products and chains entry smoothness. -/
lemma chartGramMatrix_det_contMDiffOn
    (g : RiemannianMetric I M) (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => (chartGramMatrix (I := I) g α x).det)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun x : M => (chartGramMatrix (I := I) g α x).det)
        = (fun x : M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ i, chartGramMatrix (I := I) g α x (σ i) i) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finsetSum (fun σ _ => ?_)
  refine ContMDiffOn.mul
    (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finsetProd (fun i _ => ?_)
  exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ i) i

/-! ## Stage 4: smoothness of the adjugate entries -/

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** Each adjugate entry of the Gram matrix is smooth on the
trivialization base set: a polynomial in the smooth Gram-matrix entries
via `Matrix.adjugate_apply` + `updateRow`. -/
lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j) =
        (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
          (Pi.single i (1 : ℝ))).det) := by
    funext x
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp2 :
      (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
          (Pi.single i (1 : ℝ))).det) =
        (fun x : M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ k, (chartGramMatrix (I := I) g α x).updateRow j
                (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finsetSum (fun σ _ => ?_)
  refine ContMDiffOn.mul
    (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finsetProd (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq :
        (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
            (Pi.single i (1 : ℝ)) (σ k) k) =
          (fun _ : M => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ)
            i (1 : ℝ)) k) := by
      funext x
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq :
        (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
            (Pi.single i (1 : ℝ)) (σ k) k) =
          (fun x : M => chartGramMatrix (I := I) g α x (σ k) k) := by
      funext x
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

/-! ## Stage 5: the inverse Gram matrix and its smoothness -/

/-- **Math.** The inverse Gram matrix at $(\alpha, x)$. On the chart base
set, the matrix inverse of the (positive-definite) Gram matrix. -/
def chartInvGramMatrix (g : RiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (chartGramMatrix (I := I) g α x)⁻¹

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** On the chart base set, the inverse Gram matrix is a one-sided inverse. -/
lemma chartInvGramMatrix_mul_chartGramMatrix
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartInvGramMatrix (I := I) g α x * chartGramMatrix (I := I) g α x = 1 := by
  have hpos := chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.nonsing_inv_mul _ hdet_unit

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Symmetric form: Gram · inverse Gram = 1 on the base set. -/
lemma chartGramMatrix_mul_chartInvGramMatrix
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartGramMatrix (I := I) g α x * chartInvGramMatrix (I := I) g α x = 1 := by
  have hpos := chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.mul_nonsing_inv _ hdet_unit

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** Each entry of the inverse Gram matrix is smooth on the chart
base set, via the cofactor / adjugate formula. -/
lemma chartInvGramMatrix_entry_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hcongr : ∀ x ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartInvGramMatrix (I := I) g α x i j =
        ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j := by
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 :=
      ne_of_gt hdet_pos
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) g α x).det •
            (chartGramMatrix (I := I) g α x).adjugate) i j =
      ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_ ?_
  · have hdet_smooth :
        ContMDiffOn I 𝓘(ℝ) ∞
          (fun x : M => (chartGramMatrix (I := I) g α x).det)
          (trivializationAt E (TangentSpace I) α).baseSet :=
      chartGramMatrix_det_contMDiffOn (I := I) g α
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 :=
      ne_of_gt hdet_pos
    have hsmooth_inv : ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹)
        (chartGramMatrix (I := I) g α x).det := contDiffAt_inv _ hdet_ne
    have h_at := hdet_smooth x hx
    exact hsmooth_inv.contMDiffAt.comp_contMDiffWithinAt x h_at
  · exact chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j

/-! ## Stage 6: chart-coordinate expression of the Riesz dual

At any base-set point $x$, the Riesz dual of a covector $\varphi$ admits the
explicit chart-frame expression
$$\sharp_g\,\varphi(x) = \sum_i \Bigl(\sum_j G^{ij}(x)\,\varphi(e_j(x))\Bigr)\,
    e_i(x),$$
derived by `g.metricRiesz_unique` against the bilinear-form action on the
chart frame.

This is the algebraic heart of the smoothness argument: every quantity on
the right-hand side is smooth on the base set (Gram-matrix inverse entries
via Stage 5, chart-basis vectors via `SmoothOrthoFrame`, and the covector
section by hypothesis), so the LHS is smooth too. -/

                                                             
                                            
                                              
                                                              
                                  
                                    
             
                                                           
                                                        
                                              
                                           
                                                   
                                                             
                    
                                                           
                                                        
                                              
                                                            
                                                        
                                                                  
                                                                           
                  
                                                                         
                     
                                                      
                                                    
                                                            
                                                 
                                                       
                                                      
                                                    
             
                                  
         
                                                  
                                                          
                        
                                                     
                                                    
                                            
                                                          
                                                       
                                                      
             
                         
                                                     
                                                      
                        
                                                      
                     
                                                     
                                                   
                                             
                                                      
                                                      
                                                       
             
                         
                                    
               
          
                                                  
                                                        
                                                                   
                      
                                            
                                               
                                                
                                                       
               
                                                                    
                                      
               
                   
                                                  
                                                  
                                                  
                                                     
             
                                                            
                                                
                                                     
                                                      
                                                  
               
                                                                         
                     
                                           
                                                    
                                                    
                                                       
                 
                     
         
                                                        
                                                          
                               
                                
                   
                                                   
                                                        
                                         
                         
              
                                         
                                                             
                
                                  
             
                 

                                                             
                                                                                     
                                      
                                              
                                                              
                                    
                       
                                                        
                                                      
                                               
      
                            
         
                                                                
               
                
                                                             
                                                          
                                                  
                                   
                                              
                                              
           
                                               
                                                            
                                                                     
                                
            

                                                                               

                                                             
                                                                                 
                                                                     
                                                               
                              
                                                                          
                                                      

                                          
                                                                      
                                                                      
                                                                          
                                                            
                                              
                                      
                                            
                                         
                            
                                                            
                                                            
                                    
                                      
                                                           
                                                          
                                             
                                                           
           
                                                                  
                       
                                                   
                                              
                          
                                                              
                                                            
           
                                                
                                                                            
                                                                      
                                                                  
                                                                      
                                                              
                                  
                                                      
                                                                   
                                                                    
             
                         
               
                                                            
                                                          
                                                 
                                                            
                                                      
                                           
              
                                                                               
                                                                                  
                     
                                             
                                                                     
             
                                                                   
                               
                   
                                                                              
                                                      
                                  
             
                                                       
           
                                                         
                                                            
                    
                             
                                                                    
                                                      
                                              
                                                
                                                                               
                                                    

                                                             
                                                                    
                                                                        
                                                                     
                                                                      
              
                                       
                                              
                                                              
                                            
                                         
                            
                                                            
                                                            
                                    
                                                                       
                     
                                                                     
                                                          
                                                                      
                                                         
                                                        
                                                                            
              
                                                             
            
                                      
                                                                 
                                                             
                               
              
                         
                                                    
          
                                                                  
                                                                        
                                                        
                                                  

                                                             
                                                                     
                                                                          
                                                                      
                                                                      
              
                                                 
                                              
                                                              
                                            
                                         
                                  
                                                            
                                                              
                                    
                                                                       
           
                                                                  
                       
                                            
                                                
                                                             
                                                 
                          
                                                              
                                                            
           
               
                                  
                                                                
                                                                
                                                        
                                                                                     
                                  
                                                                 
                                                                          
                                                                          
                         
               
                                                            
                                                          
                                                 
                                                            
                                                      
                                           
              
                                             
                                                                     
             
                                                                                   
                   
                                                      
                                  
             
                                                       
           
                                                         
                                                            
                                                                             
                       
                                      
                                        
                                                             
                                                            
                                                         
                                                           
                  
                               
                                                                      
                                                        
                                                
                                                  
                                                                                    
                                           
                                      
                      
                                                                
                                                
                                    
                                                  
                                                          


end Tensor
end Riemannian

end
