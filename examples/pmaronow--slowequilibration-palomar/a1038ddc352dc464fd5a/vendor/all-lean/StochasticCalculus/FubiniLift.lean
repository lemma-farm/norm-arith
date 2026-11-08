/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

/-!
# The Fubini lift `L²(μ; L²(ν)) → L²(ν × μ)`

A square-integrable random variable `U` with values in `L²(ν)` should be the same thing as a
square-integrable function of two variables `(t, ω) ↦ U ω t`.  Choosing jointly measurable
representatives is delicate, so we construct the map as an isometry: on the simple tensors
`1_A • g` (the `L²(ν)`-valued indicator functions `indicatorConstLp`) it is
`(t, ω) ↦ g t · 1_A ω`, the Gram matrices of the two families agree (`inner_indicatorLp`,
`inner_tensorLp`), the simple tensors have dense span (`Lp.induction`), and
`LinearMap.extendOfNorm` extends along the dense map.

## Main definitions

* `StochasticCalculus.fubiniLift`: the linear isometry `Lp (Lp ℝ 2 ν) 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (ν.prod μ)`;
* `StochasticCalculus.tensorLp`: the simple tensor `(t, ω) ↦ g t · 1_A ω` in `L²(ν × μ)`.

## Main results

* `StochasticCalculus.fubiniLift_indicatorLp`: `fubiniLift (1_A • g) = tensorLp A g`;
* `StochasticCalculus.inner_fubiniLift`, `norm_fubiniLift`: the lift is an isometry;
* `StochasticCalculus.inner_fubiniLift_tensorLp`: the weak Fubini identity
  `⟪fubiniLift U, g ⊗ 1_A⟫ = ∫ ω in A, ⟪g, U ω⟫ ∂μ`;
* `StochasticCalculus.fubiniLift_smulLp`: on rank-one elements, `fubiniLift (G • g) = g ⊗ G`;
* `fubiniLift_surjective`, `fubiniEquiv`: for σ-finite measures the lift is onto, so
  `L²(μ; L²(ν)) ≃ L²(ν × μ)` isometrically.
-/

public section

open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace

universe u_1 u_2 u_3





namespace StochasticCalculus

section Generic

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
  [SFinite μ]

/-- Finite-measure measurable sets. -/
abbrev FiniteMeasurableSet (μ : Measure Ω) := {A : Set Ω // MeasurableSet A ∧ μ A ≠ ∞}

/-! ### Simple tensors -/

                                                                                    
                                                                 
                                                                                    
                                               
                                                    
                                                        
                                     
                                                                                   
                                                              
                       
                          
      

                                                                             
                                                                                            
                           

                                                                   
                                           
                                                      
                    

/-- The `L²(ν)`-valued indicator `1_A • g` in `L²(μ; L²(ν))`. -/
noncomputable def indicatorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) : Lp (Lp ℝ 2 ν) 2 μ :=
  indicatorConstLp 2 A.2.1 A.2.2 g

omit [SFinite μ] in
/-- Gram matrix of the `L²(ν)`-valued indicators: `⟪1_A • g, 1_{A'} • g'⟫ = μ (A ∩ A') ⟪g, g'⟫`. -/
theorem inner_indicatorLp (A A' : FiniteMeasurableSet μ) (g g' : Lp ℝ 2 ν) :
    ⟪indicatorLp A g, indicatorLp A' g'⟫_ℝ = μ.real (A.1 ∩ A'.1) * ⟪g, g'⟫_ℝ := by
  unfold indicatorLp
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ A.2.1 A.2.2 g,
    setIntegral_indicatorConstLp A.2.1 A'.2.1 A'.2.2, real_inner_smul_right, Set.inter_comm]

/-! ### The lift on formal combinations of simple tensors -/

/-- Formal combinations of simple tensors, realized in `L²(μ; L²(ν))`. -/
noncomputable def tensorStepToLp :
    (FiniteMeasurableSet μ × Lp ℝ 2 ν →₀ ℝ) →ₗ[ℝ] Lp (Lp ℝ 2 ν) 2 μ :=
  Finsupp.linearCombination ℝ fun x ↦ indicatorLp x.1 x.2

                                                                      
                                    
                                                                      
                                                      

omit [SFinite μ] in
theorem tensorStepToLp_single (x : FiniteMeasurableSet μ × Lp ℝ 2 ν) (c : ℝ) :
    tensorStepToLp (Finsupp.single x c) = c • indicatorLp x.1 x.2 :=
  Finsupp.linearCombination_single _ _ _

                                                                                
                                                                   
                                        

omit [SFinite μ] in
/-- Simple tensors have dense span in `L²(μ; L²(ν))`. -/
theorem denseRange_tensorStepToLp : DenseRange (tensorStepToLp (μ := μ) (ν := ν)) := by
  change Dense (Set.range tensorStepToLp)
  rw [← LinearMap.coe_range, tensorStepToLp, Finsupp.range_linearCombination,
    Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  intro f _
  refine Lp.induction ENNReal.ofNat_ne_top
    (fun f : Lp (Lp ℝ 2 ν) 2 μ ↦ f ∈ (Submodule.span ℝ (Set.range fun x :
      FiniteMeasurableSet μ × Lp ℝ 2 ν ↦ indicatorLp x.1 x.2)).topologicalClosure)
    ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(⟨s, hs, hμs.ne⟩, c), rfl⟩)
  · intro f g _ _ _ hf hg
    exact Submodule.add_mem _ hf hg
  · exact Submodule.isClosed_topologicalClosure _

variable [SFinite ν]

                                                                                        
                                                                         
                                                                            
                   
                                                                
                                                                                          
                               
                                                                              
                                            
                                                                  
            
                                                                              
                                                                                             
                                             
                                                                                
               
                               
                             
                                                              

                                                                              
                                                                                             
                                        
                                                                                
                                                                                   

                                                                           
                                                   
                                      
                                                                  
                                                        

                          

                                                                                  
                                                                            
                                              

                                                                                
                                                          
                                                     
                                                         

                                        
                                                                            
                                                      
                                                                    
                                                                                  

                                                
                                                     
                                                     
                                                
                                                                          
                                                                         
                                                                                         
             
                                                                  

                                                                              
                                 
                                                                  
                                                        

                                                                           
                                                                                      
                                             

                                                                                      

                                                                           
                                                  
                             

                                                                                 
                                                           
                                                         
                             
                          

                                                                                           
                                                       
                                                                                     
                    
                                                                    
                                                                                           
                                                                     

end Generic

/-! ### Rank-one elements

The lift of a rank-one element `ω ↦ G ω • g` of `L²(μ; L²(ν))` is the tensor `(t, ω) ↦ g t · G ω`;
this extends `fubiniLift_indicatorLp` from indicators to all of `L²(μ)` by `Lp.induction`. -/

section RankOne

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
  [SFinite μ]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rank-one element `ω ↦ G ω • e` of `L²(μ; E)`, as a continuous linear map in `G`. -/
noncomputable def smulLp (e : E) : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℝ e).compLpL 2 μ

omit [SFinite μ] in
theorem coeFn_smulLp (e : E) (G : Lp ℝ 2 μ) :
    (smulLp e G : Ω → E) =ᵐ[μ] fun ω ↦ G ω • e := by
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ e).coeFn_compLpL (p := 2) (μ := μ) G]
    with ω hω
  rw [smulLp, hω, ContinuousLinearMap.toSpanSingleton_apply]

omit [SFinite μ] in
theorem smulLp_indicatorConstLp (e : E) {A : Set Ω} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (c : ℝ) :
    smulLp e (indicatorConstLp 2 hA hμA c) = indicatorConstLp 2 hA hμA (c • e) := by
  apply Lp.ext
  filter_upwards [coeFn_smulLp e (indicatorConstLp 2 hA hμA c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := c • e)] with ω h1 h2 h3
  rw [h1, h2, h3]
  by_cases hω : ω ∈ A <;> simp [hω]

/-- The product `(t, ω) ↦ g t * G ω` is square integrable on the product. -/
theorem memLp_tensor' (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    MemLp (fun p : T × Ω ↦ g p.1 * G p.2) 2 (ν.prod μ) := by
  refine (memLp_two_iff_integrable_sq
    ((Lp.aestronglyMeasurable g).comp_fst.mul (Lp.aestronglyMeasurable G).comp_snd)).mpr ?_
  refine ((Lp.memLp g).integrable_sq.mul_prod (Lp.memLp G).integrable_sq).congr ?_
  filter_upwards with p
  simp only [Pi.mul_apply]
  ring

/-- The tensor `(t, ω) ↦ g t * G ω` in `L²(ν × μ)`. -/
noncomputable def tensor (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) : Lp ℝ 2 (ν.prod μ) :=
  (memLp_tensor' g G).toLp _

theorem coeFn_tensor (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    (tensor g G : T × Ω → ℝ) =ᵐ[ν.prod μ] fun p ↦ g p.1 * G p.2 :=
  MemLp.coeFn_toLp _

theorem tensor_add (g : Lp ℝ 2 ν) (G G' : Lp ℝ 2 μ) :
    tensor g (G + G') = tensor g G + tensor g G' := by
  apply Lp.ext
  have h5 : (fun p : T × Ω ↦ (G + G' : Lp ℝ 2 μ) p.2) =ᵐ[ν.prod μ]
      fun p ↦ G p.2 + G' p.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_add G G')
  filter_upwards [coeFn_tensor g (G + G'), coeFn_tensor g G, coeFn_tensor g G',
    Lp.coeFn_add (tensor g G) (tensor g G'), h5] with p h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5]
  ring

theorem tensor_smul (g : Lp ℝ 2 ν) (c : ℝ) (G : Lp ℝ 2 μ) :
    tensor g (c • G) = c • tensor g G := by
  apply Lp.ext
  have h5 : (fun p : T × Ω ↦ (c • G : Lp ℝ 2 μ) p.2) =ᵐ[ν.prod μ] fun p ↦ c * G p.2 := by
    have h : (c • (G : Ω → ℝ)) =ᵐ[μ] fun ω ↦ c * G ω :=
      Filter.Eventually.of_forall fun ω ↦ by simp
    exact Measure.quasiMeasurePreserving_snd.ae_eq_comp ((Lp.coeFn_smul c G).trans h)
  filter_upwards [coeFn_tensor g (c • G), coeFn_tensor g G, Lp.coeFn_smul c (tensor g G), h5]
    with p h1 h2 h3 h5
  rw [h1, h3, Pi.smul_apply, h2, h5, smul_eq_mul]
  ring

/-- Inner products of simple tensors factor into the two component inner products. -/
theorem inner_tensor [SFinite ν]
    (g g' : Lp ℝ 2 ν) (G G' : Lp ℝ 2 μ) :
    inner ℝ (tensor g G) (tensor g' G') = inner ℝ g g' * inner ℝ G G' := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  calc
    ∫ p, tensor g' G' p * tensor g G p ∂ν.prod μ =
        ∫ p, (g' p.1 * g p.1) * (G' p.2 * G p.2) ∂ν.prod μ := by
      apply integral_congr_ae
      filter_upwards [coeFn_tensor g G, coeFn_tensor g' G'] with p hfirst hsecond
      rw [hfirst, hsecond]
      ring
    _ = (∫ t, g' t * g t ∂ν) * ∫ w, G' w * G w ∂μ :=
      integral_prod_mul (fun t ↦ g' t * g t) (fun w ↦ G' w * G w)

/-- `‖g ⊗ G‖ = ‖g‖ * ‖G‖`. -/
theorem norm_tensor [SFinite ν] (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    ‖tensor g G‖ = ‖g‖ * ‖G‖ := by
  have h := inner_tensor g g G G
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    ← mul_pow] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h

/-- `G ↦ g ⊗ G` as a continuous linear map. -/
@[expose] noncomputable def tensorL [SFinite ν] (g : Lp ℝ 2 ν) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (ν.prod μ) :=
  LinearMap.mkContinuous
    { toFun := tensor g
      map_add' := tensor_add g
      map_smul' := tensor_smul g } ‖g‖ fun G ↦ by
      change ‖tensor g G‖ ≤ ‖g‖ * ‖G‖
      rw [norm_tensor]

theorem tensorL_apply [SFinite ν] (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    tensorL g G = tensor g G := rfl

                                                                              
                                                                     
                                              
                                          
                                                                        
                    
                                                                  
                                                               
                               
                
                                                           
                                                      
                                                   
                                                                              
                                                                                           
               
                                            
                                           
                                                 
                           
                                              
                                                                                               

end RankOne

/-! ### Surjectivity: the Fubini isomorphism

The range of the Fubini lift is closed and contains the indicators of all finite rectangles; a
Dynkin-system argument inside each finite rectangle, followed by exhaustion along the spanning
sets of the two σ-finite measures, shows that it contains the indicator of every finite-measure
set, hence everything (`Lp.induction`). -/

section Surj

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}

/-- Changing the set of an `indicatorConstLp` along an equality of sets. -/
theorem indicatorConstLp_congr_set {α E : Type*} [MeasurableSpace α] {m : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} {s t : Set α} (h : s = t) (hs : MeasurableSet s)
    (hms : m s ≠ ∞) (c : E) :
    indicatorConstLp p hs hms c = indicatorConstLp p (h ▸ hs) (h ▸ hms) c := by
  subst h
  rfl

variable [SFinite μ] [SFinite ν]

                                                                      
                                                                     
                                                            

                                                                                                    
                                                                          

                                                        
                                                                                            
                                                                    
                                                                               
                                         
                                                                     
                                                             
              
                                                                            
                                                      
                                                              
                                                 
                                                                                         
             
                                       
         
                                                                                      

/-- `‖X‖² = ∫ ‖X x‖²` in `L²(m; E)`. -/
theorem norm_sq_eq_integral_norm_sq {α E : Type*} [MeasurableSpace α] {m : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (X : Lp E 2 m) :
    ‖X‖ ^ 2 = ∫ x, ‖X x‖ ^ 2 ∂m := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  exact real_inner_self_eq_norm_sq _

/-- Pointwise: the indicator of a disjoint union minus a partial sum of indicators is the
indicator of the tail. -/
theorem indicator_iUnion_sub_sum {α : Type*} {f : ℕ → Set α} (hf : Pairwise (Disjoint on f))
    (c : ℝ) (N : ℕ) (x : α) :
    (⋃ i, f i).indicator (fun _ ↦ c) x - ∑ i ∈ Finset.range N, (f i).indicator (fun _ ↦ c) x =
      (⋃ i, ⋃ (_ : N ≤ i), f i).indicator (fun _ ↦ c) x := by
  by_cases hx : x ∈ ⋃ i, f i
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    have hj' : ∀ i, i ≠ j → x ∉ f i := fun i hi hx' ↦ Set.disjoint_left.mp (hf hi) hx' hj
    rw [Set.indicator_of_mem hx]
    by_cases hjN : N ≤ j
    · rw [Finset.sum_eq_zero fun i hi ↦ Set.indicator_of_notMem
        (hj' i (by rw [Finset.mem_range] at hi; omega)) _,
        Set.indicator_of_mem (Set.mem_iUnion₂.mpr ⟨j, hjN, hj⟩), sub_zero]
    · have hnot : x ∉ ⋃ i, ⋃ (_ : N ≤ i), f i := fun h ↦ by
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp h
        exact hj' i (by omega) hxi
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega))
        (fun i _ hi ↦ Set.indicator_of_notMem (hj' i hi) _), Set.indicator_of_mem hj,
        Set.indicator_of_notMem hnot, sub_self]
  · have hnot : ∀ i, x ∉ f i := fun i hi ↦ hx (Set.mem_iUnion.mpr ⟨i, hi⟩)
    have : x ∉ ⋃ i, ⋃ (_ : N ≤ i), f i := fun h ↦ by
      obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp h
      exact hnot i hxi
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this,
      Finset.sum_eq_zero fun i _ ↦ Set.indicator_of_notMem (hnot i) _, sub_zero]

/-- A closed subspace of `L²` containing the indicators of pairwise disjoint sets of finite total
measure contains the indicator of their union. -/
theorem indicatorConstLp_iUnion_mem {α : Type*} [MeasurableSpace α] {m : Measure α}
    {K : Submodule ℝ (Lp ℝ 2 m)} (hK : IsClosed (K : Set (Lp ℝ 2 m))) {f : ℕ → Set α}
    (hf : Pairwise (Disjoint on f)) (hfm : ∀ i, MeasurableSet (f i))
    (hU : m (⋃ i, f i) ≠ ∞) (c : ℝ)
    (hmem : ∀ i, indicatorConstLp 2 (hfm i)
      (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c ∈ K) :
    indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c ∈ K := by
  set S : ℕ → Lp ℝ 2 m := fun N ↦ ∑ i ∈ Finset.range N, indicatorConstLp 2 (hfm i)
    (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c with hS
  have hSK : ∀ N, S N ∈ K := fun N ↦ Submodule.sum_mem _ fun i _ ↦ hmem i
  -- the tails `⋃ i ≥ N, f i` have measure tending to zero
  set tail : ℕ → Set α := fun N ↦ ⋃ i, ⋃ (_ : N ≤ i), f i with htail
  have htail_meas : ∀ N, MeasurableSet (tail N) := fun N ↦
    MeasurableSet.iUnion fun i ↦ MeasurableSet.iUnion fun _ ↦ hfm i
  have htail_sub : ∀ N, tail N ⊆ ⋃ i, f i := fun N ↦
    Set.iUnion_subset fun i ↦ Set.iUnion_subset fun _ ↦ Set.subset_iUnion f i
  have htail_anti : Antitone tail := fun N M hNM ↦
    Set.iUnion_mono fun i ↦ Set.iUnion_mono' fun h ↦ ⟨hNM.trans h, le_rfl⟩
  have htail_inter : ⋂ N, tail N = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp (hx 0)
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hx (i + 1))
    exact Set.disjoint_left.mp (hf (by omega : i ≠ j)) hxi hxj
  have htail_tendsto : Tendsto (fun N ↦ m (tail N)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (fun N ↦ (htail_meas N).nullMeasurableSet) htail_anti
      ⟨0, ne_top_of_le_ne_top hU (measure_mono (htail_sub 0))⟩
    rwa [htail_inter, measure_empty] at this
  -- the difference between the indicator of the union and a partial sum is the tail indicator
  have hdiff : ∀ N, ∀ᵐ x ∂m, (indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c : α → ℝ) x -
      (S N : α → ℝ) x = (tail N).indicator (fun _ ↦ c) x := by
    intro N
    have hsum := Lp.coeFn_finsetSum (Finset.range N) fun i ↦ indicatorConstLp 2 (hfm i)
      (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c
    have hind : ∀ᵐ x ∂m, ∀ i : ℕ, (indicatorConstLp 2 (hfm i)
        (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c : α → ℝ) x =
          (f i).indicator (fun _ ↦ c) x :=
      ae_all_iff.2 fun i ↦ indicatorConstLp_coeFn
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.iUnion hfm)
      (hμs := hU) (c := c), hsum, hind] with x h1 h2 h3
    rw [h1, hS, h2, Finset.sum_apply]
    simp_rw [h3]
    exact indicator_iUnion_sub_sum hf c N x
  have hnorm : ∀ N, ‖indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N‖ ^ 2 =
      c ^ 2 * (m (tail N)).toReal := by
    intro N
    rw [norm_sq_eq_integral_norm_sq]
    calc ∫ x, ‖(indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N) x‖ ^ 2 ∂m
        = ∫ x, (tail N).indicator (fun _ ↦ c ^ 2) x ∂m := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_sub (indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c) (S N),
            hdiff N] with x h1 h2
          rw [h1, Pi.sub_apply, h2, Real.norm_eq_abs, sq_abs]
          by_cases hx : x ∈ tail N <;> simp [hx]
      _ = c ^ 2 * (m (tail N)).toReal := by
          rw [integral_indicator_const _ (htail_meas N), smul_eq_mul, mul_comm]
          rfl
  have hlim : Tendsto (fun N ↦ ‖indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N‖)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N ↦ (m (tail N)).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail_tendsto
      rw [ENNReal.toReal_zero] at this
      exact this
    have h2 : Tendsto (fun N ↦ ‖indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N‖ ^ 2)
        atTop (𝓝 0) := by
      simp_rw [hnorm]
      simpa using h1.const_mul (c ^ 2)
    have := h2.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have hS_tendsto : Tendsto S atTop (𝓝 (indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hlim
  exact hK.mem_of_tendsto hS_tendsto (Filter.Eventually.of_forall hSK)

                                                                                          
                                                                             
                                                                                           
                                                       
                                                  
                                                                    
                                                                                        
                                                                              
                                                                         
                                                                
                                           
                                                                                       
                                    
                                                      
           
                                                                               
                              
                                  
                                                                             
                                                                             
                                                                      
                                                                        
                     
                                                           
                                                                                    
                                                                           
                                                                                          
                                                                 
           
                                                                     
           
                                                  
                                                                         
                                                                     
                                          
                                                               
                                                                               
                                                                  
                                                                       
                                                                     
                                      
            
                                          
                         
                                                                   
                                                           
                                                                                           
                                                                 

variable [SigmaFinite μ] [SigmaFinite ν]

                                                              
                                                                                 
                                      
                                                                     
                                                                                 
                                                
                                                                          
                                           
                                                                             
                                          
              
                                                                        
                                                                                       
                                                                                       
                                                                 
                                                    
                                                        
                                                                        
                                                
                                                                                
                                                                           
                                                 
                                            
                                                    
                                                                
                                                                                     
                                   
         
                                                                                                 
                       
                                                                  
                         
                                                                       
                                                                                   
                                                                  
                                        
                                                               
                                                                                   
                                            
                                                                                         
                                         
           
                                                                                     
                                                              
                                                                                       
                  
               
                                                                                        
                                                                                        
                                                                             
                                             
           
                                    
                                                                                   
                                                                                              
                                                                  
                                 
                                                                    
                                                  
                                                                                         
                        
                                                             
                                             
                                                 
                                                                        
             
                                                                    
                                                                             
                                             
                                          
                                                                           
                                                                         
                                      
                
                                                                                
                                                                                                 
                         
                     
                                      
                   
                                                                    
                                        
                                                                                   

                                                                    
                                                                    
                 
           
                                                                                              
                          
                    
                                         
                                                      
                         
                                   

                                                                                                
                                             
                                                              
            

                                                             
                                                                                       
                                                                   

                                                                                       

end Surj

/-! ### Bounded multipliers

Multiplication by a bounded measurable function `G` of `ω` is a continuous linear map on
`L²(μ; E)`; the Fubini lift intertwines it with multiplication by `G ∘ snd` on `L²(ν × μ)`
(`fubiniLift_boundedSMul`). -/

section Multiplier

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- Multiplication by a bounded measurable scalar function, as a map on `L²(μ; E)`. -/
theorem memLp_boundedSMul {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) : MemLp (fun x ↦ G x • U x) 2 μ := by
  refine MemLp.of_le ((Lp.memLp U).norm.const_mul C) (hG.smul (Lp.aestronglyMeasurable U))
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
  rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs (C * ‖U x‖),
    abs_of_nonneg (mul_nonneg hC0 (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Multiplication by a bounded measurable scalar function as a linear map on `L²(μ; E)`. -/
@[expose] noncomputable def boundedSMulₗ {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) : Lp E 2 μ →ₗ[ℝ] Lp E 2 μ where
  toFun U := (memLp_boundedSMul hG hC U).toLp _
  map_add' U V := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_add U V] with x hx
    rw [hx, Pi.add_apply, Pi.add_apply, smul_add]
  map_smul' c U := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_smul c U] with x hx
    rw [hx, Pi.smul_apply, Pi.smul_apply, smul_comm]

theorem boundedSMulₗ_apply {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) :
    boundedSMulₗ hG hC U = (memLp_boundedSMul hG hC U).toLp _ := rfl

theorem norm_boundedSMulₗ_le {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) : ‖boundedSMulₗ hG hC U‖ ≤ C * ‖U‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_boundedSMul hG hC U)] with x hx
  rw [boundedSMulₗ_apply, hx, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Multiplication by a bounded measurable scalar function as a continuous linear map on
`L²(μ; E)`. -/
@[expose] noncomputable def boundedSMul {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  LinearMap.mkContinuous (boundedSMulₗ hG hC) C (norm_boundedSMulₗ_le hG hC)

theorem boundedSMul_apply {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) :
    boundedSMul hG hC U = (memLp_boundedSMul hG hC U).toLp _ := rfl

theorem norm_boundedSMul_le {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) : ‖boundedSMul hG hC U‖ ≤ C * ‖U‖ :=
  norm_boundedSMulₗ_le hG hC U

theorem coeFn_boundedSMul {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) :
    (boundedSMul hG hC U : Ω → E) =ᵐ[μ] fun x ↦ G x • U x :=
  MemLp.coeFn_toLp (memLp_boundedSMul hG hC U)

end Multiplier

section Compat

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
  [SFinite μ] [SFinite ν]

omit [SFinite ν] in
/-- A bounded measurable function of `ω`, viewed on `T × Ω`. -/
theorem aestronglyMeasurable_comp_snd {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) :
    AEStronglyMeasurable (fun p : T × Ω ↦ G p.2) (ν.prod μ) :=
  hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd

                                                                                 
                                                   
                                                                                  
                                                   
                                      
                                                                                                   
                                                                       
                                      
                                                                                              
              
                    
                                         
                                                                           
                                                                              
                                                    
                               
                                                                 
                                                                                 
                  
                                                                              
                                                                                  
                                                                       
                                                                            
                                                                                  
                             
                                          
                                       
                              
                
                                                                                              
                                                                                    
                                     
                                       
                                                   
                                                                         
                                                   
                                                                                    
                           
                   
                                            
                                         
                                                 
                         
                                                   
                                                                                 
                                                               

end Compat

end StochasticCalculus
