module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.BrownianMotion.Gaussian.BrownianMotion
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SphericalAging.HardSphereDynamics
set_option autoImplicit false
public section
/-!
# Actual independent Brownian coordinate drivers

The probability space is a finite product of continuous path spaces. The
filtration records every coordinate up to the current time. Increment
independence from this complete vector past is proved from scalar Brownian
independence and product measures, rather than assumed as driving data.
-/
noncomputable section
open MeasureTheory ProbabilityTheory MeasurableSpace Filtration Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology
namespace SphericalAging.VectorBrownian
@[expose] abbrev Path := C(ℝ≥0, ℝ)
@[expose] def scalarPath (ω : ℝ≥0 → ℝ) : Path :=
  ⟨fun t => brownian t ω, continuous_brownian ω⟩
lemma scalarPath_measurable : Measurable scalarPath := by
  rw [ContinuousMap.measurable_iff_eval]
  exact measurable_brownian
/-- The continuous Brownian path law constructed in the staged foundations. -/
@[expose] def pathLaw : Measure Path := gaussianLimit.map scalarPath
lemma scalarPath_hasLaw : HasLaw scalarPath pathLaw gaussianLimit :=
  hasLaw_map scalarPath_measurable.aemeasurable
instance pathLaw_probability : IsProbabilityMeasure pathLaw :=
  scalarPath_hasLaw.isProbabilityMeasure_iff.mp inferInstance
lemma scalar_eval_measurable (t : ℝ≥0) : Measurable (fun ω : Path => ω t) :=
  (by fun_prop : Continuous (fun ω : Path => ω t)).measurable
@[expose] abbrev Space (N : ℕ) := Fin N → Path
@[expose] def law (N : ℕ) : Measure (Space N) := Measure.pi (fun _ => pathLaw)
instance law_probability (N : ℕ) : IsProbabilityMeasure (law N) := by
  unfold law
  infer_instance
@[expose] def coordinate {N : ℕ} (i : Fin N) (t : ℝ≥0) (ω : Space N) : ℝ := ω i t
@[expose] def process {N : ℕ} (t : ℝ≥0) (ω : Space N) : Fin N → ℝ := fun i => coordinate i t ω
lemma coordinate_measurable {N : ℕ} (i : Fin N) (t : ℝ≥0) :
    Measurable (coordinate i t) := (scalar_eval_measurable t).comp (measurable_pi_apply i)
lemma process_measurable (N : ℕ) (t : ℝ≥0) : Measurable (process (N := N) t) :=
  measurable_pi_iff.mpr (fun i => coordinate_measurable i t)
/-- Every coordinate history is observed by this filtration. -/
@[expose] def filtration (N : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Space N)) :=
  natural process (fun t => (process_measurable N t).stronglyMeasurable)
lemma paths_independent (N : ℕ) :
    iIndepFun (fun i (ω : Space N) => fun t => coordinate i t ω) (law N) := by
  exact iIndepFun_pi (fun _ => (measurable_pi_iff.mpr scalar_eval_measurable).aemeasurable)
lemma coordinate_stronglyAdapted {N : ℕ} (i : Fin N) :
    StronglyAdapted (filtration N) (coordinate i) := by
  intro t
  have h := stronglyAdapted_natural (fun s => (process_measurable N s).stronglyMeasurable) t
  exact ((measurable_pi_apply i).comp h.measurable).stronglyMeasurable
/-- Tensorization of independence: independent pairs in each coordinate give
independent first and second vectors on the finite product probability space. -/
lemma product_vectors_independent {ι Ω A B : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : ι → Ω → A) (Y : ι → Ω → B)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXY : ∀ i, IndepFun (X i) (Y i) (μ i)) :
    IndepFun (fun ω i => X i (ω i)) (fun ω i => Y i (ω i)) (Measure.pi μ) := by
  let ν : ι → Measure A := fun i => (μ i).map (X i)
  let ξ : ι → Measure B := fun i => (μ i).map (Y i)
  have hν : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (hasLaw_map (hX i).aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hξ : ∀ i, IsProbabilityMeasure (ξ i) := fun i =>
    (hasLaw_map (hY i).aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hpair : ∀ i, IsProbabilityMeasure ((μ i).map (fun ω => (X i ω, Y i ω))) := fun i =>
    (hasLaw_map ((hX i).prodMk (hY i)).aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hVX : Measurable (fun (ω : ι → Ω) i => X i (ω i)) :=
    measurable_pi_iff.mpr (fun i => (hX i).comp (measurable_pi_apply i))
  have hVY : Measurable (fun (ω : ι → Ω) i => Y i (ω i)) :=
    measurable_pi_iff.mpr (fun i => (hY i).comp (measurable_pi_apply i))
  have hVP : Measurable (fun (ω : ι → Ω) i => (X i (ω i), Y i (ω i))) :=
    measurable_pi_iff.mpr (fun i => ((hX i).prodMk (hY i)).comp (measurable_pi_apply i))
  have hpairs : (Measure.pi μ).map (fun ω i => (X i (ω i), Y i (ω i))) =
      Measure.pi (fun i => (ν i).prod (ξ i)) := by
    rw [Measure.pi_map_pi (fun i => ((hX i).prodMk (hY i)).aemeasurable)]
    congr 1
    funext i
    exact (hXY i).map_prod_eq_prod_map_map (hX i).aemeasurable (hY i).aemeasurable
  rw [indepFun_iff_map_prod_eq_prod_map_map hVX.aemeasurable hVY.aemeasurable,
    Measure.pi_map_pi (fun i => (hX i).aemeasurable),
    Measure.pi_map_pi (fun i => (hY i).aemeasurable)]
  calc
    _ = ((Measure.pi μ).map (fun ω i => (X i (ω i), Y i (ω i)))).map
        (MeasurableEquiv.arrowProdEquivProdArrow A B ι) := by
      rw [Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow A B ι).measurable hVP]
      rfl
    _ = (Measure.pi (fun i => (ν i).prod (ξ i))).map
        (MeasurableEquiv.arrowProdEquivProdArrow A B ι) := by rw [hpairs]
    _ = (Measure.pi ν).prod (Measure.pi ξ) :=
      (measurePreserving_arrowProdEquivProdArrow A B ι ν ξ).map_eq
/-- An independent background can be revealed at time zero without changing
increment independence: a future variable remains independent of background
and the old past jointly. -/
lemma independent_background_and_past {A Ω X Y : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure A) (μ : Measure Ω) [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (f : Ω → X) (g : Ω → Y) (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g μ) :
    IndepFun (fun ω : A × Ω => f ω.2) (fun ω : A × Ω => (ω.1, g ω.2)) (ρ.prod μ) := by
  let ν := μ.map f
  let ξ := μ.map g
  have hν : IsProbabilityMeasure ν := (hasLaw_map hf.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hξ : IsProbabilityMeasure ξ := (hasLaw_map hg.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hbase : HasLaw (fun ω : A × Ω => (ω.1, (f ω.2, g ω.2)))
      (ρ.prod (ν.prod ξ)) (ρ.prod μ) := by
    refine ⟨(measurable_fst.prodMk ((hf.comp measurable_snd).prodMk
      (hg.comp measurable_snd))).aemeasurable, ?_⟩
    have heq := Measure.map_prod_map ρ μ measurable_id (hf.prodMk hg)
    rw [Measure.map_id, hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable] at heq
    exact heq.symm
  have hshuffle : MeasurePreserving (fun ω : A × X × Y => (ω.2.1, (ω.1, ω.2.2)))
      (ρ.prod (ν.prod ξ)) (ν.prod (ρ.prod ξ)) := by
    have hi := MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc ρ ν ξ)
    have hs : MeasurePreserving (Prod.swap : A × X → X × A) (ρ.prod ν) (ν.prod ρ) :=
      Measure.measurePreserving_swap
    have hp := hs.prod ((HasLaw.id (μ := ξ)).measurePreserving measurable_id)
    exact (measurePreserving_prodAssoc ν ρ ξ).comp (hp.comp hi)
  have hjoint : HasLaw (fun ω : A × Ω => (f ω.2, (ω.1, g ω.2)))
      (ν.prod (ρ.prod ξ)) (ρ.prod μ) := hshuffle.hasLaw.comp hbase
  have hfirst : HasLaw (fun ω : A × Ω => f ω.2) ν (ρ.prod μ) :=
    measurePreserving_fst.hasLaw.comp hjoint
  have hsecond : HasLaw (fun ω : A × Ω => (ω.1, g ω.2)) (ρ.prod ξ) (ρ.prod μ) :=
    measurePreserving_snd.hasLaw.comp hjoint
  exact (indepFun_iff_map_prod_eq_prod_map_map hfirst.aemeasurable hsecond.aemeasurable).2
    (by rw [hjoint.map_eq, hfirst.map_eq, hsecond.map_eq])
section Background
variable {A : Type*} [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A]
@[expose] abbrev BackgroundSpace (A : Type*) (N : ℕ) := A × Space N
@[expose] def backgroundLaw (ρ : Measure A) (N : ℕ) : Measure (BackgroundSpace A N) := ρ.prod (law N)
instance backgroundLaw_probability (ρ : Measure A) [IsProbabilityMeasure ρ] (N : ℕ) :
    IsProbabilityMeasure (backgroundLaw ρ N) := by unfold backgroundLaw; infer_instance
@[expose] def backgroundCoordinate {N : ℕ} (i : Fin N) (t : ℝ≥0) (ω : BackgroundSpace A N) : ℝ :=
  coordinate i t ω.2
@[expose] def backgroundProcess {N : ℕ} (t : ℝ≥0) (ω : BackgroundSpace A N) : A × (Fin N → ℝ) :=
  (ω.1, process t ω.2)
omit [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A] [BorelSpace A] in
lemma backgroundProcess_measurable (N : ℕ) (t : ℝ≥0) :
    Measurable (backgroundProcess (A := A) (N := N) t) :=
  measurable_fst.prodMk ((process_measurable N t).comp measurable_snd)
/-- The independent initial point and disorder are known at time zero;
all coordinate Brownian histories are observed at subsequent times. -/
@[expose] def backgroundFiltration (A : Type*) [TopologicalSpace A] [MetrizableSpace A]
    [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] (N : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (BackgroundSpace A N)) :=
  natural backgroundProcess (fun t => (backgroundProcess_measurable N t).stronglyMeasurable)
lemma background_coordinate_stronglyAdapted {N : ℕ} (i : Fin N) :
    StronglyAdapted (backgroundFiltration A N) (backgroundCoordinate i) := by
  intro t
  have h := stronglyAdapted_natural
    (fun s => (backgroundProcess_measurable (A := A) N s).stronglyMeasurable) t
  exact ((measurable_pi_apply i).comp (measurable_snd.comp h.measurable)).stronglyMeasurable
lemma background_known_at_zero {N : ℕ} :
    StronglyMeasurable[backgroundFiltration A N 0] (Prod.fst : BackgroundSpace A N → A) := by
  have h := stronglyAdapted_natural
    (fun s => (backgroundProcess_measurable (A := A) N s).stronglyMeasurable) 0
  exact (measurable_fst.comp h.measurable).stronglyMeasurable
omit [TopologicalSpace A] [MetrizableSpace A] [SecondCountableTopology A] [BorelSpace A] in
lemma background_paths_independent (ρ : Measure A) [IsProbabilityMeasure ρ] (N : ℕ) :
    iIndepFun (fun i (ω : BackgroundSpace A N) => fun t => backgroundCoordinate i t ω)
      (backgroundLaw ρ N) := by
  have hm : ∀ i : Fin N, Measurable (fun (ω : Space N) t => coordinate i t ω) :=
    fun i => measurable_pi_iff.mpr (fun t => coordinate_measurable i t)
  change iIndepFun (fun i => (fun (ω : Space N) t => coordinate i t ω) ∘
    (Prod.snd : BackgroundSpace A N → Space N)) (backgroundLaw ρ N)
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).comp measurable_snd |>.aemeasurable)]
  have hs : (backgroundLaw ρ N).map (Prod.snd : BackgroundSpace A N → Space N) = law N :=
    measurePreserving_snd.map_eq
  have hmaps : ∀ i : Fin N, (backgroundLaw ρ N).map
      (fun (ω : BackgroundSpace A N) t => backgroundCoordinate i t ω) =
      (law N).map (fun (ω : Space N) t => coordinate i t ω) := by
    intro i
    change (backgroundLaw ρ N).map ((fun (ω : Space N) t => coordinate i t ω) ∘ Prod.snd) = _
    rw [← Measure.map_map (hm i) measurable_snd, hs]
  have hmvec : Measurable (fun (ω : Space N) i t => coordinate i t ω) :=
    measurable_pi_iff.mpr hm
  change (backgroundLaw ρ N).map ((fun (ω : Space N) i t => coordinate i t ω) ∘ Prod.snd) = _
  rw [← Measure.map_map hmvec measurable_snd, hs]
  change (law N).map (fun (ω : Space N) i t => coordinate i t ω) =
    Measure.pi (fun i => (backgroundLaw ρ N).map
      (fun (ω : BackgroundSpace A N) t => backgroundCoordinate i t ω))
  simp_rw [hmaps]
  exact (paths_independent N).map_fun_eq_pi_map (fun i => (hm i).aemeasurable)
end Background
/-- The manuscript's initial point and actual ordered Gaussian tensor form
one independent background before taking its product with Brownian paths. -/
@[expose] abbrev ModelBackground (N p : ℕ) := FiniteModel.Vector N × FiniteModel.Disorder N p
@[expose] def modelBackgroundLaw {N : ℕ} (ν : Measure (FiniteModel.Vector N)) (p : ℕ) :
    Measure (ModelBackground N p) := ν.prod (FiniteModel.disorderLaw N p)
instance modelBackgroundLaw_probability {N : ℕ} (ν : Measure (FiniteModel.Vector N))
    [IsProbabilityMeasure ν] (p : ℕ) : IsProbabilityMeasure (modelBackgroundLaw ν p) := by
  unfold modelBackgroundLaw
  infer_instance
lemma model_initial_known_at_zero {N p : ℕ} :
    StronglyMeasurable[backgroundFiltration (ModelBackground N p) N 0]
      (fun ω : BackgroundSpace (ModelBackground N p) N => ω.1.1) :=
  (measurable_fst.comp background_known_at_zero.measurable).stronglyMeasurable
lemma model_disorder_known_at_zero {N p : ℕ} :
    StronglyMeasurable[backgroundFiltration (ModelBackground N p) N 0]
      (fun ω : BackgroundSpace (ModelBackground N p) N => ω.1.2) :=
  (measurable_snd.comp background_known_at_zero.measurable).stronglyMeasurable
lemma model_initial_hasLaw {N : ℕ} (ν : Measure (FiniteModel.Vector N))
    [IsProbabilityMeasure ν] (p : ℕ) :
    HasLaw (fun ω : BackgroundSpace (ModelBackground N p) N => ω.1.1) ν
      (backgroundLaw (modelBackgroundLaw ν p) N) :=
  measurePreserving_fst.hasLaw.comp measurePreserving_fst.hasLaw
lemma model_disorder_hasLaw {N : ℕ} (ν : Measure (FiniteModel.Vector N))
    [IsProbabilityMeasure ν] (p : ℕ) :
    HasLaw (fun ω : BackgroundSpace (ModelBackground N p) N => ω.1.2)
      (FiniteModel.disorderLaw N p) (backgroundLaw (modelBackgroundLaw ν p) N) :=
  measurePreserving_snd.hasLaw.comp measurePreserving_fst.hasLaw
end SphericalAging.VectorBrownian
