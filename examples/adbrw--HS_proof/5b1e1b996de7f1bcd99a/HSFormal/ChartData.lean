module

public import HSFormal.FreePoint
public import HSFormal.SpherePinch
public import HSFormal.CharacterDetector
                                        
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Topology.Metrizable.Urysohn

@[expose] public section

/-!
# Section 7: the chart, the subgroup `H`, the averaged coordinate and the sphere map

Fixed data of Section 7 of `fullHS_final.md` (L456–517) for an effective jointly continuous
`ℤ_[p]`-action on a manifold without boundary; the package is completed in `HSFormal.FixedData`.

* `HSFormal.PadicTail`: `H_j` as a compact multiplicative group, with normalized Haar measure.
* `HSFormal.padicChar`: the quotient character `χ : H_j → H_j/H_{j+1} ≅ C_p ⊆ S¹` (L517).
* `HSFormal.ChartData`: the free point `x₀`, a chart `φ` with `φ x₀ = 0`, `B(0,4) ⊆ φ(U)`, and
  `H = H_j` with displacement `≤ D < 1/64` on `φ⁻¹ B̄(0,2)` (7.1). Derived: `Ω = H · φ⁻¹ B(0,2)`
  (L468), the Haar average `F₀` (7.2) with (7.3), and the carrier `Z⁺ = F₀⁻¹ B̄(0,ρ₊)` (7.4).
* `HSFormal.exists_equivariant_sphere_map`: the equivariant map `ρ̃ : Z⁺ → T = S^{2m-1}` (7.7).
  It is obtained from the repo's character detector (`exists_finite_character_detector`), with
  the stabilizer hypothesis supplied by `padicStabilizer_le_nextPower_of_not_fixed`, instead of the
  paper's partition of unity on the free `C_p`-space `Z⁺/H'`. Both give a continuous map
  `Z⁺ → S^{2m-1} ⊆ ℂ^m` with `ρ̃(hx) = χ(h) ρ̃(x)`; here `ρ̃` is even defined and continuous on an
  open neighbourhood of `Z⁺`, and equivariant on all of `M`.
-/

noncomputable section

open Set Filter Metric MeasureTheory OnePoint Topology
open scoped unitInterval

namespace HSFormal

/-! ### The tail `H_j` as a compact multiplicative group, and the quotient character -/

/-- The tail `H_j = p^j ℤ_[p]`, written multiplicatively (for Haar averages and characters). -/
def PadicTail (p : ℕ) [Fact p.Prime] (j : ℕ) : Type :=
  Multiplicative (padicPowerSubgroup p j)

namespace PadicTail

variable {p : ℕ} [Fact p.Prime] {j : ℕ}

instance : CommGroup (PadicTail p j) := inferInstanceAs (CommGroup (Multiplicative _))

instance : TopologicalSpace (PadicTail p j) :=
  inferInstanceAs (TopologicalSpace (Multiplicative _))

instance : IsTopologicalGroup (PadicTail p j) :=
  inferInstanceAs (IsTopologicalGroup (Multiplicative (padicPowerSubgroup p j)))

instance : CompactSpace (PadicTail p j) :=
  haveI : CompactSpace (padicPowerSubgroup p j) :=
    isCompact_iff_compactSpace.1 (padicPowerSubgroup_isClosed j).isCompact
  inferInstanceAs (CompactSpace (Multiplicative (padicPowerSubgroup p j)))

instance : T2Space (PadicTail p j) :=
  inferInstanceAs (T2Space (Multiplicative (padicPowerSubgroup p j)))

instance : MeasurableSpace (PadicTail p j) := borel _

instance : BorelSpace (PadicTail p j) := ⟨rfl⟩

/-- The underlying p-adic integer. -/
def val (g : PadicTail p j) : ℤ_[p] :=
  ((Multiplicative.toAdd g : padicPowerSubgroup p j) : ℤ_[p])

                                                  
                                                                       
                              

       
                                                                                       

theorem val_mem (g : PadicTail p j) : g.val ∈ padicPowerSubgroup p j :=
  (Multiplicative.toAdd g).2

       
                                                                          

       
                                                    

theorem continuous_val : Continuous (val : PadicTail p j → ℤ_[p]) := continuous_subtype_val

instance {X : Type*} [AddAction ℤ_[p] X] : MulAction (PadicTail p j) X where
  smul g x := g.val +ᵥ x
  one_smul := zero_vadd ℤ_[p]
  mul_smul g h x := add_vadd g.val h.val x

                                                                              
                             

instance {X : Type*} [TopologicalSpace X] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X] :
    ContinuousSMul (PadicTail p j) X :=
  ⟨(continuous_val.comp continuous_fst).vadd continuous_snd⟩

end PadicTail

section Character

variable {p : ℕ} [Fact p.Prime] {j : ℕ}

instance (p : ℕ) [Fact p.Prime] (k : ℕ) : NeZero (p ^ k) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- The character `ℤ_[p] → ℤ/p^{j+1} → S¹`. On `H_j` it is the quotient character
`χ : H_j → H_j/H_{j+1} ≅ C_p ⊆ S¹` of (7.7), see `padicChar_eq_one_iff` and
`padicChar_pow_eq_one`. -/
def padicChar (p : ℕ) [Fact p.Prime] (j : ℕ) : AddChar ℤ_[p] Circle :=
  ZMod.toCircle.compAddMonoidHom (PadicInt.toZModPow (j + 1)).toAddMonoidHom

                                          
                                                                
                                                                                
                                                                      
                                                        
                                              
     

                                                                        
                                                                            
                                 
                                                       
                               
                                                   
                         
                                            
                   
      

                                                               
                                                  
                                                                       
                                                                                                
                                                         
                                                          
                                                  
                                          
                                                                                               

                                                                                           
                                                                                   
                                                                                             
                             
                                                                                          
                                       
                                                                               
                      

                                                                                     
                                                                           
                                
                                                                
                                                                   

                                                          
                                                    

end Character

/-! ### Charts and uniform chart displacement -/

section Chart

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M]

                                                                     
                                                                                
                                                             
                                                          
                                                 
                          
                                                                                      
                                            
                                                                 
                                                                             
                                                           
                            
                                                                                    
                             
             
                          
                                        
                             
                                                           
                             
                                  
                                                                             
                 
                                                     
                           

                                                                                              
                                                                             
                                                                                   
                                                                                           
                                               
                                          
                                                      
                                                                         
                       
                                                                                          
                                                                              
                                                                           
                                                                        
                                                                           
                                      
                                                                          
                          
                                
            
                        
                                                                                              
                                                        
                                         
                                   

end Chart

/-! ### The chart, the subgroup `H` and the averaged coordinate (7.1)–(7.3) -/

/-- The data `(x₀, φ, H = H_j, D)` of L458–466. -/
structure ChartData (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type*) [TopologicalSpace M]
    [AddAction ℤ_[p] M] where
  /-- A free point (L458). -/
  x₀ : M
  stabilizer_x₀ : AddAction.stabilizer ℤ_[p] x₀ = ⊥
  /-- A chart centred at `x₀` whose image contains `B(0,4)` (L460). -/
  φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  x₀_mem_source : x₀ ∈ φ.source
  φ_x₀ : φ x₀ = 0
  ball_subset_target : ball 0 4 ⊆ φ.target
  /-- `H = H_j` and the displacement bound `D` of (7.1). -/
  j : ℕ
  D : ℝ
  D_nonneg : 0 ≤ D
  D_lt : D < 1 / 64
  vadd_mem_source : ∀ h ∈ padicPowerSubgroup p j, ∀ x ∈ φ.source, ‖φ x‖ ≤ 2 →
    h +ᵥ x ∈ φ.source
  displacement_le : ∀ h ∈ padicPowerSubgroup p j, ∀ x ∈ φ.source, ‖φ x‖ ≤ 2 →
    ‖φ (h +ᵥ x) - φ x‖ ≤ D

namespace ChartData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (c : ChartData p n M)

/-- `H = H_j = p^j ℤ_[p]`. -/
abbrev H : AddSubgroup ℤ_[p] := padicPowerSubgroup p c.j

                      
                                                               

                              
abbrev fixH : Set M := AddAction.fixedPoints (padicPowerSubgroup p c.j) M

/-- `Ω = H · φ⁻¹ B(0,2)` (L468). -/
def Ω : Set M := {x | ∃ h ∈ c.H, h +ᵥ x ∈ c.φ.source ∧ ‖c.φ (h +ᵥ x)‖ < 2}

/-- The averaged coordinate `F₀(x) = ∫_H φ(hx) dμ(h)` for normalized Haar measure (7.2). -/
def F₀ (x : M) : EuclideanSpace ℝ (Fin n) :=
  ∫ g, c.φ (g • x) ∂normalizedCompactHaar (PadicTail p c.j)

                                                                   
                
                                                                                                   

                                                                         
def carrier (ρplus : ℝ) : Set M := c.Ω ∩ c.F₀ ⁻¹' closedBall 0 ρplus

                                                                                   
                                    
                                                             

                                                  
                                                         
                                                                                     
                                                             
                                                     
                                                                                          

                                                                                          
                
theorem exists_near {x : M} (hx : x ∈ c.Ω) :
    ∃ x₁ ∈ c.φ.source, ‖c.φ x₁‖ < 2 ∧
      ∀ h ∈ c.H, h +ᵥ x ∈ c.φ.source ∧ ‖c.φ (h +ᵥ x) - c.φ x₁‖ ≤ c.D := by
  obtain ⟨h₁, hh₁, hs, hlt⟩ := hx
  refine ⟨h₁ +ᵥ x, hs, hlt, fun h hh => ?_⟩
  have he : h +ᵥ x = (h - h₁) +ᵥ (h₁ +ᵥ x) := by rw [vadd_vadd, sub_add_cancel]
  have hmem : h - h₁ ∈ c.H := c.H.sub_mem hh hh₁
  rw [he]
  exact ⟨c.vadd_mem_source _ hmem _ hs hlt.le, c.displacement_le _ hmem _ hs hlt.le⟩

theorem vadd_mem_source_of_mem_Ω {x : M} (hx : x ∈ c.Ω) {h : ℤ_[p]} (hh : h ∈ c.H) :
    h +ᵥ x ∈ c.φ.source := by
  obtain ⟨x₁, -, -, hx₁⟩ := c.exists_near hx
  exact (hx₁ h hh).1

theorem Ω_subset_source : c.Ω ⊆ c.φ.source := fun x hx => by
  simpa using c.vadd_mem_source_of_mem_Ω hx c.H.zero_mem

/-- On `Ω` the displacement of `H` is at most `2D` (L468). -/
theorem displacement_Ω {x : M} (hx : x ∈ c.Ω) {h : ℤ_[p]} (hh : h ∈ c.H) :
    ‖c.φ (h +ᵥ x) - c.φ x‖ ≤ 2 * c.D := by
  obtain ⟨x₁, -, -, hx₁⟩ := c.exists_near hx
  have h1 := (hx₁ h hh).2
  have h2 := (hx₁ 0 c.H.zero_mem).2
  rw [zero_vadd] at h2
  calc ‖c.φ (h +ᵥ x) - c.φ x‖ = ‖(c.φ (h +ᵥ x) - c.φ x₁) - (c.φ x - c.φ x₁)‖ := by
        congr 1; abel
    _ ≤ ‖c.φ (h +ᵥ x) - c.φ x₁‖ + ‖c.φ x - c.φ x₁‖ := norm_sub_le _ _
    _ ≤ 2 * c.D := by linarith

                                   
                                                                         
                                               
                                   
                      
                                                                      
                                                      
                              

                                                                                      
                                                           

                            
                                                                                        
             
                             
                                                                     
                             
                                                                                   

                                                            
                                                                               
         
                                                                                            
                  
         
                                 
                                                                              

                                    
                           
                                                                              
                        

                                                
                                      
                                                                  

                                                               
                                                   
                                                                

                                                                                         
                                                        
                                                                          

                                          
                                            
            
                                                                        
                                                                      
                                            
                                                   
                                                                            

                                                                                  
                                                                    
         
                                                                    
       
         
                                                                                    

                                   

theorem continuous_φ_smul [ContinuousVAdd ℤ_[p] M] {x : M} (hx : x ∈ c.Ω) :
    Continuous fun g : PadicTail p c.j => c.φ (g • x) :=
  c.φ.continuousOn.comp_continuous (continuous_id.smul continuous_const) fun g =>
    c.vadd_mem_source_of_mem_Ω hx g.val_mem

theorem integrable_φ_smul [ContinuousVAdd ℤ_[p] M] {x : M} (hx : x ∈ c.Ω) :
    Integrable (fun g : PadicTail p c.j => c.φ (g • x)) (normalizedCompactHaar _) := by
  have hi := ContinuousOn.integrableOn_compact (μ := normalizedCompactHaar (PadicTail p c.j))
    isCompact_univ (c.continuous_φ_smul hx).continuousOn
  simpa only [IntegrableOn, Measure.restrict_univ] using hi

                                                               
                                                                                 
                                                 
                               
                                                                             

                                        
                                                                       
                                                                 
                                                                          
              

                                       
theorem norm_F₀_sub_le [ContinuousVAdd ℤ_[p] M] {x : M} (hx : x ∈ c.Ω) :
    ‖c.F₀ x - c.φ x‖ ≤ 2 * c.D := by
  have he : c.F₀ x - c.φ x =
      ∫ g, (c.φ (g • x) - c.φ x) ∂normalizedCompactHaar (PadicTail p c.j) := by
    rw [integral_sub (c.integrable_φ_smul hx) (integrable_const _)]
    simp [F₀]
  rw [he]
  calc _ ≤ 2 * c.D * (normalizedCompactHaar (PadicTail p c.j)).real univ :=
        norm_integral_le_of_norm_le_const
          (Eventually.of_forall fun g => c.displacement_Ω hx g.val_mem)
    _ = 2 * c.D := by simp

                                        
                                                                        
                                                            
                                              
                                                                   
                                                                                
                                    
                                                                                 
                                                    
                                                        
                                                  
                                                                                     
                                                        
                                                                                              

                                                                           
                                                                
                                  
                                           
                                                                      
                                                      
                                      

                              
                                                                                      
                                                                 
                                     
                   
                        
                                                              
                                                              
                                   
                                                                                     
                                                                   
         
                                                                         
                                                                        
         
                                                                                         
                                                      

                                    
                                                                             
                                                        
                                                                                     

                                                                     
                                              
                                                                 
                                                          
                               
                                                                                

                                                                     
                                                           
                                            
                                                          
                                                          
                                                                 
                                                                           
                                                      
                                               
                                                                
                                                   
                                             
                                                                       
                                                             
                                                                                     
                     
                                         
              

end ChartData

/-! ### The equivariant sphere map (7.7) -/

section SphereMap

variable {p : ℕ} [Fact p.Prime] {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]

                                                                                                
                                                                                                 
                                                                                                   
                                                                             
                                                                             
                                                                                           
                                                                            
                                                  
                                                                         
                                                                                         
           
                                                                  
                                                                                               
                                                                                     
                                    
                             
                                                                                
                      
                                                         
                                                        
                                                             
                                                                   
                                                                                                     
                
         
                                                     
                                                                                            
                                                             
                                                        
                                                                                             
                     
                                   
            
             
                                                                                 
                         
                                                      
                                                                                           
                                                                                         
                                              
               
                                                 

end SphereMap

end HSFormal
