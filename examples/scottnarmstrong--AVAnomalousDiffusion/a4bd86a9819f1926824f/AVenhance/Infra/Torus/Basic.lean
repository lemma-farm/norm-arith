-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Mathlib
public import Homogenization.Ambient.Basic
public import AVenhance.Statements.Roots.IsZ2Periodic
public import AVenhance.Statements.Roots.UnitCube

/-! Basic measurable and periodic infrastructure for the unit torus. -/

@[expose] public section

noncomputable section

open MeasureTheory Set

local instance avInfraTorusBasicMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraTorusBasicMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraTorusBasicIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Torus

open Homogenization

/-- A translated half-open fundamental cell `(aᵢ,aᵢ+1]^d`. -/
def unitCellAt (d : ℕ) (a : Fin d → ℝ) : Set (Vec d) :=
  {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)}

/-- The half-open fundamental cell `(0,1]^d`. This convention matches
`UnitAddTorus.measurableEquivPiIoc` and gives an exact fundamental domain. -/
def unitCell (d : ℕ) : Set (Vec d) := unitCellAt d (fun _ => 0)

theorem measurableSet_unitCellAt (d : ℕ) (a : Fin d → ℝ) :
    MeasurableSet (unitCellAt d a) := by
  simpa [unitCellAt] using MeasurableSet.univ_pi'
    (fun i => (measurableSet_Ioc : MeasurableSet (Set.Ioc (a i) (a i + 1))))

theorem measurableSet_unitCell (d : ℕ) : MeasurableSet (unitCell d) := by
  rw [unitCell]
  exact measurableSet_unitCellAt d (fun _ => 0)

                                                       
                                                                   

                                                                               
                                                              
                                                         

                                                                                         
                                                             
                                                   
             
               
               
               
               

                                                                                      
theorem unitCell_ae_eq_unitCube :
    unitCell 2 =ᵐ[(volume : Measure (Vec 2))] AVenhance.unitCube := by
  have h₁ :
      (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1) =ᵐ[volume]
        Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
    simpa [volume_pi] using
      (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
        (g := fun _ : Fin 2 => (1 : ℝ)))
  have h₂ :
      (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) =ᵐ[volume]
        (Set.pi Set.univ fun _ : Fin 2 => Set.Ioc (0 : ℝ) 1) := by
    simpa [volume_pi] using
      (Measure.univ_pi_Ioc_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
        (g := fun _ : Fin 2 => (1 : ℝ))).symm
  simpa [unitCell, unitCellAt, AVenhance.unitCube, Set.pi] using (h₁.trans h₂).symm

/-- Set integrals over the generic half-open cell and the open square agree. -/
theorem integral_unitCell_eq_unitCube {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Vec 2 → E) :
    ∫ x in unitCell 2, f x = ∫ x in AVenhance.unitCube, f x := by
  exact setIntegral_congr_set unitCell_ae_eq_unitCube

/-- The quotient map from Euclidean coordinates to the unit additive torus. -/
def toUnitTorus (d : ℕ) (x : Vec d) : UnitAddTorus (Fin d) :=
  fun i => (x i : UnitAddCircle)

/-- The representative of a torus point in the half-open cell `(0,1]^d`. -/
def unitTorusRepresentative (d : ℕ) (x : UnitAddTorus (Fin d)) : Vec d :=
  fun i => ((AddCircle.equivIoc (1 : ℝ) 0 (x i)).1 : ℝ)

/-- Transfer a Euclidean function to the torus by taking its canonical cell representative. -/
def periodicToTorus {d : ℕ} {α : Type*}
    (f : Vec d → α) : UnitAddTorus (Fin d) → α :=
  fun x => f (unitTorusRepresentative d x)

/-- Pull a torus function back to a function on Euclidean coordinates. -/
def fromUnitTorus {d : ℕ} {α : Type*}
    (f : UnitAddTorus (Fin d) → α) : Vec d → α :=
  fun x => f (toUnitTorus d x)

       
                                                                 
                                                 
                                                                                  

theorem unitTorusRepresentative_eq_of_mem_unitCell {d : ℕ} {x : Vec d}
    (hx : x ∈ unitCell d) : unitTorusRepresentative d (toUnitTorus d x) = x := by
  funext i
  have hi : x i ∈ Set.Ioc (0 : ℝ) (0 + 1) := hx i
  have h := AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := x i) hi
  exact congrArg Subtype.val h

                                                                
                                                                                        
           
                                 
                                                                         
           
                 
                                                                                             
                            
                                                 
                                            
                            
                  
                                               
                                                       
                
          
                                         
                      
      
                                                   
                                                                              
                                       

                                                                                     
                                                         
                                           
                                               
          
                                                        
                                                 

                                                                            
                                                                   
                                                                         
           
                      
         
          
                                                                        
                        
                                                 
                                  
                        
                   

                                                                                  
       
                                                                                
                                                         
          
                                                                       
                              

                                                                                       
       
                                                         
                                                                                
          
                                                              
                                          

                                                                                                 
                                                                                 
theorem integral_fromUnitTorus_eq_unitCellAt {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus (Fin d) → E) (a : Fin d → ℝ) :
    ∫ x : UnitAddTorus (Fin d), f x = ∫ x in unitCellAt d a, fromUnitTorus f x := by
  change ∫ x : UnitAddTorus (Fin d), f x =
    ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
      f (fun i => (x i : UnitAddCircle))
  exact UnitAddTorus.integral_preimage (d := Fin d) f a

/-- Integration on the torus agrees with integration of the periodic transfer on the unit cell. -/
theorem integral_periodicToTorus_eq_unitCell {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec d → E) :
    ∫ x : UnitAddTorus (Fin d), periodicToTorus f x = ∫ x in unitCell d, f x := by
  calc
    ∫ x : UnitAddTorus (Fin d), periodicToTorus f x =
        ∫ x in unitCellAt d (fun _ => 0), fromUnitTorus (periodicToTorus f) x :=
      integral_fromUnitTorus_eq_unitCellAt (periodicToTorus f) (fun _ => 0)
    _ = ∫ x in unitCell d, fromUnitTorus (periodicToTorus f) x := rfl
    _ = ∫ x in unitCell d, f x := by
      apply setIntegral_congr_ae (measurableSet_unitCell d)
      filter_upwards with x hx
      have hrep : unitTorusRepresentative d (toUnitTorus d x) = x :=
        unitTorusRepresentative_eq_of_mem_unitCell hx
      simp [fromUnitTorus, periodicToTorus, hrep]

                                                                                      
                                                           
                                                            
                                           
                                
                                  
      
                                
                              
                                                   
                                                                      
                      
                                                                       
                                                          
                                                                       
                                                                        

end AVenhance.Infra.Torus
