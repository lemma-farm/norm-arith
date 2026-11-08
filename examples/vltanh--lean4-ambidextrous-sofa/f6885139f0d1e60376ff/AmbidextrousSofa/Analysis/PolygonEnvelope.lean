module

public import AmbidextrousSofa.Analysis.PolygonVariation

@[expose] public section

/-!
# Finite expressions for actual polygon roofs and hallway barriers

The outer roof and the inner wall system use the same normal indices. A
source that occurs in several corners or also supplies the proper terminal
wall is represented by the same leaf. This keeps equal slopes from being
mistaken for different moving sources.

The zero leaf is the top wall in the outer expression and the baseline in
the inner expression. All other leaves are actual supporting halfplanes.
On the actual polygon projection the outer expression equals `capRoof`.
The inner expression equals the literal maximum of the sampled physical
corners and the terminal wall. No contact ordering is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

def roofExprList : List ι → WallExpr (Option ι)
  | [] => WallExpr.leaf none
  | i :: is => WallExpr.minimum (WallExpr.leaf (some i)) (roofExprList is)

def roofExpr [Fintype ι] : WallExpr (Option ι) :=
  roofExprList (Finset.univ.toList)

theorem le_eval_roofExprList_iff (is : List ι) (v : Option ι → ℝ) (y : ℝ) :
    y ≤ (roofExprList is).eval v ↔ y ≤ v none ∧ ∀ i ∈ is, y ≤ v (some i) := by
  induction is <;> simp [roofExprList, WallExpr.eval, *, and_left_comm]

theorem le_eval_roofExpr_iff [Fintype ι] (v : Option ι → ℝ) (y : ℝ) :
    y ≤ (roofExpr (ι := ι)).eval v ↔ y ≤ v none ∧ ∀ i, y ≤ v (some i) := by
  simp [roofExpr, le_eval_roofExprList_iff]

def wallSlope (normal : ι → Plane) : Option ι → ℝ
  | none => 0
  | some i => -(normal i).1 / (normal i).2

def roofIntercept (normal : ι → Plane) (height : ι → ℝ) : Option ι → ℝ
  | none => 1
  | some i => height i / (normal i).2

def barrierIntercept (normal : ι → Plane) (height : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => (height i - 1) / (normal i).2

                                                                               
             
                                                   

                                                                    
                                                                     
                                               
                                                
                                                                   
                          
                                                                      
                                               
                            
       
                                                            
                                                            
           
                 
                                                                                    
                                    

def roofEnvelope [Fintype ι] (normal : ι → Plane) (height : ι → ℝ) (x : ℝ) : ℝ :=
  (roofExpr (ι := ι)).eval (fun i => wallSlope normal i * x + roofIntercept normal height i)

theorem le_roofEnvelope_iff [Fintype ι] (normal : ι → Plane) (height : ι → ℝ)
    (hnormal : ∀ i, 0 < (normal i).2) (x y : ℝ) :
    y ≤ roofEnvelope normal height x ↔
      y ≤ 1 ∧ ∀ i, coordDot (x, y) (normal i) ≤ height i := by
  simp only [roofEnvelope, le_eval_roofExpr_iff, wallSlope, roofIntercept, zero_mul, zero_add]
  refine and_congr_right' (forall_congr' fun i => ?_)
  rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ (hnormal i), coordDot]
  constructor <;> intro h <;> linarith

/-- The finite upper expression is the actual fiber supremum, including
the vertical endpoint faces. -/
theorem capRoof_upperPolygon [Fintype ι] (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ)
    (hnormal : ∀ i, 0 < (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    {x : ℝ} (hx : x ∈ Icc l r) :
    capRoof (upperPolygon l r normal height) x = roofEnvelope normal height x := by
  have hK := isCompact_upperPolygon l r normal height
  have hmem (y : ℝ) : (x, y) ∈ upperPolygon l r normal height ↔
      0 ≤ y ∧ y ≤ roofEnvelope normal height x := by
    rw [mem_upperPolygon_iff, le_roofEnvelope_iff normal height hnormal]
    simp only [mem_Icc, hx]
    tauto
  refine le_antisymm ((hmem _).mp (capRoof_mem hK ?_)).2
    (le_capRoof hK ((hmem _).mpr ⟨?_, le_rfl⟩))
  · rwa [horizontalProjection_upperPolygon l r normal height hbaseline]
  · exact (le_roofEnvelope_iff normal height hnormal x 0).mpr ⟨zero_le_one, hbaseline x hx⟩

                                                                                   
                                              
                                                            

                                                       
                                                           
                                                                   
                                                                                         
                                          
          
                                                               
                     
                                                    
                                                                                            
      

                                                                  
def supportWall (U : Set Plane) (n : Plane) (x : ℝ) : ℝ :=
  (support U n - 1 - x * n.1) / n.2

                                                          
                                                           

                                                               
                                                                
                                                            

def cornerExpr (ij : ι × ι) : WallExpr (Option ι) :=
  WallExpr.minimum (WallExpr.leaf (some ij.1)) (WallExpr.leaf (some ij.2))

def nicheExpr : List (ι × ι) → WallExpr (Option ι)
  | [] => WallExpr.leaf none
  | ij :: rest => WallExpr.maximum (cornerExpr ij) (nicheExpr rest)

def barrierExpr (corners : List (ι × ι)) (terminal : Option ι) : WallExpr (Option ι) :=
  match terminal with
  | none => nicheExpr corners
  | some j => WallExpr.maximum (nicheExpr corners) (WallExpr.leaf (some j))

/-- Literal sampled corners, always clipped from below at zero. -/
def finiteNiche (U : Set Plane) (normal : ι → Plane) : List (ι × ι) → ℝ → ℝ
  | [], _ => 0
  | ij :: rest, x => max (min (supportWall U (normal ij.1) x)
      (supportWall U (normal ij.2) x)) (finiteNiche U normal rest x)

/-- A proper terminal wall remains a whole wall. It shares its source index
with any corner in which the same support is used. -/
def finiteBarrier (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) : ℝ :=
  match terminal with
  | none => finiteNiche U normal corners x
  | some j => max (finiteNiche U normal corners x) (supportWall U (normal j) x)

                                                               
                                        
                                                                
                                                                                   
                                                            

                                                               
                                                                            
                                                         

                                                                 
                                                            
                                                       
                                                             

theorem finiteBarrier_eq_eval {U : Set Plane} (normal : ι → Plane) (height : ι → ℝ)
    (hexact : ∀ i, support U (normal i) = height i)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) :
    finiteBarrier U normal corners terminal x = (barrierExpr corners terminal).eval
      (fun i => wallSlope normal i * x + barrierIntercept normal height i) := by
  have hline (i : ι) : supportWall U (normal i) x =
      wallSlope normal (some i) * x + barrierIntercept normal height (some i) := by
    simp only [supportWall, wallSlope, barrierIntercept, hexact]; ring
  have hniche : finiteNiche U normal corners x = (nicheExpr corners).eval
      (fun i => wallSlope normal i * x + barrierIntercept normal height i) := by
    induction corners <;>
      simp [finiteNiche, nicheExpr, cornerExpr, WallExpr.eval, wallSlope, barrierIntercept, *]
  cases terminal <;> simp only [finiteBarrier, barrierExpr, WallExpr.eval, hniche, hline]

                                                                     
                                                    
                                                              
                                                                              
                                                                             

                                                              
                                                                         
                                                                                    
                                                    
                                             
                                                                      
                                                                           
          
                                            
                                                                          
                     
                                                       
                                                                                               
      

                                                                                   
                 
                                                                             
                                                             
                                                                                         

                                                                                    
                 
                                                                             
                                                              
                                                                                          

                                                                       
                                    
                                                           
                                                         
                                                                            
                                          

                                                                            
                                                       
                                                                                    
                             
                                                                                             
                            

                                                                         
                                                        
                                                             
                                                       
                                     
                                                                           
                                                                                  
                                                    
                                                                                 
                                                       
                                                     
                                                                                         
                                                                                  
                                                             
                                                                         
                                           
                                                                             

end FinitePolygon

end AmbidextrousSofa
