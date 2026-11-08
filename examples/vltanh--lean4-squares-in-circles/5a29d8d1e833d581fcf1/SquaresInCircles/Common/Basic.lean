module

public import SquaresInCircles.Geometry

/-!
# Frames, interior-disjointness and the farthest-vertex bound

Vector operations, a square's frame and vertices, and the squared distance
`phi` from a point to the farthest vertex of a square: the closed square lies
in a closed disk about the point exactly when `phi` is at most the squared
radius, and `phi` bounds the distance of the centre. Distances always use
`normSq`; the product-space norm on `ℝ × ℝ` is the maximum norm.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

                                                  
def add (p q : Point) : Point := (p.1 + q.1, p.2 + q.2)
def scale (t : ℝ) (p : Point) : Point := (t * p.1, t * p.2)

                                                 
                                        

                                                                        
                     
                              
                
                              
               
                                    

                                                                            
                                                                                              

                                                                               
                        
                                                                               
                        
                                                       
                                                                  

                                              
                                                                     
                                       
                    
          

                                                                            
                                                               
                                                                 

                                                                           
                                                       

                                                                
                               
                                                                                       
                                                                          

                                                                    
                               
def frameX (S : UnitSquare) (v : Point) : ℝ := S.cosine*v.1 + S.sine*v.2
def frameY (S : UnitSquare) (v : Point) : ℝ := -S.sine*v.1 + S.cosine*v.2

lemma frame_norm (S : UnitSquare) (v : Point) :
    (frameX S v)^2 + (frameY S v)^2 = normSq v := by
  simp only [frameX,frameY,normSq]; linear_combination (v.1^2+v.2^2)*S.unit

                                                
                                                                     
                                                                            

                                                                             
                                    
                                                
                                                          
                                                         
                                                                             
                            

lemma frame_distance (S : UnitSquare) (p o : Point) :
    (localX S p - localX S o)^2 + (localY S p - localY S o)^2 = normSq (sub p o) := by
  rw [← frame_norm]; simp only [localX,localY,frameX,frameY,sub]; ring

/-- The vector with coordinates `p` in the frame of `S`. -/
def rotate (S : UnitSquare) (p : Point) : Point :=
  (S.cosine * p.1 - S.sine * p.2,
   S.sine * p.1 + S.cosine * p.2)

lemma localX_rotated (S : UnitSquare) (p : Point) :
    localX S (add S.center (rotate S p)) = p.1 := by
  simp only [localX,add,rotate]; linear_combination p.1*S.unit

lemma localY_rotated (S : UnitSquare) (p : Point) :
    localY S (add S.center (rotate S p)) = p.2 := by
  simp only [localY,add,rotate]; linear_combination p.2*S.unit

/-- Nonnegative absolute coordinates of the tested point in a square's frame. -/
def alpha (S : UnitSquare) (o : Point) : ℝ := |localX S o|
def beta (S : UnitSquare) (o : Point) : ℝ := |localY S o|

                                                                               
                                                                             

                                                      
                                                 
                                                                    

                                                      
                                                
                                                                   

                                                      
                                                            
                                                                         

                                                                             
def phi (a b : ℝ) : ℝ := (a + 1/2)^2 + (b + 1/2)^2

/-- A number of absolute value `c` with the sign of `x`. -/
lemma exists_signed (x : ℝ) {c : ℝ} (hc : 0 ≤ c) : ∃ u : ℝ, |u|=c ∧ x*u=c*|x| := by
  rcases abs_cases x with ⟨hx,-⟩ | ⟨hx,-⟩
  · exact ⟨c,abs_of_nonneg hc,by rw [hx]; ring⟩
  · exact ⟨-c,by rw [abs_neg,abs_of_nonneg hc],by rw [hx]; ring⟩

/-- The vertex across both axes from `o` is at squared distance `phi` from it. -/
lemma phi_le_of_contained (S : UnitSquare) (o : Point) (R : ℝ)
    (h : ∀ p, closedSquare S p → inDisk o R p) :
    phi (alpha S o) (beta S o) ≤ R^2 := by
  obtain ⟨u,hu,hxu⟩ := exists_signed (localX S o) (c := 1/2) (by norm_num)
  obtain ⟨v,hv,hyv⟩ := exists_signed (localY S o) (c := 1/2) (by norm_num)
  have hh := h (add S.center (rotate S (-u,-v))) (by
    simp only [closedSquare,localX_rotated,localY_rotated,abs_neg,hu,hv,le_refl,and_self])
  rw [inDisk,← frame_distance S,localX_rotated,localY_rotated] at hh
  have hu2 : u^2=1/4 := by rw [← sq_abs,hu]; norm_num
  have hv2 : v^2=1/4 := by rw [← sq_abs,hv]; norm_num
  unfold phi alpha beta
  nlinarith [sq_abs (localX S o),sq_abs (localY S o)]

lemma Packing.phi_le {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (i : Fin n) :
    phi (alpha (S i) o) (beta (S i) o) ≤ R^2 :=
  phi_le_of_contained _ _ _ (hp.2.1 i)

                                                                            
                                                          
                                                           
                                                                                   
                      
                                                         
                                                                   
                                                        
                                                                  
                                                                                
                                                          
                                                      

                                                                             
                                                                              
              
                                                               
                                                   
               
                                                      
                                                                                      

                                                                 
lemma coordinate_le_of_phi {a b Q : ℝ} (hb : 0 ≤ b) (h : phi a b ≤ Q) :
    a ≤ Real.sqrt (Q-1/4)-1/2 := by
  have hs := Real.le_sqrt_of_sq_le (show (a+1/2)^2 ≤ Q-1/4 by unfold phi at h; nlinarith)
  linarith

                                                                 
                                                                       
                                                           
                      
                                      
                                   
                                                 
             
                                    
                                                
             

                                                    
                                                      
                                                         
                                   
                                                                               
                                                                               
                                         
                                                                               
                                         
                                                   
                                                  
                                                  
                                                                                 
                              
       

                                                                                    
                                                               
                                
                                                        
                                                        
                                   
                                                         
                                                         
                                                         
                                                         
                                                                                               
                                                                                               
                                                                             
                                     
                                                                        
                                     

                                                           
                                                            
                                                                               
                                                                  

                                     

                                                                               
                                                
                                                                

end SquaresInCircles
