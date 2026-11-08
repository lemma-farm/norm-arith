/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibbleAdapter
public import PartitionedTriangleAbsorption.ReserveCoverDown
public import PartitionedTriangleAbsorption.ReserveBudget

/-! # Uniform reserve cover-down and absorption from exact inputs (L5.a → L6)

Inputs: a graph `G`, a supplied universal absorber `A` for the reserve `X`
(`∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)`), an `α`-anti-edgeful reserve
graph on `X`, integral divisibility of `E(G)`, and an exact physical weighting with
cap `b/n` on the main graph `J = G - (A ∪ X)`. The absorber and the weighting are
explicit hypotheses; neither is constructed here.

Output (`typed_cover_down_absorption`): `HasDecomp p F E(G)` for all `n ≥ N`, with
`N` depending only on `b` and `α`. The packing `Q`, its residual degree bound and
the reserve cover are produced, not assumed: `Q` comes from
`TypedNibble.typed_nibble_packing`, the scalar budget from
`ReserveBudget.sparse_residue_budget`, and the cover-down/absorption step from
`ReserveCoverDown.hasDecomp_of_sparse_main_packing`, whose absorber receives
`X \ P_reserve` (not `E(J) \ Q`).

Scalar schedule: `η = α²/256`, `a = α n`, `r = ⌈η n⌉`, `m = |E(J) \ Q|`,
`q = ⌊a/16⌋`, `N = max N_nibble ⌈256/α²⌉`.
-/

/-
New isolated module for the 2026-10-12 task.
Source proof: PartitionedTriangleAbsorption/TypedCoverDownConsumer.lean.
Original SHA256: 258a0bea3239e55bc127434bfde355fa4fa7628328125142f8f369a388e3a2b5.
Only namespace/import isolation and explicitly indicated elementary estimates
are changed; the original file is not modified.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedCoverDown

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A non-diagonal unordered pair has exactly two endpoints. -/
theorem card_endpoints_of_not_isDiag {e : Sym2 V} (he : ¬ e.IsDiag) :
    (univ.filter (fun v => v ∈ e)).card = 2 := by
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := fun h => he (Sym2.mk_isDiag_iff.mpr h)
    have h : univ.filter (fun v => v ∈ s(x, y)) = {x, y} := by
      ext v
      simp
    rw [h, card_pair hxy]

/-- **Handshake identity for a loopless edge set.** -/
theorem sum_degrees_eq_two_mul_card (L : Finset (Sym2 V)) (hdiag : ∀ e ∈ L, ¬ e.IsDiag) :
    ∑ v, (L.filter (fun e => v ∈ e)).card = 2 * L.card := by
  simp_rw [card_filter]
  rw [sum_comm]
  have h : ∀ e ∈ L, (∑ v, if v ∈ e then 1 else 0) = 2 := by
    intro e he
    rw [← card_filter]
    exact card_endpoints_of_not_isDiag (hdiag e he)
  rw [sum_congr rfl h, sum_const, smul_eq_mul, mul_comm]

/-- **Degree/cardinality bridge.** A loopless edge set of maximum degree at most `r`
on `n` vertices has at most `n r / 2` edges. (The converse fails; see the examples.) -/
theorem card_le_of_degBounded (L : Finset (Sym2 V)) (hdiag : ∀ e ∈ L, ¬ e.IsDiag) (r : ℝ)
    (h : DegBounded L r) : (L.card : ℝ) ≤ Fintype.card V * r / 2 := by
  have hsum : ((2 * L.card : ℕ) : ℝ) ≤ Fintype.card V * r := by
    rw [← sum_degrees_eq_two_mul_card L hdiag]
    push_cast
    calc ∑ v, ((L.filter (fun e => v ∈ e)).card : ℝ) ≤ ∑ _v : V, r :=
          sum_le_sum (fun v _ => h v)
      _ = Fintype.card V * r := by rw [sum_const, card_univ, nsmul_eq_mul]
  push_cast at hsum
  linarith

omit [Fintype V] [DecidableEq V] in
theorem not_isDiag_of_mem_edgeFinset (G : SimpleGraph V) [Fintype G.edgeSet]
    {E : Finset (Sym2 V)} (hE : E ⊆ G.edgeFinset) : ∀ e ∈ E, ¬ e.IsDiag := fun _ he =>
  G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hE he))

/-- **Scalar schedule.** For `η = α²/256`, `n ≥ 256/α²`, `r = ⌈η n⌉`, `q = ⌊α n/16⌋` and
`m ≤ n r / 2`, the exact cover-down budget holds and `q > 0`. -/
theorem schedule_budget (α n m : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hn : 256 / α ^ 2 ≤ n)
    (hm : m ≤ n * (⌈α ^ 2 / 256 * n⌉₊ : ℝ) / 2) :
    0 < ⌊α * n / 16⌋₊ ∧
      m / (⌊α * n / 16⌋₊ : ℝ) + 2 * ((⌈α ^ 2 / 256 * n⌉₊ : ℝ) + 2 * ⌊α * n / 16⌋₊) <
        α * n := by
  have hα2 : 0 < α ^ 2 := by positivity
  have hαn2 : 256 ≤ α ^ 2 * n := by
    have := mul_le_mul_of_nonneg_left hn hα2.le
    rwa [mul_div_cancel₀ _ hα2.ne'] at this
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hαα : α ^ 2 ≤ α := by nlinarith
  have hαn : 256 ≤ α * n := le_trans hαn2 (mul_le_mul_of_nonneg_right hαα hn0.le)
  set η := α ^ 2 / 256 with hη
  have hηn : 1 ≤ η * n := by rw [hη]; linarith
  set r : ℕ := ⌈η * n⌉₊ with hr
  set q : ℕ := ⌊α * n / 16⌋₊ with hq
  have hr2 : (r : ℝ) ≤ 2 * (η * n) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ η * n by linarith)
    rw [← hr] at this
    linarith
  have hqu : (q : ℝ) ≤ α * n / 16 := Nat.floor_le (by linarith)
  have hql : α * n / 32 ≤ q := by
    have := Nat.lt_floor_add_one (α * n / 16)
    rw [← hq] at this
    linarith
  have hqpos : 0 < q := by
    have : (0 : ℝ) < q := lt_of_lt_of_le (by linarith) hql
    exact_mod_cast this
  refine ⟨hqpos, ?_⟩
  have hrbound : 64 * n * r ≤ (α * n) ^ 2 := by
    have h1 : 64 * n * r ≤ 64 * n * (2 * (η * n)) :=
      mul_le_mul_of_nonneg_left hr2 (by linarith)
    have h2 : 64 * n * (2 * (η * n)) = (α * n) ^ 2 / 2 := by rw [hη]; ring
    have h3 : 0 ≤ (α * n) ^ 2 := sq_nonneg _
    linarith
  have hb := ReserveBudget.sparse_residue_budget n (α * n) m r q hn0 (by linarith)
    (by nlinarith) hm hrbound hql hqu
  linarith

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedCoverDown

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedCoverDown

open Finset

                                                                                      
                                                                                      
                                                                                       
                                                                       
                                                                          
                                                                                      
                            
                                                                                        
                                                                           
                                                               
                                                                        
                                                                                
                                                            
                                   
                                                           
                                                             
                                                                                       
                                               
                                      
                                                                                     
                                           
                                        
                                             
                                  
                                    
            
                                                                                 
                                    
                                                                  
           
                                                                              
                                                                                         
                                             
                                                                                      
                     
                                               
                                                 
                                                                            
                                                                    
                                           
                                    
                                                                                               
                                                                                 
                                                                                          
                                                        
               
                                                                                     

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedCoverDown
