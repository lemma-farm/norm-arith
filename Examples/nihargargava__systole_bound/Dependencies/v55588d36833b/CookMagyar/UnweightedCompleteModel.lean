module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v55588d36833b.CookMagyar.UnweightedResidueAbel
public import Examples.nihargargava__systole_bound.Dependencies.v55588d36833b.CookMagyar.HuaOrthogonality
public import Examples.nihargargava__systole_bound.Dependencies.v55588d36833b.CookMagyar.MajorArcArithmetic
public import Examples.nihargargava__systole_bound.Dependencies.v55588d36833b.CookMagyar.CubicResidueAbel
@[expose] public section
open Finset MeasureTheory
open scoped BigOperators
namespace SystolicGrowth
namespace CookMagyarMajorArc
open CookMagyarCircle CookMagyarArcs CookMagyarFiniteFourier
/-! # The all-residue complete cubic model -/
/-- The complete cubic sum includes *all* residues, not only units. -/
noncomputable def allResidueCubicExponentialSum
    (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ r : ZMod q, standardAdditiveCharacter (a * cubicResidue r)
private theorem cubicUnweightedResidueClassSum_eq_subtype
    (q : ℕ) [NeZero q] (r : ZMod q) (beta : ℝ) (N : ℕ) :
    cubicUnweightedResidueClassSum q r.val beta N =
      ∑ x : {x : Fin (N + 1) // ((x : ℕ) : ZMod q) = r},
        addChar beta (primeCubic (x : ℕ)) := by
  classical
  let p : Fin (N + 1) → Prop := fun x => ((x : ℕ) : ZMod q) = r
  have hfilter :
      (∑ x : {x : Fin (N + 1) // p x},
        addChar beta (primeCubic (x : ℕ))) =
      ∑ x ∈ (Finset.univ : Finset (Fin (N + 1))).filter p,
        addChar beta (primeCubic (x : ℕ)) := by
    simpa using (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (Fin (N + 1)))) (p := p)
      (fun x => addChar beta (primeCubic (x : ℕ))))
  rw [hfilter, Finset.sum_filter]
  unfold cubicUnweightedResidueClassSum
  rw [← Nat.range_succ_eq_Icc_zero]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k ≡ r.val [MOD q] then
      addChar beta (primeCubic k) else 0) (N + 1)]
  apply Finset.sum_congr rfl
  intro x _
  have hp : ((x : ℕ) : ZMod q) = r ↔ (x : ℕ) ≡ r.val [MOD q] := by
    constructor
    · intro h
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      exact h.trans (ZMod.natCast_zmod_val r).symm
    · intro h
      exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr h).trans
        (ZMod.natCast_zmod_val r)
  by_cases hx : (x : ℕ) ≡ r.val [MOD q]
  · simp [hp.mpr hx, hx]
  · simp [hp.not.mpr hx, hx]
/-- Exact decomposition of the ordinary cubic sum into all residue
classes at a rational center. -/
theorem cubicUnweightedExpSum_rationalCenter_add
    (q a N : ℕ) [NeZero q] (_hq : 0 < q) (beta : ℝ) :
    cubicUnweightedExpSum (rationalCenter a q + beta) N =
      ∑ r : ZMod q,
        standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassSum q r.val beta N := by
  classical
  rw [cubicUnweightedExpSum_eq_finSum]
  rw [← Fintype.sum_fiberwise
    (fun x : Fin (N + 1) => ((x : ℕ) : ZMod q))
    (fun x : Fin (N + 1) =>
      addChar (rationalCenter a q + beta) (primeCubic (x : ℕ)))]
  apply Finset.sum_congr rfl
  intro r _
  rw [cubicUnweightedResidueClassSum_eq_subtype q r beta N,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [addChar_add_real, addChar_rationalCenter]
  have hres :
      ((primeCubic (x : ℕ) : ℕ) : ZMod q) = cubicResidue r := by
    rw [cast_primeCubic_zmod]
    exact congrArg cubicResidue x.property
  rw [hres]
/-- Every all-residue class has the same uniform-density model, so their
main terms recombine into the complete sum. -/
theorem sum_allResidueCubicModels_eq_complete
    (q a N : ℕ) [NeZero q] (_hq : 0 < q) (beta : ℝ) :
    (∑ r : ZMod q,
      standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
        cubicUnweightedResidueClassModel q beta N) =
      allResidueCubicExponentialSum q (a : ZMod q) *
        cubicUnweightedResidueClassModel q beta N := by
  unfold allResidueCubicExponentialSum
  rw [Finset.sum_mul]
/-- Elementary unweighted major-arc model, before replacing the finite
real cubic phase sum by its homogeneous integral. -/
theorem norm_cubicUnweightedExpSum_sub_allResidueModel_le
    (q a N : ℕ) [NeZero q] (hq : 0 < q) (hN : 0 < N) (beta : ℝ) :
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        allResidueCubicExponentialSum q (a : ZMod q) *
          cubicUnweightedResidueClassModel q beta N‖ ≤
      (q : ℝ) *
        (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
  classical
  rw [cubicUnweightedExpSum_rationalCenter_add q a N hq beta,
    ← sum_allResidueCubicModels_eq_complete q a N hq beta,
    ← Finset.sum_sub_distrib]
  have hnorm (r : ZMod q) :
      ‖standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassSum q r.val beta N -
        standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassModel q beta N‖ ≤
        1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)) := by
    rw [← mul_sub, norm_mul, AddChar.norm_apply, one_mul]
    exact norm_cubicUnweightedResidueClassSum_sub_model_le
      q r.val hq beta N hN
  calc
    ‖∑ r : ZMod q,
      (standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassSum q r.val beta N -
        standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
          cubicUnweightedResidueClassModel q beta N)‖ ≤
        ∑ r : ZMod q,
          ‖standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
              cubicUnweightedResidueClassSum q r.val beta N -
            standardAdditiveCharacter ((a : ZMod q) * cubicResidue r) *
              cubicUnweightedResidueClassModel q beta N‖ := norm_sum_le _ _
    _ ≤ ∑ _r : ZMod q,
          (1 + (N : ℝ) *
            (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
      exact Finset.sum_le_sum (fun r _ => hnorm r)
    _ = (q : ℝ) *
          (1 + (N : ℝ) *
            (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
      simp
      ring
end CookMagyarMajorArc
end SystolicGrowth
