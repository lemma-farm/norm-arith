module
/-
Directed potentials for two probability laws and a compatibility relation.
Two changes against the `Phi` of the support layer:

* **Directed**: the row law `μ` and the column law `ν` are different PMFs;
  the bad degree of a row point is measured against the column law. The
  support layer's `Phi α μ R` is the diagonal case `ν = μ`.
* **Safe at `q = 1`**: without reflexivity-on-support there is no guarantee
  that bad degrees stay below one, and `Real.rpow`'s junk value `0 ^ (-α) = 0`
  would silently zero out exactly the points that must contribute the most. The
  `ℝ≥0∞`-valued weight `phiE` is `⊤` at `q ≥ 1`, so finite potentials really
  do force `q < 1` wherever the row law charges, and the failure bound
  `𝔼 q ≤ Φ` holds unconditionally.

The `badInd` normal form `q_ν(z) = ∑' y, ν y · 𝟙[z ⋡ y]` makes the bad degree
linear in the column law, which is how the kernel mixture enters the step.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Process.Sim
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Support.Potential
@[expose] public section
namespace GraphMarkovMatching
open GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {X : Type u}
/-! ### The safe weight `phiE` -/
/-- The `ℝ≥0∞`-valued potential weight: `φ_α` below `1`, `⊤` from `1` on. -/
noncomputable def phiE (α t : ℝ) : ℝ≥0∞ :=
  if t < 1 then ENNReal.ofReal (phi α t) else ⊤
lemma phiE_of_lt {α t : ℝ} (h : t < 1) : phiE α t = ENNReal.ofReal (phi α t) :=
  ite_eq_left h
@[simp] lemma phiE_one (α : ℝ) : phiE α 1 = ⊤ := ite_eq_right (lt_irrefl 1)
end GraphMarkovMatching
