import Examples.gmDevi__zeta2_7_9_lean.Dependencies.vd9600a014307.Zeta2Lean.Statements
import Examples.gmDevi__zeta2_7_9_lean.Dependencies.vd9600a014307.Zeta2Lean.Pair.Defs
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Zeta2Lean.Pair.Statements — one `Prop` per lemma of the pair blueprint

Every lemma of the pair proof is a `def Stmt_X : Prop` (or a `structure Stmt_X : Prop` with named
fields), in the namespace `Zeta2.Pair`.  Proof files `Zeta2Lean/Pair/Proofs/*.lean` prove them,
taking the statements they depend on as *hypotheses*; `Zeta2Lean/Pair/Assembly.lean` derives the
main theorem (complete, no gaps); `Zeta2Lean/Pair/Main.lean` wires everything together.

Reused from the `{7,9,11}` repository (namespace `Zeta2`, file `Zeta2Lean/Statements.lean`):
`PNT_Stmt` (proved in `Zeta2Lean/Cited/PNT.lean`), `Stmt_JConv`, `Stmt_Translation`,
`Stmt_Criterion`, `Stmt_Delta`, `Stmt_DeltaFun` and their proof files
`Zeta2Lean/Proofs/{JConvergence, Translation, Criterion, DeltaCalculus, DeltaFunctions}.lean`.

Kinds of statements here (all are proved):
* **routine** (proof files with `gap = ''`): `Stmt_GenLinearForm`, `Stmt_PF`, `Stmt_CoeffVanish`,
  `Stmt_L1`, `Stmt_IntegrandTaylor`, `Stmt_CrudeInt`, and `Stmt_Valuation` (GAP 4: the Lai/Sprang
  Δ-calculus bound).  `Pair/Main.lean` uses their proofs.
* **the three gap statements** `Stmt_Growth` (GAP 1), `Stmt_Denominators` (GAP 2),
  `Stmt_Nonvanishing` (GAP 3), proved for configuration E in `Pair/Proofs/Growth.lean`,
  `Denominators.lean` and `Nonvanishing.lean`.  They are parametrised by a configuration
  `cfg : Config` and by the rates `g`, `δ`, and stated in exactly the form `main_of_stmts`
  consumes; the margin condition is `g + δ < 12 log 2`.

Normalisation reminder: `R_n` carries **no** power of `2`; `ρ₀, Z₇, Z₉` have 2-adic denominators of
size `≈ 2^{12n}`, `v₂(S_n) ≈ 12 n`, and only the *odd part* `D · ‖D‖₂` of a common denominator `D`
enters the margin.
-/
set_option linter.style.longLine false
open Filter Topology Finset PowerSeries
noncomputable section
namespace Zeta2.Pair
/-! ## The main statement -/
structure Stmt_PF : Prop where
  poly : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → Rnum n h = PFpoly n h
  series : ∀ (n : ℕ) (h : Fin 6 → ℤ) (y : ℚ), Admissible n h → (∀ j ≤ n, y + (j : ℚ) ≠ 0) →
    Rser n h y =
      ∑ i ∈ Icc (1 : ℕ) 6, ∑ k ∈ range (n + 1), C (rcoef n h i k) * ((C (y + k) + X) ^ i)⁻¹
/-- **Parity lemma and vanishing sums**: `r_{i,n-k} = (-1)^{i+1} r_{i,k}`
(from `R_n(-t-n) = -R_n(t)`;
each shifted factor `(t+1/2-h)_{n+2h}` is individually symmetric), `c₁ = 0` (`deg R_n = -5`) and
`c_i = 0` for even `i`. -/
structure Stmt_CoeffVanish : Prop where
  symm : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ∀ i k : ℕ, k ≤ n →
    rcoef n h i (n - k) = (-1) ^ (i + 1) * rcoef n h i k
  c1 : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → csum n h 1 = 0
  ceven : ∀ (n : ℕ) (h : Fin 6 → ℤ), Admissible n h → ∀ i : ℕ, Even i → csum n h i = 0
def Stmt_Growth (cfg : Config) (g : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
    |(rho0 (cfg.n m) (cfg.h m) : ℝ)| ≤ Real.exp ((g + ε) * cfg.n m) ∧
      |(Z7 (cfg.n m) (cfg.h m) : ℝ)| ≤ Real.exp ((g + ε) * cfg.n m) ∧
      |(Z9 (cfg.n m) (cfg.h m) : ℝ)| ≤ Real.exp ((g + ε) * cfg.n m)
end Zeta2.Pair
end
