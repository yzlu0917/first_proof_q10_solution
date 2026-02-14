## Disclaimer (for Problem 10 of https://arxiv.org/pdf/2602.05192)

The solution and verify workflow for this problem in this repository were completed using GPT Pro and Codex (gpt-5.3-codex). Workflow used: GPT Pro and Codex were prompted with the problem statement and repository constraints, then iteratively generated, edited, and checked the Lean code until compilation and automated checks passed. No human mathematical guidance was provided, and the maintainer is not a professional mathematician. At present, we can only guarantee that Lean compilation passes and that AI-based semantic checks pass. There are no known issues at this time, but it cannot be guaranteed to be completely error-free.

# AutoProof Q10: Mathematical Overview and Audit Route

This README is the project-level overview for `autoproof/`.
It is written for mathematicians who want a clear answer to three questions:

1. What is the exact mathematical statement being formalized?
2. Under which assumptions is each conclusion valid?
3. Where is each claim encoded in Lean?

For concept definitions plus proof navigation, use:
- `autoproof/Q10/Mainline/TexConceptsAndProofRoute.README.md`

For line-by-line proof reading, use:
- `autoproof/Q10/Mainline/TexAligned.README.md`

---

## 1. Problem Scope (`q10.tex`)

Target source:
- `autoproof/q10.tex`

The project formalizes the mode-\(k\) RKHS-regularized CP subproblem with missing entries, in the standard observed-data setting:

\[
\Big[(Z\otimes K)^\top S S^\top (Z\otimes K) + \lambda(I_r\otimes K)\Big]\mathrm{vec}(W)
= (I_r\otimes K)\mathrm{vec}(B).
\]

Interpretation:
- \(K\): kernel matrix for the RKHS-constrained mode.
- \(Z\): fixed design/features induced by all other modes.
- \(S\): observation selector (only observed entries are used).
- \(W\): unknown mode-\(k\) coefficient matrix.
- \(B\): observed-data MTTKRP target, locked to observations (not free).

Computational requirement in `q10.tex`:
- avoid explicit \(O(N)\)-scale construction;
- use matrix-free and observed-sparse computation;
- provide PCG/preconditioned guarantees and complexity formulas.

---

## 2. One-to-One tex-to-Lean Dictionary

Core files for this dictionary:
- `autoproof/Q10/Core/Operators/ProblemModel.lean`
- `autoproof/Q10/Core/Operators/ObservedOps.lean`

| tex symbol or statement | Lean object | Where in Lean | Meaning of the correspondence |
|---|---|---|---|
| Tensor with missing entries (observed-only semantics) | `Ω`, `vals` | `ProblemModel.lean` (`TexObservedProblem`) | Instead of storing full tensor `T`, Lean stores observed coordinates (`Ω`) and observed values (`vals`). |
| Observation index map \(\Omega\) | `Ω : Fin q → Fin M × Fin n` | `ProblemModel.lean` (`Problem`/`TexProblem`) | The `t`-th observed sample points to one matrix coordinate (column,row) in mode-\(k\) unfolding. |
| Observation selector \(S\) | `selectionMatrix Ω` | `ObservedOps.lean` | Algebraic selection matrix induced by `Ω`; this is the Lean realization of the tex selector. |
| Observed data vector on selected entries | `gather Ω X` | `ObservedOps.lean` | Pulls values from matrix `X` at observed indices only. |
| Scatter back to matrix with zeros elsewhere | `scatter Ω u` | `ObservedOps.lean` | Rebuilds an observed-only matrix from `q` observed values. |
| Kernel matrix \(K\) | `K : Matrix (Fin n) (Fin n) Real` | `ProblemModel.lean` (`Problem`) | RKHS geometry is encoded by the kernel matrix object `K`. |
| Fixed factor design \(Z\) (from modes other than \(k\)) | `Z : Matrix (Fin M) (Fin r) Real` | `ProblemModel.lean` (`Problem`) | Encodes the fixed multi-mode information used in the mode-\(k\) subproblem. |
| Unknown mode-\(k\) variable \(W\) | `W : Matrix (Fin n) (Fin r) Real` | arguments of `applyDenseVec`/`applyMatrixFree*` | Lean solves for `W`; the mode-\(k\) factor is represented by kernelized form `A_k = K * W`. |
| Regularization \(\lambda\) | `lam : Real` | `ProblemModel.lean` (`Problem`) | Same scalar regularization parameter as in tex. |
| \(B = TZ\) (observed semantics) | `sparseMTTKRP Ω vals Z` | `ObservedOps.lean` | Computes `B` directly from observations; no dense `T` is formed. |
| “\(B\) is not free” requirement | `hBobs : B = sparseMTTKRP Ω vals Z` | `ProblemModel.lean` (`TexObservedProblem`) | Hard-locks RHS semantics to observed data. |
| RHS \((I_r \otimes K)\mathrm{vec}(B)\) | `rhsVec K B` | `ObservedOps.lean` | Abstract RHS formula in vector form. |
| Observed-locked RHS | `rhsFromObserved K Ω vals Z` | `ObservedOps.lean` | Same RHS, but directly built from observed data pipeline. |
| Full dense linear operator in tex equation | `applyDenseVec K Z Ω lam W.vec` | `ObservedOps.lean` | Lean encoding of the left-hand side matrix acting on `vec(W)`. |
| Matrix-free equivalent operator | `applyMatrixFreeSparse K Z Ω lam W` | `ObservedOps.lean` | Same operator value as dense form, computed without materializing the huge matrix. |
| CSR/bucket implementation | `applyMatrixFreeBucketed K Z Ω ...` | `ObservedOps.lean` | Implementation-level reorganization of sparse matvec; theorem-proved equivalent. |
| Online row generation (no explicit large `Z`) | `obsRowFromFactors`, `factorsGenerateObservedRows` | `ObservedOps.lean` | Builds observed rows from factor providers and proves equivalence to explicit-`Z` formulas. |
| PSD kernel fallback \(K+\nu I\), \(\nu>0\) | `withKernelShift` | `ProblemModel.lean` (`TexObservedProblem.withKernelShift`) | Converts PSD branch into SPD branch for PCG certificates. |

This table is the direct tex-to-Lean bridge at project overview level; detailed expansion is in `autoproof/Q10/Mainline/TexConceptsAndProofRoute.README.md`.

---

## 3. What Is Proved

The formal package proves:

1. Dense system and matrix-free sparse action are equivalent.
2. RHS is locked to observed data (`B = sparseMTTKRP Ω vals Z`), not an unconstrained symbol.
3. Sparse and bucket/CSR implementations are operator-equivalent.
4. Online observed-row generation from factors is equivalent to explicit-`Z` formulas.
5. Preconditioner actions are correct; preconditioner-2 has a closed form.
6. Spectral interval assumptions imply PCG residual bounds.
7. Cost models are explicit and \(N\)-free at the theorem interface.
8. PSD kernels are handled via an explicit shifted branch \(K+\nu I\), \(\nu>0\).

---

## 4. Main Theorem Map (Claim -> Lean Evidence)

Human-aligned step chain:
- file: `autoproof/Q10/Mainline/TexAligned.lean`
- key names:
  - `q10_tex_step1_system_equivalence`
  - `q10_tex_step2_rhs_from_observations`
  - `q10_tex_step3_matrix_vector_pipeline`
  - `q10_tex_step4_bucketed_matvec_and_cost`
  - `q10_tex_step5_online_rows_equivalence`
  - `q10_tex_step6_preconditioners`
  - `q10_tex_step7_pcg_residual_from_spectrum`
  - `q10_tex_step8_complexity_formulas`
  - `q10_tex_step9_psd_to_shift_core`
  - `q10_tex_step10_default_core` through `q10_tex_step17_full_default_package`

Source-level integrated certificates:
- file: `autoproof/Q10/Mainline/TexAnswer.lean`
- key names:
  - `q10_tex_complete_solution_certificate`
  - `q10_tex_complete_solution_certificate_closed_loop_online`
  - `q10_tex_complete_solution_certificate_fully_closed_full_dway`
  - `q10_tex_complete_solution_certificate_fully_closed_minimal_spectral`
  - `q10_tex_psd_to_shifted_pcg_certificate`
  - `q10_tex_precond2_choice_strong_branch_observed`

System-equivalence bridge used by the chain:
- file: `autoproof/Q10/KernelOps/SystemEquiv.lean`
- key name: `q10_mainline_system_equiv_matrixFree`

---

## 5. User-Facing Entry Points

Top-level exports:
- file: `autoproof/Q10.lean`
- default final answer: `q10_tex_final_answer`
- full d-way interface: `q10_tex_final_answer_full_dway`
- PSD-shift closure entry: `q10_tex_final_answer_shifted_pcg`
- human-aligned overview entry: `q10_tex_final_answer_human_aligned`

Mainline exports:
- file: `autoproof/Q10/Mainline.lean`
- default delivery entry: `q10_mainline_delivery`
- human-aligned delivery entry: `q10_mainline_human_aligned_delivery`

---

## 6. Assumptions and Branches

SPD branch (direct PCG/preconditioner inversion certificates):
- used where inverse-action proofs are mathematically required.

PSD branch (tex-style kernel assumption):
- handled by explicit shift \(K \mapsto K + \nu I\), \(\nu > 0\).
- core objects:
  - `withKernelShift` in `ProblemModel.lean`
  - `q10_tex_psd_to_shifted_pcg_certificate` in `TexAnswer.lean`

Optional stronger preconditioner-2 comparison branch:
- theorem: `q10_tex_precond2_choice_strong_branch_observed`
- gives strict Loewner/\(\kappa\)/rate comparison under stronger assumptions.

---

## 7. Recommended Reading Order

Three-layer route for mathematicians:

1. Concept layer:
   - `autoproof/Q10/Mainline/TexConceptsAndProofRoute.README.md`
   - read symbols, structures, and why each object exists.

2. Proof-chain layer:
   - `autoproof/Q10/Mainline/TexAligned.README.md`
   - read Step1-17 and line-by-line proof meaning.

3. Source layer:
   - `autoproof/Q10/Mainline/TexAligned.lean`
   - `autoproof/Q10/Mainline/TexAnswer.lean`
   - inspect exact theorem statements and packaging objects.

---

## 8. Verification Commands

Run from `/root/mathlib4`:

```bash
lake build autoproof.Q10.Mainline
lake build autoproof.Q10
rg -n "sorry|admit|axiom" autoproof/Q10
```

Optional focused checks:

```bash
lake build autoproof.Q10.TraceAndRates.RateTheory.PreconditionedKrylovInterval
lake build autoproof.Q10.SolutionClosure.StrictLoewner
```

---

## 9. Repository Layout

- `autoproof/q10.tex`: original problem statement.
- `autoproof/Q10/Core`: operators, preconditioners, costs, algorithmic primitives.
- `autoproof/Q10/KernelOps`: system-equivalence bridge.
- `autoproof/Q10/Preconditioners`: closed forms and action bridges.
- `autoproof/Q10/TraceAndRates`: residual/rate/cost theory.
- `autoproof/Q10/Mainline`: integrated theorem packaging and readable step chain.
- `autoproof/Q10.lean`: top-level user-facing aliases.
