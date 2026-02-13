# q10 Concept-Proof Overview (For Mathematical Readers)

This document provides two things:
1. It first clarifies the mathematical objects in `autoproof/q10.tex` and the key `def/structure` objects actually used later in Lean.
2. It then gives a verifiable proof-reading route explaining why the conclusion is trustworthy.

This document does not replace a line-by-line commentary document; it is the main entry point for "read the concepts first, then read the proof".
For finer-grained proof reading (by Step and by line-level proof actions), use
`autoproof/Q10/Mainline/TexAligned.README.md`.

---

## 0. Document Positioning: The Role of `TexAligned`

`TexAligned` is not a complete modeling document, but it is the backbone of the proof chain.

- Why it is not complete: `TexAligned.lean` mainly handles alignment and packaging for Step1-17; it does not unfold the modeling semantics of every mathematical object from scratch.
- Where completeness comes from: it is sufficient to cover whether the proof chain is closed (system equivalence, RHS locking, preconditioning, residual bounds, complexity, PSD fallback, final delivery).
- Recommended reading order:
1. Read this document first (concepts/definitions).
2. Then read `autoproof/Q10/Mainline/TexAligned.README.md` (more detailed proof interpretation, including line-by-line explanation).
3. Cross-check with `autoproof/Q10/Mainline/TexAligned.lean` (proof-chain source code).
4. If you need root causes, return to the `Core` files for definitions and bridge theorems.

---

## 1. How `q10.tex` Is Actually Modeled in Lean

The core of `autoproof/q10.tex:1-38` is:
1. The original problem comes from a CP subproblem of an incompletely observed tensor (fix all factors except mode-k, and solve the mode-k factor).
2. mode-k is kernelized/RKHS mode, with `A_k = K W`, where the unknown is `W`.
3. The linear system is written in Kronecker+selection form.
4. Use preconditioned PCG, avoid any `O(N)`-scale computation, and provide complexity conclusions.

In Lean, this is compressed into a "finite-dimensional computable model":
1. It does not directly operate on the full tensor `T`; it uses observation indices `Ω` and observed values `vals`.
2. It does not explicitly represent an infinite-dimensional function space; RKHS information is carried by the kernel matrix `K`.
3. `Z` carries the Khatri-Rao combination information of factors outside mode-k.
4. `Problem/TexProblem/TexObservedProblem` turn the assumptions in the statement into checkable objects.

This explains why you do not see full tex narrative sentences inside `TexAligned`: the corresponding semantics have already been pushed down into the object-definition layer.

---

## 2. Full One-to-One Mapping from `q10.tex` to Lean (Audit Map First, Details Next)

This section is organized like an "auditable ledger": first a master index, then itemized details.  
You can use it like a map: locate the ID first, then jump to the corresponding definition and theorem.

### 2.0 Master Audit Index (Map)

| ID | Key sentence in `q10.tex` | Minimal Lean object set | Definition-layer location | Mainline-layer location |
|---|---|---|---|---|
| T1 | "`d`-way tensor … data is unaligned (missing entries)" | `Ω`, `vals`, `TexObservedProblem` | `ProblemModel.lean:26-33`, `ObservedOps.lean:16-25` | Step2 `q10_tex_step2_rhs_from_observations` |
| T2 | "CP decomposition of rank `r` … infinite-dimensional … RKHS" | `r`, `Z`, `K`, `K.PosSemidef/PosDef` | `ProblemModel.lean:17-22`, `ObservedOps.lean:339-358` | Step1, Step5, Step6, Step7 |
| T3 | "alternating optimization … mode-`k` subproblem … solve for `A_k`" | `W` (unknown), `A_k = K * W` (implemented in the operator) | `ObservedOps.lean:189-207` | Step1 `q10_tex_step1_system_equivalence` |
| T4 | "`N,n,M,q`, `q \ll N`" | parameters `n M q`, environment scale `n * M`, `hScale` | `TexAnswer.lean:1352-1362` | Step10/16/17 packaging |
| T5 | "`T` unfold, `vec`, `S`, `S^T vec(T)`" | `scatter`, `.vec`, `selectionMatrix`, `gather` | `ObservedOps.lean:16-25` | Step3 pipeline equivalence |
| T6 | "`Z` Khatri-Rao, `B = TZ`" | `Z`, `sparseMTTKRP`, `hBobs` | `ObservedOps.lean:83-87`, `ProblemModel.lean:33` | Step2 RHS locking |
| T7 | "Main linear system equation" | `applyDenseVec = rhsVec` | `ObservedOps.lean:189`, `ObservedOps.lean:661` | Step1 system equivalence |
| T8 | "PCG + preconditioner + matvec + complexity + avoid `O(N)`" | `applyMatrixFreeSparse/Observed`, preconditioners, cost defs | `ObservedOps.lean:579-664`, `CostAndPSD.lean` | Step3-8, Step15-16 |

How to audit:
1. Find which ID (T1-T8) the statement sentence belongs to.
2. Open the "definition-layer location" to confirm the object definition.
3. Open the "mainline-layer location" to confirm how the object enters the conclusion.
4. If both sides match, that audit item passes.

### 2.1 T1: How `d`-way tensor and `unaligned` land in Lean

Original text:
> Given a $d$-way tensor $\mathcal{T} \in \mathbb{R}^{n_1 \times n_2 \times \cdots \times n_d}$
> such that the data is unaligned (meaning the tensor $\mathcal{T}$ has missing entries),

Lean translation (object layer):
1. It does not store full `\mathcal{T}` directly; it stores observation-coordinate function `Ω : Fin q → Fin M × Fin n`.  
2. It stores observation-value function `vals : Fin q → Real`.  
3. It packages both with system parameters into `TexObservedProblem`. Source: `autoproof/Q10/Core/Operators/ProblemModel.lean:31-33`.

Why this is equivalent to "unaligned / missing entries":
1. Entries outside the `q` observation points never enter the data structure, so semantically they are "missing".  
2. When `scatter Ω vals` writes observed values back into an `n×M` matrix, unobserved locations are automatically `0` (`autoproof/Q10/Core/Operators/ObservedOps.lean:24-25`).  
3. `hOmegaInj : Function.Injective Ω` is not written literally as `S^T S = I_q`, but there are equivalent theorems:  
`selectionMatrix_transpose_mul_self_eq_one_iff_injective` (`ObservedOps.lean:73-76`) and  
`TexProblem.selection_subidentity_iff` (`ProblemModel.lean:79-82`).

Role in the proof chain:
1. Step2 writes the premise as `P : TexObservedProblem n M r q`, which is equivalent to injecting "observation semantics + RHS locking semantics" in one shot.  
2. Corresponding theorem: `q10_tex_step2_rhs_from_observations` (`autoproof/Q10/Mainline/TexAligned.lean:31-34`).

### 2.2 T2: CP decomposition and RKHS constraints map to which objects

Original text:
> we consider the problem of computing a CP decomposition of rank $r$ where some modes are infinite-dimensional and constrained to be in a Reproducing Kernel Hilbert Space (RKHS).

Lean translation (object layer):
1. CP rank is explicit parameter `r`.  
2. After fixing other modes, Khatri-Rao aggregation is written as `Z : Matrix (Fin M) (Fin r) Real` (`ProblemModel.lean:18`).  
3. RKHS constraints are represented by kernel matrix `K : Matrix (Fin n) (Fin n) Real` (`ProblemModel.lean:17`), used later via `K.PosSemidef`/`K.PosDef` in theorems.

Why this indeed expresses CP+RKHS:
1. Information from the "other modes" in CP enters the mode-`k` subproblem only through `Z`.  
2. The function-space constraint for mode-`k` is not modeled as an explicit infinite-dimensional space in Lean; instead, algebraic properties of `K` are used in operators.  
3. In the online version, `obsRowFromFactors` defines each observed row as a cross-mode product:  
`obsRowFromFactors F t l = ∏ m, F m t l` (`ObservedOps.lean:343-344`), consistent with Khatri-Rao row definition.

Role in the proof chain:
1. Step1 defines the system operator using `K,Z`.  
2. Step5 proves "online row generation = explicit `Z` row" using `factorsGenerateObservedRows`.  
3. Step6/7 use positive-definiteness and spectral intervals of `K` to produce preconditioning and residual certificates.

### 2.3 T3: The alternating mode-`k` subproblem is "fix `Z`, solve `W`" in Lean

Original text:
> We want to solve this using an alternating optimization approach, and our question is focused on the mode-$k$ subproblem for an infinite-dimensional mode.
> For the subproblem, then CP factor matrices
> $A_1, \dots, A_{k-1}, A_{k+1}, \dots, A_d$ are fixed, and we are solving for $A_k$.

Lean translation (object layer):
1. "Other factors fixed" means `Z` is fixed as an input parameter in Lean.  
2. The unknown is `W : Matrix (Fin n) (Fin r) Real`.  
3. The effect of `A_k = K W` appears in system action: the left operator acts on `W`, and the right target is `K * B`.

Mainline theorem (directly auditable):
```lean
theorem q10_tex_step1_system_equivalence
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real)
    (hK : Kᵀ = K)
    (W B : Matrix (Fin n) (Fin r) Real) :
    applyDenseVec K Z Ω lam W.vec = rhsVec K B
      ↔ applyMatrixFreeSparse K Z Ω lam W = K * B
```

Why this sentence is exactly the mode-`k` subproblem in the statement:
1. The left side is the vectorized form of the tex main system.  
2. The right side is the matrix-free matrix form of the same system.  
3. `W` is the only unknown; `K,Z,Ω,lam` are all fixed inputs.

Role in the proof chain:
1. Step1 is the certificate for "correctness of system rewriting".  
2. Step2 further locks `B` into observation semantics `sparseMTTKRP`, matching the statement's RHS source.

### 2.4 T4-T6: Exact landing points of notation block `N,n,M,q,T,vec,S,Z,B`

Original text (dimensions and observation scale):
> Let $N = \prod_i n_i$ denote the product of all sizes.
> Let $n \equiv n_k$ be the size of mode $k$, let
> $M = \prod_{i\neq k} n_i$ be the product of all dimensions except $k$, and assume $n \ll M$.
> Since the data are unaligned, this means only a subset of $\mathcal{T}$'s entries are observed, and we let $q \ll N$ denote the number of observed entries.

Original text (`T`, `vec`, `S`):
> We let $T \in \mathbb{R}^{n \times M}$ denote the mode-$k$ unfolding of the tensor $\mathcal{T}$ with all missing entries set to zero.
> The $\operatorname{vec}$ operations creates a vector from a matrix by stacking its columns,
> and we let $S \in \mathbb{R}^{N \times q}$ denote the selection matrix ...

Original text (`Z` and `B`):
> We let $Z = A_d \odot \cdots \odot A_{k+1} \odot A_{k-1} \odot \cdots \odot A_1 \in \mathbb{R}^{M \times r}$ ...
> We let $B = TZ$ denote the MTTKRP ...

Entry ledger from symbols to Lean:

| tex symbol | Lean object | Location | Explanation |
|---|---|---|---|
| `N` | `n * M` (environment-scale role) | `TexAnswer.lean:1352-1362` | No explicit full-`N` object is built, but complexity assumptions use `n*M` for the same semantic role. |
| `n, M, q` | type parameters `n M q` | all main theorem parameters | mode dimension, product of other dimensions, and observation count all become checkable parameters. |
| `T` (missing entries set to 0) | `scatter Ω vals` | `ObservedOps.lean:24-25` | Values are written only at observed positions; others are automatically 0. |
| `\operatorname{vec}(X)` | `X.vec` | multiple places in `ObservedOps.lean` | Same vectorization convention. |
| `S` | `selectionMatrix Ω` | `ObservedOps.lean:16-17` | One 1 per column, selecting observed coordinates. |
| `S^T vec(T)` | `gather Ω X` | `ObservedOps.lean:20-21` | Extract observed entries from vectorized matrix. |
| `Z` | `Z : Matrix (Fin M) (Fin r) Real` | `ProblemModel.lean:18` | Khatri-Rao aggregation of factors in other modes. |
| `B=TZ` | `sparseMTTKRP Ω vals Z` + `hBobs` | `ObservedOps.lean:83-87`, `ProblemModel.lean:33` | RHS is no longer a free variable; it is a function of observations and `Z`. |

Role in the proof chain:
1. Step3 aligns the `gather/scatter` pipeline with sparse implementation.  
2. Step2 fixes the semantics of `B=TZ` as `hBobs`, and rewrites `rhsVec` as `rhsFromObserved`.

### 2.5 T7: Correspondence between the main equation and theorem parameter block

Original text:
> The system to be solved is
> \[
> \left[(Z \otimes K)^T S S^T (Z \otimes K) + \lambda (I_r \otimes K)\right]\operatorname{vec}(W)
> = (I_r \otimes K)\operatorname{vec}(B).
> \]
> Here, $I_r$ denotes the $r \times r$ identity matrix.
> This is a system of size $nr \times nr$.

Lean one-to-one correspondence:
1. Left matrix-vector product corresponds to `applyDenseVec K Z Ω lam W.vec` (`ObservedOps.lean:189-195`).  
2. Right side corresponds to `rhsVec K B` (`ObservedOps.lean:661-664`).  
3. The full equation corresponds to the first half of Step1:  
`applyDenseVec K Z Ω lam W.vec = rhsVec K B` (`TexAligned.lean:24`).

Parameter audit table ("statement element -> theorem parameter"):

| tex element | Lean parameter/object | Location |
|---|---|---|
| `K` | `(K : Matrix (Fin n) (Fin n) Real)` | `TexAligned.lean:18` |
| `Z` | `(Z : Matrix (Fin M) (Fin r) Real)` | `TexAligned.lean:19` |
| `S` (determined by observations) | `(Ω : Fin q → Fin M × Fin n)` | `TexAligned.lean:20` |
| `\lambda` | `(lam : Real)` | `TexAligned.lean:21` |
| `W` | `(W : Matrix (Fin n) (Fin r) Real)` | `TexAligned.lean:23` |
| `B` | `(B : Matrix (Fin n) (Fin r) Real)` | `TexAligned.lean:23` |
| symmetry constraint | `(hK : Kᵀ = K)` | `TexAligned.lean:22` |

Why these parameters are exactly right:  
`K,Z,Ω,lam` fully determine the left operator, `W` is the unknown, `B` determines the RHS, and `hK` is the structural assumption needed by operator theory.  
Adding `vals,hBobs` from `TexObservedProblem` yields the closed version of the statement: "RHS generated from observations".

### 2.6 T8: How the task sentences (PCG/preconditioner/matvec/complexity) close the loop

Original text:
> Using a standard linear solver costs $O(n^3 r^3)$, and explicitly forming the matrix is an additional expense.
> Explain how an iterative preconditioned conjugate gradient linear solver can be used to solve this problem more efficiently.
> Explain the method and choice of preconditioner.
> Explain in detail how the matrix-vector products are computed and why this works.
> Provide complexity analysis.
> We assume $n,r < q \ll N$. Avoid any computation of order $N$.

Mainline closure ledger:
1. Step1: `q10_tex_step1_system_equivalence`, proving dense system is equivalent to matrix-free sparse system.  
2. Step3/4/5: proving sparse, bucket, and online matvec implementations are all consistent with the same baseline operator.  
3. Step6: `q10_tex_step6_preconditioners`, giving correctness of two preconditioners and the closed form of precond2.  
4. Step7: `q10_tex_step7_pcg_residual_from_spectrum`, turning spectral-interval assumptions into PCG residual upper-bound certificates.  
5. Step8: `q10_tex_step8_complexity_formulas`, giving explicit complexity formulas.  
6. Step16: adding the sparse main-cost bridge, connecting implementation cost and theoretical cost.

Why this satisfies "avoid any computation of order `N`":
1. Core operators are `applyMatrixFreeSparse` and `applyMatrixFreeObserved`, which only do `q`-level observation summation and `K`-multiplications (`ObservedOps.lean:579-587`, `487-495`).  
2. Cost formulas are explicitly written using `n,r,q,dObs`, with no full-`N` traversal term.  
3. `hScale : n < q ∧ r < q ∧ q < n * M` provides size-range assumptions in the default delivery interface (`TexAnswer.lean:1357`).

---

## 3. Detailed Key `structure` Objects (Structure Ledger)

### 3.0 Structure Master Index (Map)

| ID | Structure | What this ledger records | Definition location | Which mainline Steps it enters directly |
|---|---|---|---|---|
| S1 | `Problem` | Minimal inputs of the mode-`k` subproblem: `K,Z,Ω,lam,B,hK` | `ProblemModel.lean:16-22` | Step1, Step3, Step4, Step5, Step6 |
| S2 | `TexProblem` | Adds selection-matrix structural constraint `hOmegaInj` on top of `Problem` | `ProblemModel.lean:26-27` | Step5, Step6 |
| S3 | `TexObservedProblem` | Adds observed values and RHS lock `vals,hBobs` on top of `TexProblem` | `ProblemModel.lean:31-33` | Step2, Step7, Step9 |
| S4 | `TexObservedProblem.withKernelShift` | Turns a PSD kernel into an SPD kernel for the same problem object | `ProblemModel.lean:36-53` | Step9, Step12 |

Audit usage:  
Whenever you see `P : ...` in theorem premises, first locate which layer it is in this table (`S1-S4`), then check which additional usable facts it carries.

### 3.1 S1: `Problem` is the "base ledger"

Lean definition location: `autoproof/Q10/Core/Operators/ProblemModel.lean:16-22`.  
Field meanings:
1. `K`: kernel matrix of mode-`k`, carrying RKHS geometry.  
2. `Z`: the `M×r` Khatri-Rao aggregation matrix after fixing other modes.  
3. `Ω`: observation-coordinate selection function determining which entries are seen.  
4. `lam`: regularization coefficient `\lambda`.  
5. `B`: right-hand matrix (treated as abstract input at this base layer).  
6. `hK : Kᵀ = K`: symmetry premise ensuring later spectral/preconditioning arguments are valid.

Role in the proof chain:  
System equivalence in Step1, matvec pipeline in Step3-5, and preconditioner correctness in Step6 all require at least the `Problem` layer.

### 3.2 S2: `TexProblem` is the "statement-structure ledger"

Lean definition location: `autoproof/Q10/Core/Operators/ProblemModel.lean:26-27`.  
Added field:
`hOmegaInj : Function.Injective Ω`.

Mathematical meaning:  
This is not an "extra assumption"; it encodes the structural property of selection matrix `S` in tex as an index condition.  
Its relation with `S^T S = I_q` is theorem equivalence, not literal textual identity. Auditable basis:
1. `selectionMatrix_transpose_mul_self_eq_one_iff_injective`: `ObservedOps.lean:73-76`.  
2. `TexProblem.selection_subidentity_iff`: `ProblemModel.lean:79-82`.

Role in the proof chain:  
Step6 uses `P : TexProblem ...` for preconditioner-related conclusions; Step5 keeps statement semantics while connecting online row generation.

### 3.3 S3: `TexObservedProblem` is the "observation-closure ledger"

Lean definition location: `autoproof/Q10/Core/Operators/ProblemModel.lean:31-33`.  
Added fields:
1. `vals : Fin q → Real`: table of observed values.  
2. `hBobs : B = sparseMTTKRP Ω vals Z`: `B` is locked as the observation-generated result.

Mathematical meaning:  
`B` is no longer a free input; it is uniquely determined by observation data `(Ω, vals)` and fixed `Z`.  
This is exactly the checkable Lean version of tex's "`B = T Z` and `T` contains only observed entries".

Directly auditable bridge theorem:  
`TexObservedProblem.rhsVec_eq_rhsFromObserved` (`ProblemModel.lean:95-99`).  
It tells you that at the `S3` layer, RHS must be writable as observation semantics `rhsFromObserved`.

Role in the proof chain:  
Step2, Step7, and Step9 all use `P : TexObservedProblem ...`, because all three steps must rely on "RHS comes from observations" rather than arbitrary `B`.

### 3.4 S4: `withKernelShift` is the "PSD fallback ledger"

Lean definition location: `autoproof/Q10/Core/Operators/ProblemModel.lean:36-53`.  
The operation replaces `K` with `K + nu I`, while keeping `Z,Ω,vals,lam,B` unchanged.

Mathematical meaning:  
When `K` is only PSD and not strong enough for SPD, adding a nugget `nu > 0` pushes the system into the SPD range required by PCG theory.

Auditable basis:
`TexObservedProblem.withKernelShift_posDef_of_posSemidef` (`ProblemModel.lean:175`).  
It is the key theorem source for "PSD -> shifted SPD" in Step9.

Role in the proof chain:  
Step9 gives the core transition for the PSD case; Step12 connects this transition to the default delivery interface.

---

## 4. Detailed Key `def` Objects: Grouped by Computational Pipeline (Definition Ledger)

### 4.0 Definition Master Index (Map)

| ID | Definition group | Core objects | Definition-layer location | Which Steps it enters directly |
|---|---|---|---|---|
| D1 | Observation extraction/backfill | `selectionMatrix`, `gather`, `scatter` | `ObservedOps.lean:16-25` | Step3 |
| D2 | Observation RHS | `sparseMTTKRP`, `rhsFromObserved`, `rhsVec` | `ObservedOps.lean:83-97`, `661-664` | Step2 |
| D3 | System operators | `applyDenseVec`, `applyMatrixFree*` | `ObservedOps.lean:189-207`, `579-600` | Step1, Step3, Step4 |
| D4 | Online row generation | `ObsFactorProvider`, `obsRowFromFactors`, `factorsGenerateObservedRows`, `*Observed*` | `ObservedOps.lean:339-358`, `487-577` | Step5 |
| D5 | Preconditioning/residual | `gramMatrix`, `precond1/2*`, `pcgResidualNorm` | `BaseDefs.lean:16-18,53,86,112,539`, `Contraction.lean:101` | Step6, Step7 |
| D6 | Cost model | `matVecCost`, `applyMatrixFreeSparseCost`, `rhsFromObservedCost`, `applyMatrixFreeObservedOnlineCost` | `CostAndPSD.lean:18,149,170,174` | Step8, Step16 |

### 4.1 D1: Observation extraction and backfill

Definition location: `autoproof/Q10/Core/Operators/ObservedOps.lean:16-25`.

Mathematical semantics of the three definitions:
1. `selectionMatrix Ω`: column index is observation ID `t`, row index is coordinate `(j,i)`; it is `1` iff `Ω t = (j,i)`. This is tex selection matrix `S`.  
2. `gather Ω X = (selectionMatrix Ω)ᵀ *ᵥ X.vec`: extracts observed entries from vectorized `X`, equivalent to `S^T vec(X)`.  
3. `scatter Ω u`: writes vector `u` of length `q` back to an `n×M` matrix; unobserved locations are automatically zero-filled.

Auditable bridges:
`gather_apply` (`ObservedOps.lean:28-31`) gives the pointwise formula;  
`vec_scatter` (`ObservedOps.lean:40-41`) gives the exact relation after backfill then vectorization.

Role in the mainline:  
Step3's "Step-B/Step-C pipeline" proves equivalence around these three D1 definitions.

### 4.2 D2: RHS and MTTKRP

Definition locations:
1. `sparseMTTKRP`: `ObservedOps.lean:83-87`.  
2. `rhsFromObserved`: `ObservedOps.lean:91-96`.  
3. `rhsVec`: `ObservedOps.lean:661-664`.

Mathematical semantics:
1. `sparseMTTKRP Ω vals Z = (scatter Ω vals) * Z`, the sparse observed implementation of `B=TZ`.  
2. `rhsFromObserved` is the Kronecker form of `vec(K * sparseMTTKRP Ω vals Z)`.  
3. `rhsVec K B` is the unified interface for abstract RHS `vec(K * B)`.

Auditable bridges:
1. `rhsFromObserved_eq_vec` (`ObservedOps.lean:178-185`).  
2. `TexObservedProblem.rhsVec_eq_rhsFromObserved` (`ProblemModel.lean:95-99`).

Role in the mainline:  
Step2 performs "RHS locking" on D2: from abstract `rhsVec` down to observation semantics `rhsFromObserved`.

### 4.3 D3: System operators (dense and matrix-free)

Definition locations:
1. `applyDenseVec`: `ObservedOps.lean:189-195`.  
2. `applyMatrixFree`: `ObservedOps.lean:198-206`.  
3. `applyMatrixFreeSparse`: `ObservedOps.lean:579-587`.  
4. `applyMatrixFreeBucketed`: `ObservedOps.lean:591-600`.

Mathematical semantics:
1. `applyDenseVec` is direct multiplication by the big left matrix in the tex main equation.  
2. `applyMatrixFree` decomposes the same operation into `P=KW`, `u=gather(...)`, `U=scatter(...)`, then recombines.  
3. `applyMatrixFreeSparse` rewrites this pipeline into summation over observation indices only.  
4. `applyMatrixFreeBucketed` replaces Step-C with bucketed accumulation; same operator, more engineering-oriented implementation.

Auditable bridges:
1. `applyDenseVec_eq_vec_applyMatrixFreeSparse` (`ObservedOps.lean:700-710`).  
2. `applyMatrixFreeSparse_eq_applyMatrixFree` (`ObservedOps.lean:621-629`).  
3. `applyMatrixFreeBucketed_eq_sparse` (`ObservedOps.lean:602-610`).

Role in the mainline:  
Step1 uses D3 to prove "dense = matrix-free"; Step3/4 prove "sparse and bucketed are both implementations of the same operator".

### 4.4 D4: Online factor-row generation (without explicit `Z` storage)

Definition locations:
1. `ObsFactorProvider`: `ObservedOps.lean:339`.  
2. `obsRowFromFactors`: `ObservedOps.lean:343-344`.  
3. `factorsGenerateObservedRows`: `ObservedOps.lean:353-358`.  
4. `applyMatrixFreeObserved` / `rhsFromObservedRows`: `ObservedOps.lean:487-495`, `546-551`.

Mathematical semantics:
1. `ObsFactorProvider` gives factor values for each auxiliary mode, each observation, and each rank component.  
2. `obsRowFromFactors` generates observed row `z^{(t)}` by cross-mode product.  
3. `factorsGenerateObservedRows` explicitly states that online generated rows are consistent with corresponding rows in explicit `Z`.  
4. `applyMatrixFreeObserved` and `rhsFromObservedRows` depend only on online rows, without explicit `M×r` storage of `Z`.

Auditable bridges:
1. `rhsFromObservedRows_from_factors_eq_rhsFromObserved` (`ObservedOps.lean:565-576`).  
2. `applyMatrixFreeObserved_from_factors_eq_sparse` (`ObservedOps.lean:647-658`).

Role in the mainline:  
Step5 is exactly D4's closure certificate, answering why the online implementation is fully equivalent to explicit `Z`.

### 4.5 D5: Preconditioning and spectral-residual objects

Definition locations:
1. `precond1Apply`: `BaseDefs.lean:16-18`.  
2. `gramMatrix`: `BaseDefs.lean:53-54`.  
3. `precond2Matrix`: `BaseDefs.lean:86-88`.  
4. `precond2Apply`: `BaseDefs.lean:112-114`.  
5. `precond1Matrix`: `BaseDefs.lean:539-541`.  
6. `pcgResidualNorm`: `Contraction.lean:101`.

Mathematical semantics:
1. precond1 corresponds to inverse-action approximation of `\lambda(I_r \otimes K)`.  
2. precond2 uses the structured model `(Z^T Z + \lambda I_r) \otimes K`.  
3. `pcgResidualNorm` is the residual-norm indicator at iteration step `k`.

Auditable bridges:
1. Step6 calls `q10_mainline_preconditioner_action_bridge` and `q10_mainline_precond2_closed_form_bridge` to give preconditioner correctness and closed-form expression.  
2. Step7 connects D5 objects to spectral-interval assumptions and derives residual upper bounds.

### 4.6 D6: Cost model

Definition locations:
1. `matVecCost`: `CostAndPSD.lean:18`.  
2. `applyMatrixFreeSparseCost`: `CostAndPSD.lean:149-151`.  
3. `applyMatrixFreeObservedOnlineCost`: `CostAndPSD.lean:170-172`.  
4. `rhsFromObservedCost`: `CostAndPSD.lean:174-175`.

Mathematical semantics:  
These definitions write "cost per operator step" as explicit polynomials whose variables are only `n,r,q,dObs`, with no full-`N` traversal.

Auditable bridge:
`applyMatrixFreeSparseCost_eq_two_mul_matVecCost` (`CostAndPSD.lean:153`) bridges sparse main cost to the main matvec baseline.

Role in the mainline:  
Step8 gives core complexity formulas, and Step16 adds one more bridge for cost in the default delivery interface.

---

## 5. What `TexAligned` Actually Does in the Proof Chain

`TexAligned.lean` is an alignment layer that "splits a large certificate into human-readable steps":

1. Step1-9: mathematical-content layer
- Step1 `q10_tex_step1_system_equivalence`: rigorously proves equivalence between the dense Kronecker linear system and matrix-free sparse implementation.
- Step2 `q10_tex_step2_rhs_from_observations`: locks RHS to `rhsFromObserved` generated from observed entries, excluding arbitrary RHS replacement.
- Step3 `q10_tex_step3_matrix_vector_pipeline`: proves gather/scatter/sparse pipeline is pointwise consistent with the baseline operator.
- Step4 `q10_tex_step4_bucketed_matvec_and_cost`: proves bucketed (CSR-style) implementation has the same operator and same cost model as sparse implementation.
- Step5 `q10_tex_step5_online_rows_equivalence`: proves online observed-row generation (without explicit `Z` storage) is consistent with explicit-`Z` RHS/matvec.
- Step6 `q10_tex_step6_preconditioners`: gives correctness of two preconditioners and the closed form of precond2.
- Step7 `q10_tex_step7_pcg_residual_from_spectrum`: turns spectral-interval premises into PCG residual upper-bound certificates.
- Step8 `q10_tex_step8_complexity_formulas`: gives explicit complexity equalities without environment total scale `N`.
- Step9 `q10_tex_step9_psd_to_shift_core`: proves PSD kernels enter SPD via `K + nu I` (`nu > 0`), enabling PCG theory.

2. Step10-17: delivery-packaging layer
- Step10 `q10_tex_step10_default_core`: exports the core total certificate of "minimal inputs + spectral index + ambient-`N`".
- Step11 `q10_tex_step11_default_online_closure`: exports the "online-closure" certificate.
- Step12 `q10_tex_step12_default_shifted_pcg`: exports the closure certificate that "PSD becomes PCG-usable after shift".
- Step13 `q10_tex_step13_default_poly_envelope`: exports the "polynomial-envelope tolerance closure" certificate.
- Step14 `q10_tex_step14_default_spectral_binding`: binds abstract spectral-interval assumptions to the concrete preconditioned operators here.
- Step15 `q10_tex_step15_default_strong_precond2_branch`: exports the strong precond2 branch (Loewner/κ/rate improvement) certificate.
- Step16 `q10_tex_step16_default_cost_bridge`: fills the bridge equality between sparse matvec cost and main cost model.
- Step17 `q10_tex_step17_full_default_package`: exports the full default package (same source as `q10_tex_final_answer`).

Corresponding location: `autoproof/Q10/Mainline/TexAligned.lean:17-583`.
Note: line numbers may shift after refactoring; when auditing, prioritize searching by Step names.

---

## 6. Verification Route (Recommended Order)

Use this order to verify consistency of "statement-definition-proof-delivery" most directly:

1. Statement and objects
- Read `autoproof/q10.tex:1-38`.
- Cross-check with Sections 2 and 3 of this document to confirm every symbol has landed in a Lean object.

2. Key definitions
- Read corresponding definitions in `ProblemModel.lean` and `ObservedOps.lean`.
- Focus check: `Ω/vals` replacing full `T`, and `K` carrying kernelized information.

3. Equivalence bridges
- Check `q10_tex_step1_system_equivalence` and `q10_tex_step2_rhs_from_observations`.
- This step guarantees we are not changing the problem, only changing to computable expressions.

4. Correctness of computational implementations
- Check Step3/4/5 to confirm sparse/CSR/online are all consistent with the baseline operator.

5. Iterative theory and cost
- Check Step6/7/8 to confirm preconditioners, residual bounds, and complexity all have certificates.

6. PSD fallback and full packaging
- Check Step9 and Step10-17 to confirm both extreme-case handling and final interface are closed.

7. Machine verification
- Run:
```bash
lake env lean autoproof/Q10/Mainline/TexAligned.lean
lake env lean autoproof/Q10/Mainline/TexAnswer.lean
```
- If both files pass, the certificate chain is replayable.

---

## 7. Reading-Structure Summary

A complete understanding should follow a three-layer structure:
1. Concept layer: this document (object definitions, symbol mapping, key `def/structure`).
2. Mainline layer: first read `autoproof/Q10/Mainline/TexAligned.README.md` (line-by-line proof interpretation), and read it against `autoproof/Q10/Mainline/TexAligned.lean` (proof chain and packaging order of Step1-17).
3. Source layer: `autoproof/Q10/Mainline/TexAnswer.lean` (source of total certificate and default delivery interface).
If you encounter an unfamiliar symbol in the mainline layer, jump back to Sections 2-4 of this document to check "definition-location-role", then return to the corresponding Step; this is the most efficient reading route.
