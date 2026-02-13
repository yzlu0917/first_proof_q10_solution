# TexAligned.lean Line-by-Line Beginner Guide

This document does one thing only: it translates **every line** of `autoproof/Q10/Mainline/TexAligned.lean` into Chinese that mathematical readers can read directly.
Reading method: put the Lean source on the left and this file on the right, and compare line by line using `- Lxxx`.
Document positioning: this file is a "line-by-line reading of the proof mainline" (more specific), focused on what each line of the proof is doing and why it is valid.
If you want to first build the overall semantics of the statement symbols and key structures/definitions before returning to the line-by-line proof, read
`autoproof/Q10/Mainline/TexConceptsAndProofRoute.README.md` first.
The main text explains the proof in line order; when key concepts appear, explanations and source locations are given under the corresponding entries.

## A. Basic Syntax Key (Understand Lean Writing in 1 Minute)

- `theorem T : P := by ...`: declares a theorem named `T`, with proposition `P`; the proof script is after `by`.
- `def X := Y`: defines a new object `X`; the content of `X` is `Y`.
- `abbrev X := Y`: only introduces an alias, without adding a new mathematical object; it replaces a long name with a short one.
- `:=`: read as "is defined as / use the right side as the implementation of the left side".
- `@f`: uses the "all-parameters-explicit" version of `f`, avoiding hidden parameters that Lean may omit automatically.
- `intro x`: introduces the quantified variable/assumption from `∀ x, ...` or from the antecedent of an implication.
- `calc ...`: chained equality derivation, splitting a large equality into small checkable steps.
- `simp [...]`: performs automated algebraic simplification using the given list of lemmas.
- `simpa using h`: first simplifies the goal to a standard form, then closes with an existing result `h`.
- `rfl`: `reflexivity`; when both sides are the same expression after unfolding definitions, the proof ends immediately.
- `(K := K)` style: explicitly specifies named arguments and tells Lean to use the current `K` for that parameter.

## B. Complete Line-by-Line Explanation (`- L001` to `- L583`)

- L001: `import autoproof.Q10.Mainline.TexAnswer`
  Explanation: import dependency; all following conclusions are based on theorems already in this file.
- L002: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L003: `set_option autoImplicit false`
  Explanation: disable automatic implicit parameters; force explicit parameters for easier human reading.
- L004: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L005: `open scoped BigOperators Kronecker`
  Explanation: after opening scopes `BigOperators` and `Kronecker`, later notations like `∑` and `⊗ₖ` are parsed in linear-algebra semantics; this ensures Lean expressions align directly with matrix/tensor formulas in tex.
- L006: `open Matrix`
  Explanation: open the Matrix namespace so matrix notation can be written directly below.
- L007: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L008: `namespace AutoProof`
  Explanation: first enter top-level namespace `AutoProof`, separating this project’s symbols from external library symbols.
- L009: `namespace Q10`
  Explanation: further enter sub-namespace `Q10` inside `AutoProof`, indicating the following code serves the Q10 mainline.
- L010: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L011: `noncomputable section`
  Explanation: enter a noncomputable section; this is mathematical proof, not executable algorithm code.
- L012: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L013: `variable {n M r q : Nat}`
  Explanation: declare global size parameters `n`, `M`, `r`, `q`.
- L014: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L015: `/-- \`q10.tex\` Step 1 (system equation):`
  Explanation: this is the Step 1 comment header, telling readers that the next block is Lean’s correspondence for the "system-equation equivalence" question.
- L016: `Dense Kronecker/selection system is equivalent to the matrix-free sparse action. -/`
  Explanation: the comment body summarizes Step 1: dense Kronecker+selection form is fully equivalent to matrix-free sparse action.
- L017: `theorem q10_tex_step1_system_equivalence`
  Explanation: Premise: given symmetric kernel matrix `K`, feature matrix `Z`, observation index `Ω`, regularization parameter `lam`, and arbitrary `W,B`; Conclusion: `applyDenseVec ... = rhsVec ...` iff `applyMatrixFreeSparse ... = K * B`; Role: rigorously bridges the theoretical system form in tex Step 1 and the computable matrix-free form, establishing an equal-value baseline for all later sparse routes.
- L018: `    (K : Matrix (Fin n) (Fin n) Real)`
  Explanation: kernel matrix parameter `K` in Step 1; system equivalence is ultimately built around it for the LHS operator and RHS `K*B`.
- L019: `    (Z : Matrix (Fin M) (Fin r) Real)`
  Explanation: feature matrix parameter `Z` in Step 1; it controls feature-coupling structure in the Kronecker/selection system.
- L020: `    (Ω : Fin q → Fin M × Fin n)`
  Explanation: observation-index map `Ω` in Step 1; it places the `i`-th observation at coordinate `(m,n)`.
- L021: `    (lam : Real)`
  Explanation: regularization parameter `lam` in Step 1; it enters operator `A`, affecting the same operator family on both dense and sparse sides.
- L022: `    (hK : Kᵀ = K)`
  Explanation: this line explicitly requires symmetry of `K`; mathematically it places the system in a self-adjoint framework, and in the proof chain it is required to call the main bridge theorem when rewriting dense to matrix-free form.
- L023: `    (W B : Matrix (Fin n) (Fin r) Real) :`
  Explanation: parameters `W` and `B`: `W` is the unknown, and `B` is the RHS MTTKRP matrix.
- L024: `    applyDenseVec K Z Ω lam W.vec = rhsVec K B`
  Explanation: this line states the left proposition of the equivalence: vectorize `W`, substitute into the dense system, and require equality with vectorized RHS.
- L025: `      ↔ applyMatrixFreeSparse K Z Ω lam W = K * B := by`
  Explanation: this line does two things at once: mathematically it declares "dense equation ↔ matrix-free equation"; syntactically `:= by` starts the theorem proof block, where `:=` means "defined by / provided by the right side".
- L026: `  exact q10_mainline_system_equiv_matrixFree`
  Explanation: `exact` means the current goal matches this existing theorem exactly and can be delivered directly; this delegates all Step 1 proof work to the main bridge theorem, avoiding repeated derivation.
- L027: `    (K := K) (Z := Z) (Ω := Ω) (lam := lam) (hK := hK) (W := W) (B := B)`
  Explanation: explicitly pass each local parameter into the bridge theorem to ensure the instantiated object is exactly current `K,Z,Ω,λ,W,B`.
- L028: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L029: `/-- \`q10.tex\` Step 2 (RHS from observed entries):`
  Explanation: this is the Step 2 comment header, corresponding to the statement part "how RHS is constructed from observations".
- L030: `\`B = TZ\` is locked by observed sparse MTTKRP, so RHS is \`rhsFromObserved\`. -/`
  Explanation: the comment body gives the core meaning: `B` is not a free matrix; it is fixed by sparse MTTKRP, so RHS is fixed as `rhsFromObserved`.
- L031: `theorem q10_tex_step2_rhs_from_observations`
  Explanation: Premise: `P` is `TexObservedProblem`, which already includes structural information that observation data locks RHS; Conclusion: `rhsVec P.K P.B` is exactly equal to `rhsFromObserved P.K P.Ω P.vals P.Z`; Role: corresponds to tex Step 2 and makes explicit that RHS is not free but uniquely determined by observed entries.
- L032: `    (P : TexObservedProblem n M r q) :`
  Explanation: this packages all data as `TexObservedProblem`; it carries built-in structure that observed RHS is locked, exactly suitable for Step 2.
- L033: `    rhsVec P.K P.B = rhsFromObserved P.K P.Ω P.vals P.Z := by`
  Explanation: theorem body directly states the Step 2 conclusion: the statement RHS `rhsVec P.K P.B` and observation-driven `rhsFromObserved ...` are equal at the object level.
- L034: `  exact P.rhsVec_eq_rhsFromObserved`
  Explanation: directly use the built-in locking axiom of `TexObservedProblem` to obtain `rhsVec = rhsFromObserved`.
- L035: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L036: `/-- \`q10.tex\` Step 3 (matrix-vector pipeline identities):`
  Explanation: this is the Step 3 comment header, entering equivalence proof for the matvec pipeline (`gather/scatter/sparse`).
- L037: `Step-B gather, Step-C scatter, and sparse matrix-free implementation are`
  Explanation: first comment line says the next part will unify gather, scatter, and sparse matrix-free into one consistent pipeline.
- L038: `exactly the dense pipeline rewritten over \`q\` observed entries. -/`
  Explanation: second comment line emphasizes this pipeline is just a rewrite of dense computation over `q` observed entries; the mathematical object is unchanged.
- L039: `theorem q10_tex_step3_matrix_vector_pipeline`
  Explanation: Premise: fix the same group `K,Z,Ω,lam,W`; Conclusion: `gatherKernelPredictSparse`, `scatterMulSparse`, and `applyMatrixFreeSparse` are each equivalent to explicit dense-pipeline forms; Role: corresponds to tex Step 3 and proves implementation-level gather/scatter rewriting does not change operator semantics.
- L040: `    (K : Matrix (Fin n) (Fin n) Real)`
  Explanation: `K` in Step 3 is the base kernel for pipeline-equivalence proof; both gather and scatter expand around `K*W*Zᵀ`.
- L041: `    (Z : Matrix (Fin M) (Fin r) Real)`
  Explanation: `Z` in Step 3 determines whether right-multiplying prediction by `Zᵀ` and then multiplying `Z` after scatter are aligned.
- L042: `    (Ω : Fin q → Fin M × Fin n)`
  Explanation: `Ω` in Step 3 drives both `gather` and `scatter`, ensuring extraction and backfill target the same observed set.
- L043: `    (lam : Real)`
  Explanation: `lam` in Step 3 appears only in the third conclusion (`applyMatrixFreeSparse = applyMatrixFree`) to guarantee full definition-level operator identity.
- L044: `    (W : Matrix (Fin n) (Fin r) Real) :`
  Explanation: introduce arbitrary input matrix `W`; all three equalities below hold for arbitrary `W`.
- L045: `    gatherKernelPredictSparse K Z Ω W = gather Ω (K * W * Zᵀ) ∧`
  Explanation: first sub-conclusion: sparse gather implementation is exactly consistent with "compute `K*W*Zᵀ` first, then sample by `Ω`".
- L046: `    scatterMulSparse Ω Z (gatherKernelPredictSparse K Z Ω W)`
  Explanation: left side of second sub-conclusion: gather first, then run implementation form `scatterMulSparse`.
- L047: `      = (scatter Ω (gather Ω (K * W * Zᵀ))) * Z ∧`
  Explanation: right side of second sub-conclusion: rewrite it into standard algebraic form "backfill matrix * Z".
- L048: `    applyMatrixFreeSparse K Z Ω lam W = applyMatrixFree K Z Ω lam W := by`
  Explanation: third sub-conclusion: explicitly prove sparse implementation is definition-level equivalent to original `applyMatrixFree`.
- L049: `  refine ⟨?_, ?_, ?_⟩`
  Explanation: `refine ⟨?_, ?_, ?_⟩` splits the conjunction target into 3 subgoals; `?_` are proof holes for gather equivalence, scatter equivalence, and matvec equivalence.
- L050: `  · exact gatherKernelPredictSparse_eq_gather (K := K) (Z := Z) (Ω := Ω) (W := W)`
  Explanation: first subgoal ends directly by calling the lemma proving `gatherKernelPredictSparse` equals explicit `gather`.
- L051: `  · calc`
  Explanation: `calc` is chained-equality syntax: each line is a small checkable rewrite, ending by rewriting implementation expression into matrix formula familiar to tex readers.
- L052: `      scatterMulSparse Ω Z (gatherKernelPredictSparse K Z Ω W)`
  Explanation: start point of `calc`: begin the equality chain from original input expression of `scatterMulSparse`.
- L053: `          = scatterMulSparse Ω Z (gather Ω (K * W * Zᵀ)) := by`
  Explanation: proof starts here and enters proof script below.
- L054: `              simp [gatherKernelPredictSparse_eq_gather]`
  Explanation: `simp` automatically rewrites using given lemmas; here it directly turns `gatherKernelPredictSparse` into standard `gather`, preparing for the next `scatter` lemma.
- L055: `      _ = (scatter Ω (gather Ω (K * W * Zᵀ))) * Z :=`
  Explanation: this line is the key landing point in the `calc` chain: rewrite implementation symbol `scatterMulSparse` into standard matrix form "scatter-backfill then multiply `Z`", converting engineering expression back to algebraic form familiar to tex readers.
- L056: `            scatterMulSparse_eq_scatter_mul`
  Explanation: call the key lemma that precisely rewrites `scatterMulSparse` as `scatter ... * Z`.
- L057: `              (Ω := Ω) (Z := Z) (u := gather Ω (K * W * Zᵀ))`
  Explanation: provide the concrete instance for that lemma: set `u` to current `gather Ω (K * W * Zᵀ)`.
- L058: `  · exact applyMatrixFreeSparse_eq_applyMatrixFree`
  Explanation: third subgoal directly calls the core lemma, completing equivalence between sparse and original matvec versions.
- L059: `      (K := K) (Z := Z) (Ω := Ω) (lam := lam) (W := W)`
  Explanation: explicitly instantiate `K,Z,Ω,λ,W` into `applyMatrixFreeSparse_eq_applyMatrixFree`.
- L060: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L061: `/-- \`q10.tex\` Step 4 (CSR/bucket implementation and cost):`
  Explanation: this is the Step 4 comment header, discussing CSR/bucket implementation and cost counting.
- L062: `bucketed matrix-free matvec is algebraically identical to sparse matvec,`
  Explanation: first comment line emphasizes algebraic output equivalence between bucket/CSR implementation and sparse implementation.
- L063: `and its trace cost equals the sparse model cost. -/`
  Explanation: second comment line states not only output equivalence but also exact equality of trace-count cost with sparse model.
- L064: `theorem q10_tex_step4_bucketed_matvec_and_cost`
  Explanation: Premise: with fixed `K,Z,Ω,lam`, compare under canonical bucket plan for arbitrary `W`; Conclusion: bucketed matvec output equals sparse matvec and bucket trace-count cost equals `applyMatrixFreeSparseCost`; Role: corresponds to tex Step 4, aligning engineering optimization with theoretical value and cost model in both aspects.
- L065: `    (K : Matrix (Fin n) (Fin n) Real)`
  Explanation: `K` in Step 4 appears in both bucketed and sparse implementations; what is compared is implementation difference under the same kernel, not model difference.
- L066: `    (Z : Matrix (Fin M) (Fin r) Real)`
  Explanation: `Z` in Step 4 ensures both implementations share the same feature input, making "same output" conclusion comparable.
- L067: `    (Ω : Fin q → Fin M × Fin n)`
  Explanation: `Ω` in Step 4 determines bucket partition and sparse access path; cost comparison is fully tied to this observation index set.
- L068: `    (lam : Real) :`
  Explanation: `lam` in Step 4 fixes the same regularization term in both matvecs, avoiding mixing implementation differences with model-parameter differences.
- L069: `    (∀ W : Matrix (Fin n) (Fin r) Real,`
  Explanation: beginning of first universal quantifier: prove output equivalence for arbitrary `W`.
- L070: `      applyMatrixFreeBucketed K Z Ω (canonicalObsBuckets Ω) lam W`
  Explanation: this line makes explicit that the left object is matvec output under canonical bucket organization, i.e., the operator output actually executed by engineering implementation.
- L071: `        = applyMatrixFreeSparse K Z Ω lam W) ∧`
  Explanation: this line completes the first branch conclusion: bucketed output equals sparse output pointwise.
- L072: `    (∀ W : Matrix (Fin n) (Fin r) Real,`
  Explanation: beginning of second universal quantifier: prove trace-cost equivalence for arbitrary `W`.
- L073: `      sparseMatVecTraceCost n r`
  Explanation: specify the compared cost function as `sparseMatVecTraceCost n r`.
- L074: `        (applyMatrixFreeBucketedPlan K Z Ω (canonicalObsBuckets Ω) lam W).2`
  Explanation: `applyMatrixFreeBucketedPlan ...` returns "result + trace"; `.2` takes the second component (trace), fed into the cost-counting function.
- L075: `          = applyMatrixFreeSparseCost n r q) := by`
  Explanation: this line completes the second branch conclusion: trace cost of bucketed plan is exactly `applyMatrixFreeSparseCost`.
- L076: `  refine ⟨?_, ?_⟩`
  Explanation: split Step 4 total target into two parts: prove "value equality" first, then "cost equality".
- L077: `  · intro W`
  Explanation: `intro W` converts "for all `W`" into "fix an arbitrary `W` and prove"; this is Lean's standard action for `∀`.
- L078: `    exact applyMatrixFreeCanonicalBucketed_eq_sparse`
  Explanation: the first subgoal is closed directly by reusing the canonical-bucket equivalence lemma.
- L079: `      (K := K) (Z := Z) (Ω := Ω) (lam := lam) (W := W)`
  Explanation: pass current `K,Z,Ω,λ,W` into the conclusion "canonical bucket = sparse".
- L080: `  · intro W`
  Explanation: enter the second subgoal: fix an arbitrary `W` and prove bucketed-plan cost equals sparse cost.
- L081: `    exact applyMatrixFreeCanonicalBucketedPlan_cost_eq`
  Explanation: the second subgoal ends directly by calling the cost-consistency lemma.
- L082: `      (K := K) (Z := Z) (Ω := Ω) (lam := lam) (W := W)`
  Explanation: pass current `K,Z,Ω,λ,W` into the conclusion "canonical bucket plan cost = sparse cost".
- L083: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L084: `/-- \`q10.tex\` Step 5 (online observed-row generation):`
  Explanation: this is the Step 5 comment header, entering equivalence between online observed-row generation and explicit `Z`.
- L085: `if observed rows are generated on-the-fly from factors, both RHS and matvec`
  Explanation: first comment line says this section proves online observed-row generation does not change RHS and matvec semantics.
- L086: `match the explicit-\`Z\` sparse formulas. -/`
  Explanation: second comment line adds that after online generation, both RHS and matvec are exactly consistent with explicit-`Z` sparse formulas.
- L087: `theorem q10_tex_step5_online_rows_equivalence`
  Explanation: Premise: given online factor provider `F` and consistency assumption `factorsGenerateObservedRows`; Conclusion: online `rhsFromObservedRows` equals explicit `rhsFromObserved`, and online `applyMatrixFreeObserved` equals `applyMatrixFreeSparse` for arbitrary `W`; Role: corresponds to tex Step 5 and confirms online observed-row generation changes only implementation style, not the mathematical equation.
- L088: `    (P : TexProblem n M r q)`
  Explanation: Step 5 uses `TexProblem` (not `TexObservedProblem`) because this part first constructs RHS/operator equivalence from given `vals` and online row generator.
- L089: `    (vals : Fin q → Real)`
  Explanation: `vals` maps each observation index `i : Fin q` to the corresponding real observed value; mathematically this is the numeric carrier of observed tensor entries and determines RHS values, not just structure.
- L090: `    {dObs : Nat}`
  Explanation: `dObs` is the internal dimension of the online generator; written as implicit parameter, meaning readers usually do not fill it manually and Lean infers it from `F`.
- L091: `    (F : ObsFactorProvider dObs q r)`
  Explanation: `F` is the online data-source interface: given an observation index, it produces the factor-row information needed for that observation on demand.
- L092: `    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F) :`
  Explanation: `hRows` is the consistency certificate: it guarantees online-generated data equals explicit `Z` at every observation location; this is the core assumption for Step 5.
- L093: `    rhsFromObservedRows P.K P.Ω vals (obsRowFromFactors F)`
  Explanation: left side first writes the concrete form of online RHS: no explicit `Z`, but dynamically generate observed rows from `F` and aggregate them into RHS.
- L094: `      = rhsFromObserved P.K P.Ω vals P.Z ∧`
  Explanation: completes the first sub-conclusion: online RHS equals explicit-`Z` RHS, then conjoins with the second conclusion.
- L095: `    (∀ W : Matrix (Fin n) (Fin r) Real,`
  Explanation: start of second sub-conclusion: compare online matvec and sparse matvec for arbitrary `W`.
- L096: `      applyMatrixFreeObserved P.K P.Ω (obsRowFromFactors F) P.lam W`
  Explanation: left side of online version: execute matvec using observation rows provided by `obsRowFromFactors F`.
- L097: `        = applyMatrixFreeSparse P.K P.Z P.Ω P.lam W) := by`
  Explanation: this line closes the second sub-conclusion: online matvec equals explicit-`Z` sparse matvec for all `W`.
- L098: `  refine ⟨?_, ?_⟩`
  Explanation: split Step 5 into two independent tasks: RHS equivalence and matvec equivalence.
- L099: `  · exact rhsFromObservedRows_from_factors_eq_rhsFromObserved`
  Explanation: this line directly calls the dedicated bridge theorem, proving the core claim "online RHS generation is exactly equal to explicit-`Z` RHS".
- L100: `      (K := P.K) (Ω := P.Ω) (vals := vals) (Z := P.Z) (F := F) (hRows := hRows)`
  Explanation: substitute all `K,Ω,vals,Z,F,hRows` into the RHS-equivalence bridge theorem to obtain the first sub-conclusion.
- L101: `  · intro W`
  Explanation: enter the second subgoal: fix arbitrary `W` and prove online matvec equivalence.
- L102: `    exact applyMatrixFreeObserved_from_factors_eq_sparse`
  Explanation: directly call the matvec-equivalence lemma for online rows generated from factors.
- L103: `      (K := P.K) (Z := P.Z) (Ω := P.Ω) (F := F) (hRows := hRows)`
  Explanation: substitute `K,Z,Ω,F,hRows` into the online matvec-equivalence bridge theorem.
- L104: `      (lam := P.lam) (W := W)`
  Explanation: continue completing parameters on the above line using current `λ` and `W`.
- L105: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L106: `/-- \`q10.tex\` Step 6 (preconditioner correctness and closed form):`
  Explanation: this is the Step 6 comment header, corresponding to "how preconditioners are defined, why they are correct, and whether they have closed forms" in the statement.
- L107: `under SPD assumptions required by PCG inverse actions, both preconditioners`
  Explanation: first comment line states this section depends on SPD assumptions (required by PCG/inverse actions).
- L108: `are correct and preconditioner-2 has an explicit closed form. -/`
  Explanation: second comment line clearly outputs: both preconditioners are correct, and preconditioner-2 has an explicit closed form.
- L109: `theorem q10_tex_step6_preconditioners`
  Explanation: Premise: require `lam > 0` and `K` positive definite so related inverse actions are legal; Conclusion: preconditioner-1 and preconditioner-2 both satisfy left-inverse correctness, and preconditioner-2 has explicit closed form; Role: corresponds to tex Step 6 by turning "preconditioner usability" into machine-checkable equalities instead of verbal statements.
- L110: `    (P : TexProblem n M r q)`
  Explanation: Step 6 is also based on `TexProblem`; here the focus is algebraic correctness of preconditioners, not the extra structure that `vals` is already locked.
- L111: `    (hLamPos : 0 < P.lam)`
  Explanation: require `λ>0`, so `λ(I⊗K)` and related inverse operators have invertibility basis in preconditioner proofs.
- L112: `    (hKpos : P.K.PosDef) :`
  Explanation: require `K` positive definite, making inverse-matrix expressions in preconditioner actions legal and usable in PCG route.
- L113: `    (∀ R : Matrix (Fin n) (Fin r) Real,`
  Explanation: first universal quantifier: prove left-inverse relation of precond1 for arbitrary residual matrix `R`.
- L114: `      (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ (precond1Apply P.toProblem R).vec`
  Explanation: writes the left operator for precond1: `λ(I⊗K)` acting on vectorized result of `precond1Apply`.
- L115: `        = R.vec) ∧`
  Explanation: completes precond1 left-inverse equality, then conjoins with the following precond2 conclusion.
- L116: `    (∀ R : Matrix (Fin n) (Fin r) Real,`
  Explanation: second universal quantifier: prove precond2 left-inverse relation for arbitrary `R`.
- L117: `      precond2Matrix P.toProblem *ᵥ (precond2Apply P.toProblem R).vec = R.vec) ∧`
  Explanation: this line is left-inverse correctness of preconditioner 2.
- L118: `    (∀ R : Matrix (Fin n) (Fin r) Real,`
  Explanation: start of third universal quantifier: give closed-form formula of precond2 for arbitrary `R`.
- L119: `      precond2Apply P.toProblem R`
  Explanation: left side of closed-form equality: the object currently characterized is `precond2Apply(P,R)`.
- L120: `        = P.K⁻¹ * R * (gramMatrix P.toProblem + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹) := by`
  Explanation: this line writes full closed form of precond2, and opens the proof block with `:= by`; the mathematical goal is to realize the "algorithm definition" as an explicit computable matrix formula.
- L121: `  refine ⟨?_, ?_, ?_⟩`
  Explanation: split Step 6 into three parts: precond1 left inverse, precond2 left inverse, and precond2 closed form.
- L122: `  · intro R`
  Explanation: enter first subgoal: fix arbitrary residual `R` and prove precond1 left-inverse relation.
- L123: `    exact (q10_mainline_preconditioner_action_bridge`
  Explanation: directly reuse mainline bridge theorem and extract the precond1 component, without repeating proof details.
- L124: `      (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos)).1 R`
  Explanation: take the first component (precond1 correctness) from the bridge theorem and instantiate with current `R`.
- L125: `  · intro R`
  Explanation: enter second subgoal: fix arbitrary `R` and prove precond2 left-inverse relation.
- L126: `    exact (q10_mainline_preconditioner_action_bridge`
  Explanation: similarly reuse the bridge theorem, this time taking the precond2 left-inverse component.
- L127: `      (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos)).2 R`
  Explanation: take the second component (precond2 left-inverse correctness) from bridge theorem and instantiate with current `R`.
- L128: `  · intro R`
  Explanation: enter third subgoal: fix arbitrary `R` and give the closed-form formula of precond2.
- L129: `    exact (q10_mainline_precond2_closed_form_bridge`
  Explanation: directly call precond2 closed-form bridge theorem and extract the required component.
- L130: `      (P := P.toProblem) (hLam := hLamPos) (hKpos := hKpos) (R := R)).2.2`
  Explanation: extract the "precond2 closed-form formula" component (`2.2`) from the closed-form bridge and instantiate at `R`.
- L131: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L132: `/-- \`q10.tex\` Step 7 (PCG residual certificate from spectral interval):`
  Explanation: this is the Step 7 comment header, converting spectral-interval information into a PCG residual upper-bound certificate.
- L133: `for this concrete problem and each preconditioner, dense-spectrum bounds`
  Explanation: first comment line says this section gives spectrum-to-residual certificates for the concrete operator in this problem and both preconditioners.
- L134: `on the preconditioned operator imply residual-norm bounds. -/`
  Explanation: second comment line emphasizes the logic direction: first spectral bounds of preconditioned operators, then residual-norm bounds.
- L135: `theorem q10_tex_step7_pcg_residual_from_spectrum`
  Explanation: Premise: given spectral-interval constraints, operator symmetry, and initial residual-norm upper bounds; Conclusion: for both preconditioner-1/2, obtain `pcgResidualNorm` upper bounds for arbitrary step `k`; Role: corresponds to tex Step 7 by turning abstract spectral information into computable convergence-rate inequality certificates.
- L136: `    (P : TexObservedProblem n M r q)`
  Explanation: Step 7 uses `TexObservedProblem` because residual certificates must be tied to a concrete instance where observed RHS is fixed.
- L137: `    (mu L : Real)`
  Explanation: parameters `mu` and `L`: lower and upper bounds of the spectrum interval for the preconditioned operator.
- L138: `    (hMuLeL : mu ≤ L)`
  Explanation: require `mu ≤ L` so `[mu,L]` is a valid closed interval; in Step 7 this ensures the assumption "spectrum contained in the interval" can be used in residual-polynomial bounds without interval-definition failure.
- L139: `    (hLamPos : 0 < P.lam)`
  Explanation: convergence certificate requires `λ>0`, ensuring the preconditioning system bound to spectral interval does not degenerate.
- L140: `    (hKpos : P.K.PosDef)`
  Explanation: positive definiteness of `K` here is a hard assumption in the chain, placing the problem into standard SPD-PCG theory.
- L141: `    (hSymm1 :`
  Explanation: this starts the symmetry assumption for the precond1 branch: require matrix representation of `M₁⁻¹A` to be self-adjoint (symmetric over reals), a premise for later spectral certificates.
- L142: `      (LinearMap.toMatrixAlgEquiv'`
  Explanation: this writes precond1 action as an ordinary matrix (not abstract linear map), because the following lines directly discuss transpose and eigenvalue interval.
- L143: `            (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem)))ᵀ`
  Explanation: writes transpose of this matrix, preparing to declare "transpose equals itself".
- L144: `        = LinearMap.toMatrixAlgEquiv'`
  Explanation: middle symbol of symmetry equality: left transpose equals right original matrix.
- L145: `            (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem)))`
  Explanation: right side of symmetry equality: still the matrix representation of precond1 `M^{-1}A`.
- L146: `    (hEigRange1 :`
  Explanation: this starts spectral-interval assumption for precond1: require all eigenvalues of the preconditioned operator to lie in `[mu,L]`.
- L147: `      spectrum ℝ`
  Explanation: `spectrum ℝ` can be read directly as "the full set of eigenvalues of this matrix over real field"; next line constrains it to `[mu,L]`.
- L148: `          (LinearMap.toMatrixAlgEquiv'`
  Explanation: this line specifies exactly which matrix eigenvalues are taken: the object is the matrixized operator in precond1 branch.
- L149: `            (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem)))`
  Explanation: completes the object on the previous line to avoid misreading the spectral-interval condition as applying to another operator.
- L150: `        ⊆ Set.Icc mu L)`
  Explanation: gives spectral-interval constraint: the full precond1 spectrum lies in closed interval `[mu, L]`.
- L151: `    (hSymm2 :`
  Explanation: now switch to precond2 branch and write the same type of symmetry assumption so the second preconditioned route can enter the same spectral-interval argument framework.
- L152: `      (LinearMap.toMatrixAlgEquiv'`
  Explanation: this switches to precond2 route and similarly writes it as an ordinary matrix, so we can reuse the exact same "symmetry + spectral interval" argument template as precond1.
- L153: `            (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem)))ᵀ`
  Explanation: writes transpose term of precond2 operator matrix.
- L154: `        = LinearMap.toMatrixAlgEquiv'`
  Explanation: center of symmetry equality, declaring "transpose = itself".
- L155: `            (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem)))`
  Explanation: right side of symmetry equality: the matrixized operator of precond2.
- L156: `    (hEigRange2 :`
  Explanation: this is the corresponding spectral-interval assumption for precond2, allowing both preconditioned routes to be compared under the same `mu,L` parameters.
- L157: `      spectrum ℝ`
  Explanation: start writing `hEigRange2`: take real spectrum of precond2 operator.
- L158: `          (LinearMap.toMatrixAlgEquiv'`
  Explanation: specifies the exact object whose eigenvalues are taken in precond2 route, not a generic abstract symbol.
- L159: `            (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem)))`
  Explanation: this line completes the precond2 linear-operator object and makes precise which concrete matrix spectrum is discussed; without this, later `spectrum ⊆ [mu,L]` cannot be tied exactly to precond2 route.
- L160: `        ⊆ Set.Icc mu L) :`
  Explanation: gives spectral-interval constraint for precond2: also inside `[mu, L]`.
- L161: `    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real,`
  Explanation: start of first major conclusion: for arbitrary initial value `x0` and initial preconditioned-residual bound `err0z`, provide precond1 residual estimate.
- L162: `      ‖WithLp.toLp 2 (precond1Apply P.toProblem (pcgR0 P.toProblem x0)).vec‖ ≤ err0z →`
  Explanation: this line gives the initial error bound: view step-0 preconditioned residual as Euclidean 2-norm (`WithLp.toLp 2` is just norm-space interface notation), and require it not exceed `err0z`.
- L163: `      ∀ k : Nat,`
  Explanation: precond1 branch lifts the conclusion to all iteration steps `k`, not only early steps or one fixed step.
- L164: `        pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0 k`
  Explanation: left side is the actual residual norm at step `k` of precond1-PCG.
- L165: `          ≤ precond1UndoBoundConst P.toProblem`
  Explanation: right side first uses undo constant `precond1UndoBoundConst`, accounting for amplification when converting preconditioned residual norm back to original residual norm.
- L166: `              * (polyAbsBoundOnIcc mu L`
  Explanation: multiply by the maximum absolute value of step-`k` residual polynomial on interval `[mu,L]`; this is the core step converting spectral constraints into numeric upper bounds.
- L167: `                  (pcgPrecondResidualPolyRec P.toProblem (precond1Apply P.toProblem) x0 k)`
  Explanation: this is the residual recurrence polynomial corresponding to PCG at step `k`; the polynomial changes with step count.
- L168: `                * err0z)) ∧`
  Explanation: multiply by initial bound `err0z`, then conjoin with the precond2 branch.
- L169: `    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real,`
  Explanation: start of the second major conclusion: same structure, but for precond2.
- L170: `      ‖WithLp.toLp 2 (precond2Apply P.toProblem (pcgR0 P.toProblem x0)).vec‖ ≤ err0z →`
  Explanation: initial error bound for precond2 branch; semantics are fully parallel to precond1 above: Euclidean 2-norm of step-0 preconditioned residual is bounded by `err0z`.
- L171: `      ∀ k : Nat,`
  Explanation: precond2 branch also gives guarantees for arbitrary `k`, ensuring both routes are theoretically parallel in form.
- L172: `        pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0 k`
  Explanation: left side is actual residual norm of precond2-PCG at step `k`.
- L173: `          ≤ precond2UndoBoundConst P.toProblem`
  Explanation: this is the precond2 "undo constant"; same role as above: convert an error bound under preconditioned metric back to original-problem metric.
- L174: `              * (polyAbsBoundOnIcc mu L`
  Explanation: continue multiplying by "maximum absolute value of polynomial on `[mu,L]`", keeping the upper-bound structure exactly isomorphic to precond1.
- L175: `                  (pcgPrecondResidualPolyRec P.toProblem (precond2Apply P.toProblem) x0 k)`
  Explanation: this term is the step-`k` residual recurrence polynomial of precond2 route, generated from the same PCG recursion logic as precond1.
- L176: `                * err0z)) := by`
  Explanation: by this line, both residual-upper-bound statements are fully written; `:= by` means we now only need to feed these assumptions into an existing total certificate.
- L177: `  exact q10_tex_pcg_spectral_interval_binding_certificate`
  Explanation: the whole proof directly reuses the main theorem "spectral-interval binding certificate"; this line only performs parameter transport and instantiation.
- L178: `    (P := P) (mu := mu) (L := L)`
  Explanation: explicitly pass current problem object and spectral-interval parameters into Step7 main certificate.
- L179: `    (hMuLeL := hMuLeL)`
  Explanation: explicitly pass interval-order premise `mu ≤ L` into the total certificate, ensuring certificate and current problem use the same valid spectral-interval definition; this keeps local assumptions semantically consistent with global certificate.
- L180: `    (hLamPos := hLamPos) (hKpos := hKpos)`
  Explanation: pass required assumptions `λ>0` and `K` positive definite for PCG.
- L181: `    (hSymm1 := hSymm1) (hEigRange1 := hEigRange1)`
  Explanation: pass two key spectral assumptions of precond1 route (symmetry and spectrum inclusion in `[mu,L]`) unchanged into total certificate.
- L182: `    (hSymm2 := hSymm2) (hEigRange2 := hEigRange2)`
  Explanation: then pass the corresponding two spectral assumptions of precond2 route; now both preconditioned routes are closed simultaneously under one certificate.
- L183: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L184: `/-- \`q10.tex\` Step 8 (complexity formulas, offline + online):`
  Explanation: this is the Step 8 comment header, corresponding to complexity discussion in the statement (offline + online).
- L185: `all cost models are explicit and \`N\`-free; sparse-vs-dominant cost bridge is`
  Explanation: first comment line emphasizes this section gives explicit cost formulas and expressions contain no large-scale `N`.
- L186: `also certified. -/`
  Explanation: second comment line adds that the bridge between explicit sparse cost and dominant cost is also formally certified.
- L187: `theorem q10_tex_step8_complexity_formulas`
  Explanation: Premise: fix problem sizes, online-row-generation consistency, iteration counts, etc.; Conclusion: provide all offline/online cost formulas at once, including `matVecCost`, `rhsFromObservedCost`, `applyMatrixFreeSparseCost`, online incremental cost, and total PCG cost; Role: corresponds to tex Step 8 by turning narrative complexity discussion into a closed list of line-by-line checkable formulas.
- L188: `    (n r q dObs : Nat) :`
  Explanation: parameters `n,r,q,dObs`: size variables in complexity formulas.
- L189: `    (matVecCost n r q = n * n * r + q * r) ∧`
  Explanation: first cost identity: expand abstract notation `matVecCost` into `n^2 r + q r`, matching the dominant per-step computation in tex.
- L190: `    (rhsFromObservedCost n r q = n * n * r + q * r) ∧`
  Explanation: second identity says RHS construction is same order and same formula as one dominant matvec, emphasizing RHS preparation adds no extra asymptotic order.
- L191: `    (applyMatrixFreeSparseCost n r q = 2 * (n * n * r) + q * r + q * r) ∧`
  Explanation: gives fine-grained sparse matvec cost expansion: two `n^2r` terms plus two `qr` terms.
- L192: `    (applyMatrixFreeSparseCost n r q = 2 * matVecCost n r q) ∧`
  Explanation: this is the scale-bridging equation: fine-grained sparse cost is exactly `2 ×` dominant matvec cost, useful for collapsing formulas into one unified metric.
- L193: `    (applyMatrixFreeObservedOnlineCost n r q dObs`
  Explanation: here starts the left object of online per-step cost formula: `applyMatrixFreeObservedOnlineCost` counts both matvec and online row generation.
- L194: `      = applyMatrixFreeSparseCost n r q + obsRowFromFactorsGenerationCost dObs q r) ∧`
  Explanation: this line is online per-step cost decomposition: `online = sparse + online observed-row generation cost`.
- L195: `    (∀ iters : Nat,`
  Explanation: start of universal formula for precond1-online total cost over iteration count `iters`.
- L196: `      pcgSolveCostPrecond1Online iters n r q dObs`
  Explanation: this line gives total online PCG cost for precond1.
- L197: `        = n * n * n + n * n * r`
  Explanation: fixed term in precond1-online cost: setup plus initial kernel multiplication.
- L198: `            + iters * (applyMatrixFreeObservedOnlineCost n r q dObs + n * n * r)) ∧`
  Explanation: this line gives iterative term for precond1-online: each iteration pays online matvec cost plus one `n^2 r`-level linear-algebra operation.
- L199: `    (∀ iters : Nat,`
  Explanation: start of universal formula for precond2-online total cost over `iters`.
- L200: `      pcgSolveCostPrecond2Online iters n r q dObs`
  Explanation: this line gives total online PCG cost for precond2.
- L201: `        = (n * n * n + r * r * r) + n * n * r`
  Explanation: fixed term in precond2-online cost: precond2 setup plus initial kernel multiplication.
- L202: `            + iters * (applyMatrixFreeObservedOnlineCost n r q dObs + (n * n * r + n * r * r))) ∧`
  Explanation: iterative term for precond2 has one extra `n r^2`-level term compared to precond1, reflecting extra per-step algebraic overhead of the second preconditioner.
- L203: `    (denseDirectSolveCost n r = n * n * n * r * r * r) := by`
  Explanation: final line writes direct-method cost as `n^3 r^3`, serving as the traditional baseline when comparing against PCG routes.
- L204: `  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩`
  Explanation: split 8 cost equations and handle one by one: first few by direct simplification, later ones by already-proved bridge theorems.
- L205: `  · simp [matVecCost]`
  Explanation: first cost formula needs no substantial reasoning; unfold `matVecCost` by definition and Lean simplifies directly to explicit `n^2 r + q r`.
- L206: `  · simp [rhsFromObservedCost, kernelMulCost, gatherKernelPredictSparseCost]`
  Explanation: second subgoal decomposes RHS cost into kernel multiplication plus gather cost, then `simp` merges them into an explicit polynomial.
- L207: `  · simp [applyMatrixFreeSparseCost, kernelMulCost, gatherKernelPredictSparseCost,`
  Explanation: enter third subgoal: use `simp` to unfold fine-grained sparse matvec cost formula (last cost primitive is completed on next line).
- L208: `      scatterMulSparseCost]`
  Explanation: complete the final cost primitive `scatterMulSparseCost` used by the previous `simp` call.
- L209: `  · exact applyMatrixFreeSparseCost_eq_two_mul_matVecCost n r q`
  Explanation: fourth subgoal directly cites bridge theorem "sparse cost = 2×dominant cost", avoiding manual algebra.
- L210: `  · rfl`
  Explanation: `rfl` is used here because this equation is itself definitional equality: after unfolding both sides are character-by-character identical, with no extra inequalities or algebraic reshaping needed.
- L211: `  · intro iters`
  Explanation: enter fifth subgoal: fix iteration count `iters` and prove precond1-online total cost formula.
- L212: `    simpa using pcgSolveCostPrecond1Online_eq iters n r q dObs`
  Explanation: `simpa using` can be read as "simplify current goal into same shape as an existing theorem, then cite it directly"; this line aligns target with `pcgSolveCostPrecond1Online_eq` and closes in one step.
- L213: `  · intro iters`
  Explanation: enter sixth subgoal: fix `iters` and prove precond2-online total cost formula.
- L214: `    simpa using pcgSolveCostPrecond2Online_eq iters n r q dObs`
  Explanation: similarly, align target to the same form as `pcgSolveCostPrecond2Online_eq` and cite directly to get precond2 total cost.
- L215: `  · exact denseDirectSolveCost_eq n r`
  Explanation: eighth subgoal ends by calling `denseDirectSolveCost_eq`, merging the baseline cost formula into the total package.
- L216: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L217: `/-- \`q10.tex\` Step 9 (PSD closure):`
  Explanation: this is the Step 9 comment header, corresponding to "how PSD case closes back into a usable iterative solver".
- L218: `for PSD kernels, adding any nugget \`nu > 0\` yields SPD (\`K + nu I\`) and opens`
  Explanation: first sentence of Step 9 comment body: when `K` is only PSD, adding any positive nugget (`nu > 0`) gives `K + nu I`, thus moving into SPD framework.
- L219: `PCG certificates on the shifted system. -/`
  Explanation: second sentence states the goal: recover PCG certificate chain on the shifted system.
- L220: `theorem q10_tex_step9_psd_to_shift_core`
  Explanation: Premise: assume only `K` is positive semidefinite and introduce positive shift `nu > 0`; Conclusion: kernel after `withKernelShift` enters positive-definite framework, and key correctness/convergence/complexity conclusions of Step 6/7/8 are moved to shifted system; Role: corresponds to tex Step 9, connecting "PSD case" back to the usable PCG main proof chain.
- L221: `    (P : TexObservedProblem n M r q)`
  Explanation: Step 9 continues on `TexObservedProblem`, meaning shift operation acts directly on a problem instance with fixed observation semantics.
- L222: `    (hKpsd : P.K.PosSemidef)`
  Explanation: this is the weak premise in tex "only assume PSD": no need to assume `K` is inherently positive definite.
- L223: `    (nu : Real)`
  Explanation: `nu` is kernel-shift strength (nugget): mathematically `K ↦ K + nu I`; in Step9 it pushes semidefinite kernels into strict positive-definite framework.
- L224: `    (hNu : 0 < nu) :`
  Explanation: this line requires strict positivity `nu>0`, not decoration: only positive shift guarantees `K + nu I` becomes strictly positive definite, so the SPD certificate chain required by PCG can be connected.
- L225: `    (P.withKernelShift nu).K.PosDef := by`
  Explanation: this line states the shifted positive-definite conclusion PSD->SPD.
- L226: `  exact TexObservedProblem.withKernelShift_posDef_of_posSemidef`
  Explanation: proof itself directly calls `withKernelShift_posDef_of_posSemidef`: PSD plus positive shift implies PD.
- L227: `    (P := P) hKpsd (hNu := hNu)`
  Explanation: this line fully instantiates parameters of theorem called above: problem object is `P`, PSD assumption is `hKpsd`, positive-shift assumption is `hNu`.
- L228: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L229: `/-- Human-readable \`q10.tex\` alignment overview (core, no hidden wrappers):`
  Explanation: this is the human-readable overview comment header: following theorem is specifically for side-by-side reading with tex.
- L230: `this theorem groups the paper-facing statements most readers want to inspect`
  Explanation: comment explains positioning of this theorem: a "single overview entry" for paper readers, concentrating the most important conclusions in one place.
- L231: `first: system equivalence, observed RHS locking, sparse/CSR/online matvec,`
  Explanation: continues listing overview contents: first system equivalence and observed-RHS locking, then sparse/CSR/online matvec relations and cost formulas.
- L232: `and complexity formulas. -/`
  Explanation: last comment sentence confirms this overview covers both algorithm correctness and complexity formulas.
- L233: `theorem q10_tex_human_aligned_overview`
  Explanation: Premise: collect structure/spectrum/cost assumptions needed by Step 1-9; Conclusion: package system equivalence, RHS locking, online equivalence, preconditioner correctness, convergence bounds, and complexity formulas into one conjunction theorem; Role: this is the overview entry for reading tex and Lean side by side, quickly presenting closure of the full chain.
- L234: `    (P : TexObservedProblem n M r q)`
  Explanation: overview-entry parameter is `P`: kernel, observation indices, observed values, and regularization are all gathered in one readable object.
- L235: `    {dObs : Nat}`
  Explanation: `dObs` here is still internal dimension of online row generator; keeping it implicit keeps overview interface clean.
- L236: `    (F : ObsFactorProvider dObs q r)`
  Explanation: overview introduces `F` so the full online-equivalence branch can be included in the same theorem.
- L237: `    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F) :`
  Explanation: `hRows` in overview is validity premise of online module: without it, online and explicit-`Z` routes cannot be merged into one closed loop.
- L238: `    (∀ W : Matrix (Fin n) (Fin r) Real,`
  Explanation: this starts the first core assertion: for arbitrary variable matrix `W`, system equation and matrix-free equation are equivalent.
- L239: `      applyDenseVec P.K P.Z P.Ω P.lam W.vec = rhsFromObserved P.K P.Ω P.vals P.Z`
  Explanation: dense-side equation in the first overview item: substitute `W` into dense operator and compare directly with observation-constructed RHS.
- L240: `        ↔ applyMatrixFreeSparse P.K P.Z P.Ω P.lam W = P.K * sparseMTTKRP P.Ω P.vals P.Z) ∧`
  Explanation: sparse side of the same conclusion: gives matrix-free version equivalent to the dense equation above, with RHS explicitly `K * sparseMTTKRP`.
- L241: `    (rhsVec P.K P.B = rhsFromObserved P.K P.Ω P.vals P.Z) ∧`
  Explanation: this is the second overview item: restate Step 2 RHS locking so all following formulas share one RHS definition.
- L242: `    (∀ W : Matrix (Fin n) (Fin r) Real,`
  Explanation: this starts the third assertion: for arbitrary `W`, CSR(bucketed) matvec equals sparse matvec.
- L243: `      applyMatrixFreeBucketed P.K P.Z P.Ω (canonicalObsBuckets P.Ω) P.lam W`
  Explanation: left side explicitly chooses output under canonical bucket partition, representing engineering execution path rather than abstract operator notation.
- L244: `        = applyMatrixFreeSparse P.K P.Z P.Ω P.lam W) ∧`
  Explanation: this line completes equality between CSR and sparse values, embedding Step 4 into overview theorem.
- L245: `    (∀ W : Matrix (Fin n) (Fin r) Real,`
  Explanation: this starts the fourth assertion: for arbitrary `W`, record and count trace cost of bucketed execution plan.
- L246: `      sparseMatVecTraceCost n r`
  Explanation: this line gives outer cost-count function `sparseMatVecTraceCost n r`; concrete execution trace will be supplied next.
- L247: `        (applyMatrixFreeBucketedPlan P.K P.Z P.Ω (canonicalObsBuckets P.Ω) P.lam W).2`
  Explanation: `.2` takes trace component from bucketed-plan return value, telling Lean we are comparing execution-trace cost, not numeric output itself.
- L248: `          = applyMatrixFreeSparseCost n r q) ∧`
  Explanation: this line gives equality between CSR execution-plan cost and sparse theoretical cost, a key point in implementation-cost closure.
- L249: `    (rhsFromObservedRows P.K P.Ω P.vals (obsRowFromFactors F)`
  Explanation: this line first writes left expression of online RHS: replace observed rows with dynamically generated `obsRowFromFactors F`.
- L250: `      = rhsFromObserved P.K P.Ω P.vals P.Z) ∧`
  Explanation: this line finishes equation "online RHS = explicit RHS" and links to the next statement with `∧`.
- L251: `    (∀ W : Matrix (Fin n) (Fin r) Real,`
  Explanation: starts next "for arbitrary `W`" statement: compare online matvec with sparse matvec.
- L252: `      applyMatrixFreeObserved P.K P.Ω (obsRowFromFactors F) P.lam W`
  Explanation: this line gives left side of online matvec: generate per-observation rows via `obsRowFromFactors F` without explicit construction of large matrix `Z`.
- L253: `        = applyMatrixFreeSparse P.K P.Z P.Ω P.lam W) ∧`
  Explanation: this line binds online observed-row matvec and explicit-`Z` sparse matvec to identical operator output.
- L254: `    (matVecCost n r q = n * n * r + q * r) ∧`
  Explanation: first cost conclusion in overview: directly expand main-scale `matVecCost` into explicit polynomial for line-by-line checking against tex formulas.
- L255: `    (rhsFromObservedCost n r q = n * n * r + q * r) ∧`
  Explanation: second cost conclusion in overview: RHS construction has same shape as main scale, meaning preprocessing does not change dominant complexity order.
- L256: `    (applyMatrixFreeSparseCost n r q = 2 * matVecCost n r q) ∧`
  Explanation: bridge conclusion in overview: fine-grained sparse cost can be compressed into `2 * matVecCost`, aligning implementation-scale and analysis-scale views.
- L257: `    (applyMatrixFreeObservedOnlineCost n r q dObs`
  Explanation: this line starts online per-step cost object, emphasizing online setting must bill both row generation and sparse matvec.
- L258: `      = applyMatrixFreeSparseCost n r q + obsRowFromFactorsGenerationCost dObs q r) := by`
  Explanation: this line is the total decomposition formula for online per-step cost, explicitly written as `sparse cost + row-generation cost`.
- L259: `  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩`
  Explanation: split the 10 sub-conclusions in overview and prove one by one: first 6 are correctness bridges, last 4 are cost formulas.
- L260: `  · intro W`
  Explanation: first subgoal: fix arbitrary `W` and prove system equivalence (dense equation ↔ matrix-free equation).
- L261: `    calc`
  Explanation: `calc` here rewrites "dense equation + observed RHS" step by step into "matrix-free equation + sparse MTTKRP RHS"; this is not formatting, but the key semantic-conversion main chain in the overview theorem.
- L262: `      applyDenseVec P.K P.Z P.Ω P.lam W.vec = rhsFromObserved P.K P.Ω P.vals P.Z`
  Explanation: first `calc` line writes target as "dense LHS = observed RHS", as the starting point for later RHS rewriting of `rhsFromObserved`.
- L263: `          ↔ applyDenseVec P.K P.Z P.Ω P.lam W.vec`
  Explanation: keep dense LHS unchanged first, and prepare rewriting RHS into `rhsVec` form so the main bridge theorem can be applied.
- L264: `              = rhsVec P.K (sparseMTTKRP P.Ω P.vals P.Z) := by`
  Explanation: rewrite RHS into `rhsVec` form and open a local proof block, aiming to embed Step 2 RHS-locking into Step 1 system-equivalence template.
- L265: `                simp [rhsVec, rhsFromObserved]`
  Explanation: unfold both `rhsVec` and `rhsFromObserved` to the same base expression (essentially both return to RHS vector constructed from observations), removing RHS-notation differences so Step 1 bridge theorem can be applied seamlessly next.
- L266: `      _ ↔ applyMatrixFreeSparse P.K P.Z P.Ω P.lam W = P.K * sparseMTTKRP P.Ω P.vals P.Z :=`
  Explanation: second `calc` step directly switches equivalence into matrix-free expression, completing the main jump from dense narrative to sparse narrative.
- L267: `            q10_mainline_system_equiv_matrixFree`
  Explanation: call mainline equivalence theorem `q10_mainline_system_equiv_matrixFree`, the exact bridge for "dense system ↔ matrix-free system".
- L268: `              (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam)`
  Explanation: bind bridge theorem to current problem data: kernel `K`, feature matrix `Z`, observation index `Ω`, regularization `lam`.
- L269: `              (hK := P.hK) (W := W) (B := sparseMTTKRP P.Ω P.vals P.Z)`
  Explanation: continue binding remaining parameters: kernel-property witness `hK`, unknown `W`, and observation-constructed RHS `B := sparseMTTKRP ...`.
- L270: `  · exact P.rhsVec_eq_rhsFromObserved`
  Explanation: second subgoal closes directly: use built-in equation in `P` that locks RHS source.
- L271: `  · intro W`
  Explanation: third subgoal: fix arbitrary `W` and prove canonical CSR output equals sparse matvec output.
- L272: `    exact applyMatrixFreeCanonicalBucketed_eq_sparse`
  Explanation: third subgoal directly reuses canonical-bucket equivalence lemma.
- L273: `      (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (W := W)`
  Explanation: this line only instantiates lemma "canonical bucketed = sparse" with current `(K,Z,Ω,lam,W)`.
- L274: `  · intro W`
  Explanation: fourth subgoal: fix arbitrary `W` and prove canonical CSR plan cost equals sparse cost.
- L275: `    exact applyMatrixFreeCanonicalBucketedPlan_cost_eq`
  Explanation: fourth subgoal directly calls cost-equivalence lemma.
- L276: `      (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam) (W := W)`
  Explanation: instantiate lemma "bucketed execution-plan cost = sparse matvec cost" with current `K,Z,Ω,lam,W`.
- L277: `  · exact rhsFromObservedRows_from_factors_eq_rhsFromObserved`
  Explanation: fifth subgoal directly calls online RHS bridge theorem, aligning "dynamic row generation" and "explicit `Z`" RHS routes.
- L278: `      (K := P.K) (Ω := P.Ω) (vals := P.vals) (Z := P.Z) (F := F) (hRows := hRows)`
  Explanation: parameterize theorem "RHS built online from factors equals explicit RHS": fix `K,Ω,vals,Z`, pass factor provider `F` and consistency assumption `hRows`.
- L279: `  · intro W`
  Explanation: sixth subgoal: fix arbitrary `W` and prove online observed-row matvec equals sparse matvec.
- L280: `    exact applyMatrixFreeObserved_from_factors_eq_sparse`
  Explanation: sixth subgoal directly applies online row-generation equivalence lemma.
- L281: `      (K := P.K) (Z := P.Z) (Ω := P.Ω) (F := F) (hRows := hRows)`
  Explanation: pass static parameters `K,Z,Ω,F,hRows` to lemma "online matvec = sparse matvec".
- L282: `      (lam := P.lam) (W := W)`
  Explanation: continue filling dynamic parameters for that lemma: regularization `lam` and current iteration variable `W`.
- L283: `  · simp [matVecCost]`
  Explanation: seventh subgoal reproves in overview that `matVecCost = n^2 r + q r`.
- L284: `  · simp [rhsFromObservedCost, kernelMulCost, gatherKernelPredictSparseCost]`
  Explanation: eighth subgoal decomposes RHS cost into basic cost terms and simplifies automatically into explicit formula.
- L285: `  · exact applyMatrixFreeSparseCost_eq_two_mul_matVecCost n r q`
  Explanation: ninth subgoal reuses sparse-vs-dominant cost bridge theorem to conclude the "2x" relation.
- L286: `  · rfl`
  Explanation: final subgoal is identical after definition unfolding, so `rfl` closes directly.
- L287: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L288: `/-- \`q10.tex\` Step 10 (default-package component #1):`
  Explanation: comment line: Step 10 starts here, entering the first component of default delivery package.
- L289: `minimal-input spectral-indexed ambient-\`N\` complete certificate. -/`
  Explanation: comment body: this component is a complete certificate with "minimal input + spectral index + ambient-`N`".
- L290: `def q10_tex_step10_default_core`
  Explanation: Premise: explicitly list assumptions `P,F,hRows,hScale`, spectral interval, error parameters, positivity/semi-definiteness of `lam` and `K`; Conclusion: export Step10 main certificate from `TexAnswer` under a local name as one `def` object; Role: this is component #1 of default delivery package, carrying the main certificate for "minimal input + spectral index + ambient-N".
- L291: `    (P : TexObservedProblem n M r q)`
  Explanation: introduce problem object `P`, which already contains observation semantics and RHS-locking information.
- L292: `    {dObs : Nat}`
  Explanation: introduce implicit dimension parameter `dObs` for online row-generation interface.
- L293: `    (F : ObsFactorProvider dObs q r)`
  Explanation: introduce online factor provider `F`: it generates needed row data on demand by observation index, and is the core interface for proving equivalence between online route and explicit-`Z` route.
- L294: `    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)`
  Explanation: introduce consistency assumption that online row generation and explicit `Z` agree on observed points.
- L295: `    (hScale : n < q ∧ r < q ∧ q < n * M)`
  Explanation: introduce size-relation assumption, fixing sparse-scale interval of the statement.
- L296: `    (mu L err0 eps : Real)`
  Explanation: introduce spectral-interval and error parameters `mu,L,err0,eps`.
- L297: `    (hMuPos : 0 < mu)`
  Explanation: require `mu>0` so spectral interval is away from zero, preventing instability at boundaries in later convergence/condition-number expressions.
- L298: `    (hMuLtL : mu < L)`
  Explanation: require `mu < L` so `[mu,L]` is a real interval rather than a degenerate point, giving substantial meaning to later `Set.Icc mu L` constraints.
- L299: `    (hErr0 : 0 < err0)`
  Explanation: require `err0>0`, ensuring initial-error upper bound is a meaningful positive scale used in multiplicative residual bounds.
- L300: `    (hEps : 0 < eps)`
  Explanation: require `eps>0`, fixing target-precision threshold as a valid positive value and avoiding degenerate stopping criteria.
- L301: `    (hLamNonneg : 0 ≤ P.lam)`
  Explanation: require `lam≥0`, matching basic feasibility of kernel-ridge-style regularization and consistent with assumptions in later spectral/cost results.
- L302: `    (hKpsd : P.K.PosSemidef)`
  Explanation: require `K` positive semidefinite, the basic structural premise of kernel methods and the starting point for the later "shift to SPD" route.
- L303: `    (hLamPos : 0 < P.lam) :=`
  Explanation: additionally require `λ>0`, and finish signature on this line.
- L304: `  q10_tex_complete_solution_certificate_minimal_input_spectralIndexed_ambientN`
  Explanation: definition body directly reuses the corresponding total-certificate object.
- L305: `    (P := P) (F := F) (hRows := hRows) (hScale := hScale)`
  Explanation: pass problem object, online interface, and structural assumptions.
- L306: `    (mu := mu) (L := L) (err0 := err0) (eps := eps)`
  Explanation: pass spectral-interval and error parameters further down; these appear directly in residual upper-bound and stopping-threshold formulas.
- L307: `    (hMuPos := hMuPos) (hMuLtL := hMuLtL)`
  Explanation: pass spectral-interval validity assumptions (positivity/order of endpoints), ensuring polynomial upper bounds are evaluated on a valid interval.
- L308: `    (hErr0 := hErr0) (hEps := hEps)`
  Explanation: pass positivity of `err0,eps` into target certificate, ensuring both sides of error-comparison formulas have correct scale and sign.
- L309: `    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)`
  Explanation: pass regularization and kernel assumptions, completing Step10 core.
- L310: ``
  Explanation: blank line: only layout separation, no mathematical content.
- L311: `/-- Step 10 display form (same content as Step 10 core, but written in the`
  Explanation: comment line: below is Step10 display version.
- L312: `same explicit parameter style as Step 9 for human reading). -/`
  Explanation: comment body: display version only expands parameter writing style, without changing mathematical content.
- L313: `def q10_tex_step10_default_core_display`
  Explanation: this line defines display entry for Step10: mathematically identical to Step10 core, but keeps parameter list in explicit form for item-by-item reader checking; for tex cross-reading, this lowers cognitive load from hidden implicit parameters.
- L314: `    (P : TexObservedProblem n M r q)`
  Explanation: fix problem instance `P`; all later `K,Ω,Z,lam` are read from `P`, letting readers confirm closure in one problem object.
- L315: `    {dObs : Nat}`
  Explanation: add auxiliary internal dimension `dObs` (implicit); it serves type matching and does not change mathematical objects seen in tex.
- L316: `    (F : ObsFactorProvider dObs q r)`
  Explanation: give online factor provider `F`, the key interface for comparing online implementation with explicit-`Z` implementation.
- L317: `    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)`
  Explanation: introduce consistency assumption between online and explicit rows.
- L318: `    (hScale : n < q ∧ r < q ∧ q < n * M)`
  Explanation: give scale interval `n < q ∧ r < q ∧ q < n*M`, fixing sparse-size regime discussed in tex and keeping later certificates consistent with mainline assumptions.
- L319: `    (mu L err0 eps : Real)`
  Explanation: explicitly write `mu,L,err0,eps` into signature: first two control spectral interval, latter two control initial error and target precision.
- L320: `    (hMuPos : 0 < mu)`
  Explanation: add premise `mu>0` to keep interval lower bound away from zero and maintain stability of ratio terms in later interval estimates.
- L321: `    (hMuLtL : mu < L)`
  Explanation: add `mu<L` so spectral interval has width and later `Icc` bounds are non-degenerate.
- L322: `    (hErr0 : 0 < err0)`
  Explanation: add `err0>0`, fixing initial error scale as a positive quantity for later multiplicative bounds.
- L323: `    (hEps : 0 < eps)`
  Explanation: add `eps>0`, ensuring "achieve target precision" is a decidable positive threshold.
- L324: `    (hLamNonneg : 0 ≤ P.lam)`
  Explanation: add `lam≥0`, ensuring regularization does not break PSD structure and stays compatible with mainline assumptions.
- L325: `    (hKpsd : P.K.PosSemidef)`
  Explanation: add PSD premise on `K`, the basic structure of kernel-matrix model and also support for shift-to-SPD branch.
- L326: `    (hLamPos : 0 < P.lam) :=`
  Explanation: introduce `λ>0` and finish display signature.
- L327: `  q10_tex_step10_default_core`
  Explanation: display definition body directly calls Step10 core.
- L328: `    (P := P) (F := F) (hRows := hRows) (hScale := hScale)`
  Explanation: pass problem object and structural premises unchanged to target certificate; this is interface packaging, not proposition change.
- L329: `    (mu := mu) (L := L) (err0 := err0) (eps := eps)`
  Explanation: pass spectral interval and error parameters further down; these appear directly in residual upper-bound and stopping-threshold formulas.
- L330: `    (hMuPos := hMuPos) (hMuLtL := hMuLtL)`
  Explanation: pass spectral-interval validity (positivity/order of endpoints), ensuring polynomial upper bounds are evaluated on a valid interval.
- L331: `    (hErr0 := hErr0) (hEps := hEps)`
  Explanation: pass positivity of `err0,eps`, ensuring both sides of error-comparison formulas carry correct scale and sign.
- L332: `    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)`
  Explanation: pass regularization and kernel assumptions, completing mapping from display to core.
- L333: ``
  Explanation: blank line: separate Step10 and Step11.
- L334: `/-- \`q10.tex\` Step 11 (default-package component #2):`
  Explanation: comment header marks start of Step11: from here we enter "online-closure certificate" module, which can be viewed as online extension of Step10 main certificate.
- L335: `closed-loop online spectral-indexed ambient-\`N\` certificate. -/`
  Explanation: comment body: this component corresponds to online closed-loop certificate.
- L336: `def q10_tex_step11_default_online_closure`
  Explanation: Premise: inherit Step10 base assumptions while retaining online row-generation consistency; Conclusion: export main online-closure certificate (online row generation, online matvec, and online cost all certifiable); Role: this is component #2 in default delivery package, corresponding to tex Step11 claim that "online route is also closed".
- L337: `    (P : TexObservedProblem n M r q)`
  Explanation: fix problem instance `P`; all later `K,Ω,Z,lam` are read from `P`, letting readers confirm closure in one problem object.
- L338: `    {dObs : Nat}`
  Explanation: add internal dimension `dObs` for online observed-row provider (implicit parameter); it does not change mathematics, only lets Lean typecheck `F` correctly.
- L339: `    (F : ObsFactorProvider dObs q r)`
  Explanation: give online factor provider `F`, which generates rows on demand by observation index and is key interface for online-vs-explicit `Z` equivalence.
- L340: `    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)`
  Explanation: add consistency premise: rows generated by `F` match explicit `Z` at observation locations; otherwise online and explicit routes cannot be proven value-equivalent.
- L341: `    (hScale : n < q ∧ r < q ∧ q < n * M)`
  Explanation: give size interval `n < q ∧ r < q ∧ q < n*M`, fixing sparse-size regime discussed in tex and ensuring later certificates align with mainline assumptions.
- L342: `    (mu L err0 eps : Real)`
  Explanation: explicitly list spectral-interval and error parameters; these determine numerical shape of later convergence bounds and stopping-accuracy inequalities.
- L343: `    (hMuPos : 0 < mu)`
  Explanation: write `mu>0` explicitly, ensuring interval lower bound does not touch zero and preserving stability of later interval estimates.
- L344: `    (hMuLtL : mu < L)`
  Explanation: write `mu<L` explicitly, ensuring spectral interval has width and related `Icc` constraints are not vacuous.
- L345: `    (hErr0 : 0 < err0)`
  Explanation: write `err0>0` explicitly, ensuring initial error scale can be used directly in subsequent inequalities.
- L346: `    (hEps : 0 < eps)`
  Explanation: write `eps>0` explicitly, indicating we target a non-degenerate positive accuracy goal.
- L347: `    (hLamNonneg : 0 ≤ P.lam)`
  Explanation: add `lam≥0`, ensuring regularization does not break PSD structure and remains compatible with mainline assumptions.
- L348: `    (hKpsd : P.K.PosSemidef)`
  Explanation: add PSD premise on `K`; this is the base structure of kernel-matrix model and also supports shift-to-SPD branch.
- L349: `    (hLamPos : 0 < P.lam) :=`
  Explanation: introduce `λ>0` and finish Step11 signature.
- L350: `  q10_tex_complete_solution_certificate_closed_loop_online_minimal_input_spectralIndexed_ambientN`
  Explanation: definition body directly binds to the total online-closure certificate object.
- L351: `    (P := P) (F := F) (hRows := hRows) (hScale := hScale)`
  Explanation: pass object, interface, and structural assumptions.
- L352: `    (mu := mu) (L := L) (err0 := err0) (eps := eps)`
  Explanation: pass spectral-interval and error parameters further down; these appear directly in residual upper-bound and stopping-threshold formulas.
- L353: `    (hMuPos := hMuPos) (hMuLtL := hMuLtL)`
  Explanation: pass spectral-interval validity (positivity/order of endpoints), ensuring polynomial upper bounds are evaluated on a valid interval.
- L354: `    (hErr0 := hErr0) (hEps := hEps)`
  Explanation: pass positivity of `err0,eps` into target certificate, ensuring both sides of error-comparison formulas have correct scale and sign.
- L355: `    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)`
  Explanation: pass regularization and kernel assumptions, completing Step11 core.
- L356: ``
  Explanation: blank line: separate Step11 core and display.
- L357: `/-- Step 11 display form (same content as Step 11 online closure,`
  Explanation: comment line: below is Step11 display version.
- L358: `written with explicit human-readable parameters). -/`
  Explanation: comment body: display version keeps conclusions unchanged and only expands parameters.
- L359: `def q10_tex_step11_default_online_closure_display`
  Explanation: this line gives Step11 display entry: mathematically identical to core, but all parameters are explicit so readers can directly check each assumption against tex line by line; role is a more friendly reading interface for the online-closure certificate.
- L360: `    (P : TexObservedProblem n M r q)`
  Explanation: fix problem instance `P`; all later `K,Ω,Z,lam` are read from `P`, letting readers confirm closure in one problem object.
- L361: `    {dObs : Nat}`
  Explanation: add internal dimension `dObs` for online observed-row provider (implicit); it does not change mathematics and only allows Lean to type `F` correctly.
- L362: `    (F : ObsFactorProvider dObs q r)`
  Explanation: give online factor provider `F`, generating rows on demand by observation index and acting as key interface for comparing online and explicit-`Z` implementations.
- L363: `    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)`
  Explanation: add consistency premise: rows generated by `F` match explicit `Z` at `Ω` positions; otherwise online and explicit routes cannot be proven equal.
- L364: `    (hScale : n < q ∧ r < q ∧ q < n * M)`
  Explanation: this line separately introduces size interval `n < q ∧ r < q ∧ q < n*M`: mathematically it restricts to regime "observations are sufficiently many but still sparse"; in Step11 display context, it keeps online-closure certificate fully isomorphic to Step10 on scale assumptions for line-by-line comparison.
- L365: `    (mu L err0 eps : Real)`
  Explanation: continue Step11 display parameter list with spectral-interval and error parameters.
- L366: `    (hMuPos : 0 < mu)`
  Explanation: require `mu>0`, so interval stays away from 0 and ratio/condition-number expressions in convergence bounds do not degenerate at boundary.
- L367: `    (hMuLtL : mu < L)`
  Explanation: require `mu < L`, ensuring `[mu,L]` is a valid interval rather than degenerate point, so later `Set.Icc mu L` spectral constraints are substantial.
- L368: `    (hErr0 : 0 < err0)`
  Explanation: require `err0>0`, so scaling factor in error upper bounds is an interpretable positive quantity and residual bounds remain symbolically meaningful.
- L369: `    (hEps : 0 < eps)`
  Explanation: require `eps>0`, fixing stopping threshold as a valid accuracy target and avoiding distortion from nonpositive tolerance.
- L370: `    (hLamNonneg : 0 ≤ P.lam)`
  Explanation: require `lam≥0`, matching feasibility baseline of kernel-ridge regularization and staying consistent with assumptions of later spectral/cost results.
- L371: `    (hKpsd : P.K.PosSemidef)`
  Explanation: require `K` positive semidefinite, the foundational structural premise in kernel methods and starting point for later shift-to-SPD route.
- L372: `    (hLamPos : 0 < P.lam) :=`
  Explanation: require `λ>0` and finish Step11 display signature.
- L373: `  q10_tex_step11_default_online_closure`
  Explanation: display definition body directly calls Step11 core.
- L374: `    (P := P) (F := F) (hRows := hRows) (hScale := hScale)`
  Explanation: pass object, online interface, and structural assumptions.
- L375: `    (mu := mu) (L := L) (err0 := err0) (eps := eps)`
  Explanation: pass spectral interval and error parameters further down; these appear directly in residual upper-bound and stopping-threshold formulas.
- L376: `    (hMuPos := hMuPos) (hMuLtL := hMuLtL)`
  Explanation: pass spectral-interval validity (positivity/order of endpoints), ensuring polynomial upper bounds are evaluated on a valid interval.
- L377: `    (hErr0 := hErr0) (hEps := hEps)`
  Explanation: pass positivity of `err0,eps`, ensuring both sides of error-comparison formulas have correct scale and sign.
- L378: `    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)`
  Explanation: pass regularization and kernel assumptions, completing Step11 display.
- L379: ``
  Explanation: blank line: separate Step11 and Step12.
- L380: `/-- \`q10.tex\` Step 12 (default-package component #3):`
  Explanation: comment line: Step12 starts, focusing on closure after PSD is shifted.
- L381: `PSD-to-shifted-PCG spectral-indexed ambient-\`N\` closure. -/`
  Explanation: comment body: this component handles shifted-PCG certificate for PSD case.
- L382: `def q10_tex_step12_default_shifted_pcg`
  Explanation: Premise: besides Step10 base assumptions, additionally introduce kernel-shift parameter `nu > 0`; Conclusion: export closure certificate object for "PSD -> shift -> PCG usable"; Role: this is component #3 of default delivery package, bringing weak-premise PSD case into main chain.
- L383: `    (P : TexObservedProblem n M r q)`
  Explanation: fix problem instance `P`; all later `K,Ω,Z,lam` are read from `P`, letting readers confirm closure in one problem object.
- L384: `    {dObs : Nat}`
  Explanation: add auxiliary internal dimension `dObs` (implicit); it serves type matching and does not change mathematical objects seen in tex.
- L385: `    (F : ObsFactorProvider dObs q r)`
  Explanation: give online factor provider `F`, generating rows on demand by observation index and acting as key interface for comparing online and explicit-`Z` implementations.
- L386: `    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)`
  Explanation: introduce consistency assumption for online row generation.
- L387: `    (hScale : n < q ∧ r < q ∧ q < n * M)`
  Explanation: give size interval `n < q ∧ r < q ∧ q < n*M`, fixing sparse-size regime discussed in tex and keeping later certificates consistent with mainline assumptions.
- L388: `    (mu L err0 eps : Real)`
  Explanation: explicitly list spectral-interval and error parameters; these determine numerical shape of later convergence bounds and stopping-accuracy inequalities.
- L389: `    (hMuPos : 0 < mu)`
  Explanation: require `mu>0`, so interval stays away from 0 and ratio/condition-number expressions in convergence bounds do not degenerate at boundary.
- L390: `    (hMuLtL : mu < L)`
  Explanation: require `mu<L`, ensuring interval comparison and polynomial upper bounds are evaluated on a non-degenerate interval.
- L391: `    (hErr0 : 0 < err0)`
  Explanation: require `err0>0`, so scaling factor in error upper bounds is an interpretable positive quantity and residual bounds remain symbolically meaningful.
- L392: `    (hEps : 0 < eps)`
  Explanation: require `eps>0`, fixing stopping threshold as a valid accuracy target and avoiding distortion from nonpositive tolerance.
- L393: `    (hLamNonneg : 0 ≤ P.lam)`
  Explanation: require `lam≥0`, matching feasibility baseline of kernel-ridge regularization and staying consistent with assumptions of later spectral/cost results.
- L394: `    (hKpsd : P.K.PosSemidef)`
  Explanation: require `K` positive semidefinite, the foundational structural premise in kernel methods and starting point for later shift-to-SPD route.
- L395: `    (hLamPos : 0 < P.lam)`
  Explanation: require `lam>0`, so inverse actions and spectral-bound estimates related to preconditioners are legally usable.
- L396: `    (nu : Real)`
  Explanation: introduce kernel-shift amplitude parameter `nu`.
- L397: `    (hNu : 0 < nu) :=`
  Explanation: require `nu>0` to guarantee the shift truly pushes PSD kernel into SPD; this line also finishes the definition signature.
- L398: `  q10_tex_psd_to_shifted_pcg_certificate_minimal_input_spectralIndexed_ambientN`
  Explanation: definition body directly calls Step12 shifted-PCG total certificate.
- L399: `    (P := P) (F := F) (hRows := hRows) (hScale := hScale)`
  Explanation: pass object, online interface, and structural assumptions.
- L400: `    (mu := mu) (L := L) (err0 := err0) (eps := eps)`
  Explanation: pass spectral interval and error parameters further down; these appear directly in residual upper-bound and stopping-threshold formulas.
- L401: `    (hMuPos := hMuPos) (hMuLtL := hMuLtL)`
  Explanation: pass spectral-interval validity (positivity/order of endpoints), ensuring polynomial upper bounds are evaluated on a valid interval.
- L402: `    (hErr0 := hErr0) (hEps := hEps)`
  Explanation: pass positivity of `err0,eps`, ensuring both sides of error-comparison formulas have correct scale and sign.
- L403: `    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)`
  Explanation: fully pass structural assumptions on `lam` and `K`, keeping this wrapper assumption-by-assumption identical to the main certificate.
- L404: `    (nu := nu) (hNu := hNu)`
  Explanation: pass shift parameter and positivity condition, completing Step12 core.
- L405: ``
  Explanation: blank line: separate Step12 core and display.
- L406: `/-- Step 12 display form (same content as Step 12 shifted-PCG closure,`
  Explanation: comment line: below is Step12 display version.
- L407: `written with explicit human-readable parameters). -/`
  Explanation: comment body: display version only expands interface.
- L408: `def q10_tex_step12_default_shifted_pcg_display`
  Explanation: this line defines Step12 display entry: content is identical to core, but key parameters like `nu` and `hNu` are explicit; role is to help readers see directly where shift parameters are used in closure certificate.
- L409: `    (P : TexObservedProblem n M r q)`
  Explanation: fix problem instance `P`; all later `K,Ω,Z,lam` are read from `P`, letting readers confirm closure in one problem object.
- L410: `    {dObs : Nat}`
  Explanation: add internal dimension `dObs` for online observed-row provider (implicit); it does not change mathematics and only allows Lean to type `F` correctly.
- L411: `    (F : ObsFactorProvider dObs q r)`
  Explanation: give online factor provider `F`, generating rows on demand by observation index and acting as key interface for comparing online and explicit-`Z` implementations.
- L412: `    (hRows : factorsGenerateObservedRows (Ω := P.Ω) (Z := P.Z) F)`
  Explanation: add consistency premise: rows generated by `F` match explicit `Z` at `Ω` positions; otherwise online and explicit routes cannot be proven equal.
- L413: `    (hScale : n < q ∧ r < q ∧ q < n * M)`
  Explanation: give size interval `n < q ∧ r < q ∧ q < n*M`, fixing sparse-size regime discussed in tex and ensuring later certificates align with mainline assumptions.
- L414: `    (mu L err0 eps : Real)`
  Explanation: explicitly list spectral-interval and error parameters; these determine numerical shape of later convergence bounds and stopping-accuracy inequalities.
- L415: `    (hMuPos : 0 < mu)`
  Explanation: require `mu>0`, so interval stays away from 0 and ratio/condition-number expressions in convergence bounds do not degenerate at boundary.
- L416: `    (hMuLtL : mu < L)`
  Explanation: require `mu<L`, ensuring interval comparison and polynomial upper bounds are evaluated on a non-degenerate interval.
- L417: `    (hErr0 : 0 < err0)`
  Explanation: require `err0>0`, so scaling factor in error upper bounds is an interpretable positive quantity and residual bounds remain symbolically meaningful.
- L418: `    (hEps : 0 < eps)`
  Explanation: require `eps>0`, preventing target-precision threshold from degenerating into meaningless comparison.
- L419: `    (hLamNonneg : 0 ≤ P.lam)`
  Explanation: require `lam≥0`, maintaining compatibility between regularization and kernel structure.
- L420: `    (hKpsd : P.K.PosSemidef)`
  Explanation: require `K` positive semidefinite, the foundational structural premise in kernel methods and starting point for later shift-to-SPD route.
- L421: `    (hLamPos : 0 < P.lam)`
  Explanation: require `lam>0`, ensuring steps involving inverses or condition numbers do not degenerate at zero regularization.
- L422: `    (nu : Real)`
  Explanation: introduce shift value `nu`, the explicit control variable for converting PSD kernel to SPD kernel.
- L423: `    (hNu : 0 < nu) :=`
  Explanation: require positive shift parameter and finish signature.
- L424: `  q10_tex_step12_default_shifted_pcg`
  Explanation: display version is mathematically identical to Step12 core; this line only redirects by name, giving a more intuitive entry to the same certificate.
- L425: `    (P := P) (F := F) (hRows := hRows) (hScale := hScale)`
  Explanation: pass problem object and structural assumptions unchanged to target certificate, showing this is interface packaging rather than proposition change.
- L426: `    (mu := mu) (L := L) (err0 := err0) (eps := eps)`
  Explanation: pass spectral interval and error parameters further down; these appear directly in residual upper-bound and stopping-threshold formulas.
- L427: `    (hMuPos := hMuPos) (hMuLtL := hMuLtL)`
  Explanation: pass spectral-interval validity (positivity/order of endpoints), ensuring polynomial upper bounds are evaluated on a valid interval.
- L428: `    (hErr0 := hErr0) (hEps := hEps)`
  Explanation: pass positivity of `err0,eps`, ensuring both sides of error-comparison formulas have correct scale and sign.
- L429: `    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd) (hLamPos := hLamPos)`
  Explanation: fully pass structural assumptions on `lam` and `K`, keeping this wrapper assumption-by-assumption identical to the main certificate.
- L430: `    (nu := nu) (hNu := hNu)`
  Explanation: pass shift parameter and positivity condition.
- L431: ``
  Explanation: blank line: separate Step12 and Step13.
- L432: `/-- \`q10.tex\` Step 13 (default-package component #4):`
  Explanation: comment header marks Step13 start: this segment switches to the poly-envelope tolerance route and no longer depends on stepwise error narration.
- L433: `non-stepwise polynomial-envelope tolerance closure. -/`
  Explanation: comment body: this component corresponds to non-stepwise polynomial-envelope tolerance closure.
- L434: `def q10_tex_step13_default_poly_envelope`
  Explanation: Premise: given `mu,L,eps` together with `mu>0, mu<L, eps>0, lam>0`; Conclusion: export non-stepwise poly-envelope tolerance-closure certificate; Role: this is component #4 of default delivery package, corresponding to error-control route in tex Step13.
- L435: `    (P : TexObservedProblem n M r q)`
  Explanation: fix problem instance `P`; all later `K,Ω,Z,lam` are read from `P`, letting readers confirm closure in one problem object.
- L436: `    (mu L eps : Real)`
  Explanation: write `mu,L,eps`: first two define spectral interval, `eps` gives final error target.
- L437: `    (hMuPos : 0 < mu)`
  Explanation: require `mu>0`, so interval stays away from 0 and ratio/condition-number expressions in convergence bounds do not degenerate at boundary.
- L438: `    (hMuLtL : mu < L)`
  Explanation: require `mu<L`, ensuring interval comparison and polynomial upper bounds are evaluated on a non-degenerate interval.
- L439: `    (hEps : 0 < eps)`
  Explanation: require `eps>0`, fixing stopping threshold as a valid accuracy target and avoiding distortion from nonpositive tolerance.
- L440: `    (hLamPos : 0 < P.lam) :=`
  Explanation: require `λ>0` and finish Step13 signature.
- L441: `  q10_tex_complete_solution_certificate_polyEnvelope_closure_spectralIndexed`
  Explanation: definition body directly binds to the corresponding certificate of Step13.
- L442: `    (P := P) (mu := mu) (L := L) (eps := eps)`
  Explanation: pass problem object and real parameters unchanged to target certificate, keeping branch conclusion fully identical to core.
- L443: `    (hMuPos := hMuPos) (hMuLtL := hMuLtL)`
  Explanation: pass spectral-interval validity (positivity/order of endpoints), ensuring polynomial upper bounds are evaluated on a valid interval.
- L444: `    (hEps := hEps) (hLamPos := hLamPos)`
  Explanation: pass tolerance and regularization-positivity assumptions, completing Step13 core.
- L445: ``
  Explanation: blank line: separate Step13 core and display.
- L446: `/-- Step 13 display form (same content as Step 13 poly-envelope closure,`
  Explanation: comment line: below is Step13 display version.
- L447: `written with explicit human-readable parameters). -/`
  Explanation: comment body: display version only expands parameter style.
- L448: `def q10_tex_step13_default_poly_envelope_display`
  Explanation: this line defines Step13 display entry: keep full value identity with core, but fully expand parameters and positivity conditions; role is to let mathematical readers verify this branch assumption set without tracking implicit parameters.
- L449: `    (P : TexObservedProblem n M r q)`
  Explanation: fix problem instance `P`; all later `K,Ω,Z,lam` are read from `P`, letting readers confirm closure in one problem object.
- L450: `    (mu L eps : Real)`
  Explanation: write `mu,L,eps`: first two define spectral interval, `eps` gives final error target.
- L451: `    (hMuPos : 0 < mu)`
  Explanation: require `mu>0`, so interval stays away from 0 and ratio/condition-number expressions in convergence bounds do not degenerate at boundary.
- L452: `    (hMuLtL : mu < L)`
  Explanation: require `mu<L`, ensuring interval comparison and polynomial upper bounds are evaluated on a non-degenerate interval.
- L453: `    (hEps : 0 < eps)`
  Explanation: require `eps>0`, preventing target-precision threshold from degenerating into meaningless comparison.
- L454: `    (hLamPos : 0 < P.lam) :=`
  Explanation: require `λ>0` and finish display signature.
- L455: `  q10_tex_step13_default_poly_envelope`
  Explanation: display entry is fully value-identical to Step13 core; this line only switches the reading entry name back to core object and introduces no new assumption.
- L456: `    (P := P) (mu := mu) (L := L) (eps := eps)`
  Explanation: pass problem object and real parameters unchanged to target certificate, keeping branch conclusion fully identical to core.
- L457: `    (hMuPos := hMuPos) (hMuLtL := hMuLtL)`
  Explanation: pass positivity of `mu` and endpoint order to target certificate, ensuring interval upper-bound conditions stay usable.
- L458: `    (hEps := hEps) (hLamPos := hLamPos)`
  Explanation: pass tolerance and regularization-positivity assumptions.
- L459: ``
  Explanation: blank line: separate Step13 and Step14.
- L460: `/-- \`q10.tex\` Step 14 (default-package component #5):`
  Explanation: comment line: Step14 starts, handling spectral-interval binding.
- L461: `spectral-interval binding to concrete preconditioned operators. -/`
  Explanation: comment body: this component binds spectral-interval conditions to concrete preconditioned operators.
- L462: `theorem q10_tex_step14_default_spectral_binding`
  Explanation: Premise: require `mu ≤ L`, `lam > 0`, `K` positive definite, and symmetry plus spectral inclusion `spectrum ⊆ [mu,L]` for preconditioner-1/2 linear operators; Conclusion: both preconditioned PCG residual upper bounds hold simultaneously and are valid for arbitrary step `k`; Role: this is component #5 in default delivery package, binding abstract spectral conditions into directly usable convergence estimates.
- L463: `    (P : TexObservedProblem n M r q)`
  Explanation: fix problem instance `P`; all later `K,Ω,Z,lam` are read from `P`, letting readers confirm closure in one problem object.
- L464: `    (mu L : Real)`
  Explanation: explicitly give interval endpoints `mu,L`; all following spectral-inclusion statements are around this closed interval.
- L465: `    (hMuLeL : mu ≤ L)`
  Explanation: require `mu ≤ L`, making spectral inclusion `⊆ [mu,L]` a valid comparison object.
- L466: `    (hLamPos : 0 < P.lam)`
  Explanation: require `lam>0`, ensuring steps involving inverses or condition numbers do not degenerate at zero regularization.
- L467: `    (hKpos : P.K.PosDef)`
  Explanation: require `K` positive definite so key operators in preconditioned system are invertible and stable.
- L468: `    (hSymm1 :`
  Explanation: start symmetry assumption for precond1 linear operator.
- L469: `      (LinearMap.toMatrixAlgEquiv'`
  Explanation: write matrixized object corresponding to precond1.
- L470: `            (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem)))ᵀ`
  Explanation: explicitly write transpose of the operator, in order to declare later the symmetry condition "transpose = itself".
- L471: `        = LinearMap.toMatrixAlgEquiv'`
  Explanation: start right-hand side of symmetry equality (operator body); paired with upper transpose line this forms `Aᵀ = A`.
- L472: `            (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem)))`
  Explanation: right side is the object itself, completing the "transpose equals itself" form.
- L473: `    (hEigRange1 :`
  Explanation: start spectral-interval assumption for precond1.
- L474: `      spectrum ℝ`
  Explanation: declare spectrum is taken over real field `ℝ`, avoiding semantic drift from different base fields.
- L475: `          (LinearMap.toMatrixAlgEquiv'`
  Explanation: make explicit which matrix object spectrum is taken from, preventing confusion between abstract linear maps and concrete matrix spectra.
- L476: `            (precondDenseVecLin P.toProblem (precond1ApplyLin P.toProblem)))`
  Explanation: continue writing the full matrix object under spectrum, ensuring readers can verify it matches current preconditioner.
- L477: `        ⊆ Set.Icc mu L)`
  Explanation: this line formally writes spectral-interval assumption as set inclusion `spectrum ⊆ [mu,L]`; it is the key bridge from abstract operator properties to residual-upper-bound inequalities.
- L478: `    (hSymm2 :`
  Explanation: start symmetry assumption for precond2.
- L479: `      (LinearMap.toMatrixAlgEquiv'`
  Explanation: write matrixized object for precond2.
- L480: `            (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem)))ᵀ`
  Explanation: explicitly write transpose of precond2 matrixized operator so the next line can pair it with the operator itself to form symmetry.
- L481: `        = LinearMap.toMatrixAlgEquiv'`
  Explanation: start right-hand side of symmetry equality (operator body); together with the upper transpose line this yields `Aᵀ = A`.
- L482: `            (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem)))`
  Explanation: right side is the object itself, completing precond2 symmetry form.
- L483: `    (hEigRange2 :`
  Explanation: start spectral-interval assumption for precond2.
- L484: `      spectrum ℝ`
  Explanation: declare spectrum is taken over real field `ℝ`, avoiding semantic drift from different base fields.
- L485: `          (LinearMap.toMatrixAlgEquiv'`
  Explanation: make explicit which matrix object precond2 route takes spectrum from, avoiding mixing spectral assumptions across different operators.
- L486: `            (precondDenseVecLin P.toProblem (precond2ApplyLin P.toProblem)))`
  Explanation: continue writing the full matrix object under spectrum, ensuring readers can verify correspondence to current preconditioner.
- L487: `        ⊆ Set.Icc mu L) :`
  Explanation: require spectrum to be included in `[mu,L]` and finish assumption block.
- L488: `    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real,`
  Explanation: first part of conclusion: for arbitrary initial value and initial error-bound constant.
- L489: `      ‖WithLp.toLp 2 (precond1Apply P.toProblem (pcgR0 P.toProblem x0)).vec‖ ≤ err0z →`
  Explanation: if initial residual norm under precond1 does not exceed `err0z`.
- L490: `      ∀ k : Nat,`
  Explanation: then it holds for arbitrary iteration step `k`.
- L491: `        pcgResidualNorm P.toProblem (precond1Apply P.toProblem) x0 k`
  Explanation: this is the residual-norm object at step `k` under precond1.
- L492: `          ≤ precond1UndoBoundConst P.toProblem`
  Explanation: leading factor in the upper bound is precond1 undo constant.
- L493: `              * (polyAbsBoundOnIcc mu L`
  Explanation: multiply by polynomial absolute-value upper bound on interval.
- L494: `                  (pcgPrecondResidualPolyRec P.toProblem (precond1Apply P.toProblem) x0 k)`
  Explanation: this gives residual polynomial corresponding to step `k`.
- L495: `                * err0z)) ∧`
  Explanation: finally multiply by `err0z` and connect with second-part conclusion by `∧`.
- L496: `    (∀ x0 : Matrix (Fin n) (Fin r) Real, ∀ err0z : Real,`
  Explanation: second part of conclusion begins: structure is parallel to first part, but object is switched to precond2.
- L497: `      ‖WithLp.toLp 2 (precond2Apply P.toProblem (pcgR0 P.toProblem x0)).vec‖ ≤ err0z →`
  Explanation: assume initial residual norm under precond2 is at most `err0z`.
- L498: `      ∀ k : Nat,`
  Explanation: lift residual bound to "all steps `k`", indicating this is a full-course convergence certificate, not a single-step estimate.
- L499: `        pcgResidualNorm P.toProblem (precond2Apply P.toProblem) x0 k`
  Explanation: this is residual-norm object at step `k` under precond2.
- L500: `          ≤ precond2UndoBoundConst P.toProblem`
  Explanation: leading factor in upper bound switches to precond2 undo constant.
- L501: `              * (polyAbsBoundOnIcc mu L`
  Explanation: likewise multiply by polynomial absolute-value upper bound on interval.
- L502: `                  (pcgPrecondResidualPolyRec P.toProblem (precond2Apply P.toProblem) x0 k)`
  Explanation: this is residual polynomial in precond2 case.
- L503: `                * err0z)) := by`
  Explanation: finish proposition statement and enter proof.
- L504: `  exact q10_tex_pcg_spectral_interval_binding_certificate`
  Explanation: proof body directly calls existing spectral-interval binding certificate.
- L505: `    (P := P) (mu := mu) (L := L)`
  Explanation: pass problem object and interval endpoints into total certificate, matching Step14 big proposition parameter-by-parameter.
- L506: `    (hMuLeL := hMuLeL)`
  Explanation: pass down `mu≤L` premise, ensuring total certificate is established under the same spectral-interval semantics.
- L507: `    (hLamPos := hLamPos) (hKpos := hKpos)`
  Explanation: pass assumptions `λ>0` and `K` positive definite.
- L508: `    (hSymm1 := hSymm1) (hEigRange1 := hEigRange1)`
  Explanation: pass symmetry and spectral-interval assumptions for precond1.
- L509: `    (hSymm2 := hSymm2) (hEigRange2 := hEigRange2)`
  Explanation: pass symmetry and spectral-interval assumptions for precond2, completing Step14 proof.
- L510: ``
  Explanation: blank line: separate Step14 and Step15.
- L511: `/-- \`q10.tex\` Step 15 (default-package component #6, optional strong branch):`
  Explanation: comment line: Step15 starts, corresponding to optional strong branch.
- L512: `strict Loewner/kappa/rate comparison for preconditioner-2 under data-lower assumptions. -/`
  Explanation: comment body: under extra data-lower assumptions, provide stronger comparison conclusions.
- L513: `theorem q10_tex_step15_default_strong_precond2_branch`
  Explanation: Premise: on top of Step14, add `beta` interval constraints and data-lower quadratic-form assumption `hDataLower`; Conclusion: obtain Loewner comparison, condition-number comparison, convergence-rate comparison, and construct step witnesses satisfying the same tolerance with `k2 ≤ k1`; Role: this is optional strong component #6 in default delivery package, showing preconditioner-2 can yield strict improvements under stronger assumptions.
- L514: `    (P : TexObservedProblem n M r q)`
  Explanation: fix problem instance `P`; all later `K,Ω,Z,lam` are read from `P`, letting readers confirm closure in one problem object.
- L515: `    (beta err0 eps : Real)`
  Explanation: write `beta,err0,eps`: `beta` controls scale of strong-branch comparisons, and `err0/eps` control iterative error and target precision.
- L516: `    (hLamNonneg : 0 ≤ P.lam)`
  Explanation: add `lam≥0`, ensuring regularization does not break PSD structure and stays compatible with mainline assumptions.
- L517: `    (hKpsd : P.K.PosSemidef)`
  Explanation: add PSD premise on `K`, the base structure of kernel-matrix model and support for shift-to-SPD branch.
- L518: `    (hLamPos : 0 < P.lam)`
  Explanation: explicitly include `lam>0`, ensuring later inverse/condition-number comparison steps do not degenerate at zero regularization.
- L519: `    (hKpos : P.K.PosDef)`
  Explanation: explicitly include `K` positive definite, ensuring key operators of preconditioned system are invertible and stable.
- L520: `    (hBetaPos : 0 < beta)`
  Explanation: require `beta>0`, making scaling factors in Loewner and condition-number comparisons legal.
- L521: `    (hBetaLeOne : beta ≤ 1)`
  Explanation: require `beta≤1`, restricting strong-branch coefficient to standard comparison interval.
- L522: `    (hBetaLtTrace : beta < P.K.trace + 1)`
  Explanation: introduce assumption relating `beta` to kernel-trace upper bound.
- L523: `    (hBetaGtAutoInverse :`
  Explanation: begin introducing lower-bound condition on `beta`.
- L524: `      (1 / (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)) < beta)`
  Explanation: write `beta` lower bound as explicit fractional threshold, ensuring "stronger than auto-inverse bound" can be used directly in algebraic comparisons.
- L525: `    (hDataLower :`
  Explanation: begin introducing key data-lower assumption; it links empirical data term with extra precond2 term, and is the core premise for strong branch.
- L526: `      ∀ x : Fin r × Fin n → Real,`
  Explanation: this lower bound holds for arbitrary test vector `x`.
- L527: `        beta * (star x ⬝ᵥ (precond2Extra P.toProblem *ᵥ x))`
  Explanation: left side of lower bound is scaled quadratic form of precond2 extra term.
- L528: `          ≤ star x ⬝ᵥ (denseDataTerm P.toProblem *ᵥ x))`
  Explanation: right side of lower bound is quadratic form of dense data term.
- L529: `    (hErr0 : 0 < err0)`
  Explanation: introduce positivity assumption for initial error constant.
- L530: `    (hEps : 0 < eps) :`
  Explanation: introduce positivity of target tolerance and finish assumption block.
- L531: `    (QuadraticLe (beta • precond2Matrix P.toProblem) (denseMatrix P.toProblem) ∧`
  Explanation: first part of conclusion starts: give one Loewner-type quadratic comparison.
- L532: `      QuadraticLe (denseMatrix P.toProblem)`
  Explanation: continue with the second quadratic-comparison direction.
- L533: `        (((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam))`
  Explanation: write explicit scaling factor used in the comparison.
- L534: `          • precond1Matrix P.toProblem) ∧`
  Explanation: finish second comparison and connect to the next condition-number comparison.
- L535: `      spectralKappa beta (P.K.trace + 1)`
  Explanation: write left side `spectralKappa` in condition-number comparison, representing convergence-difficulty scale in strong branch.
- L536: `        < spectralKappa (1 : Real)`
  Explanation: this uses strict `<`, with goal to show strong branch is strictly better on this metric rather than tied.
- L537: `            ((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)) ∧`
  Explanation: finish right side of condition-number comparison and connect to rate comparison.
- L538: `      pcgRate (spectralKappa beta (P.K.trace + 1))`
  Explanation: write left side of convergence-rate comparison, preparing strict-improvement contrast against baseline route.
- L539: `        < pcgRate (spectralKappa (1 : Real)`
  Explanation: this also uses strict `<`, proving strong branch is strictly better on this metric instead of tied.
- L540: `            ((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)))) ∧`
  Explanation: complete convergence-rate comparison and connect to existence conclusion on iteration counts.
- L541: `    (∃ k1 k2 : Nat,`
  Explanation: start conclusion about existence of two step-count witnesses.
- L542: `      2 * (pcgRate (spectralKappa (1 : Real)`
  Explanation: write first half of left side in first tolerance inequality.
- L543: `            ((P.K.trace + 1) * (1 + ((gramMatrix P.toProblem).trace + 1) / P.lam)))) ^ k1`
  Explanation: continue with exponent term in the first inequality.
- L544: `            * err0 ≤ eps ∧`
  Explanation: first tolerance constraint completed: baseline route has some step count `k1` reaching target accuracy `eps`.
- L545: `      2 * (pcgRate (spectralKappa beta (P.K.trace + 1))) ^ k2 * err0 ≤ eps ∧`
  Explanation: second tolerance constraint corresponds to strong-branch step count `k2`; together with previous line this allows comparing required iterations of two routes.
- L546: `      k2 ≤ k1) := by`
  Explanation: require strong-branch step count is no larger than reference branch and enter proof.
- L547: `  exact q10_tex_precond2_choice_strong_branch_observed`
  Explanation: proof body directly calls main strong-branch certificate.
- L548: `    (P := P)`
  Explanation: pass current problem instance `P` into strong-branch total certificate, fixing all matrix/index data sources.
- L549: `    (beta := beta) (err0 := err0) (eps := eps)`
  Explanation: pass comparison coefficient and error parameters.
- L550: `    (hLamNonneg := hLamNonneg) (hKpsd := hKpsd)`
  Explanation: pass assumptions `λ` nonnegative and PSD.
- L551: `    (hLamPos := hLamPos) (hKpos := hKpos)`
  Explanation: pass assumptions `λ>0` and `K` positive definite.
- L552: `    (hBetaPos := hBetaPos) (hBetaLeOne := hBetaLeOne)`
  Explanation: pass positivity and upper-bound conditions of `beta` together, ensuring strong-branch comparison is established in same parameter interval.
- L553: `    (hBetaLtTrace := hBetaLtTrace) (hBetaGtAutoInverse := hBetaGtAutoInverse)`
  Explanation: pass `beta` assumptions related to trace threshold.
- L554: `    (hDataLower := hDataLower) (hErr0 := hErr0) (hEps := hEps)`
  Explanation: pass data-lower and error-positivity assumptions, completing Step15 proof.
- L555: ``
  Explanation: blank line: separate Step15 and Step16.
- L556: `/-- \`q10.tex\` Step 16 (default-package component #7):`
  Explanation: comment header marks Step16 start: this segment specifically unifies cost scales by strictly bridging fine-grained sparse cost with dominant `matVecCost`.
- L557: `cost-model bridge between explicit sparse matvec and dominant matvec cost,`
  Explanation: comment body: this step builds bridge between sparse cost and main-scale cost.
- L558: `written in an explicit parameterized form. -/`
  Explanation: comment body supplement: bridge is given as an explicit parameterized theorem.
- L559: `theorem q10_tex_step16_default_cost_bridge`
  Explanation: Premise: only dimension parameters `n,r,q` are needed, with no extra spectral/structural assumptions; Conclusion: strict equality `applyMatrixFreeSparseCost = 2 * matVecCost`; Role: component #7 in default delivery package, unifying "fine-grained implementation cost" and "dominant complexity scale" viewpoints.
- L560: `    (n r q : Nat) :`
  Explanation: introduce size parameters `n,r,q`; this theorem depends on no additional structural assumptions and only compares two cost-model expressions.
- L561: `    applyMatrixFreeSparseCost n r q = 2 * matVecCost n r q := by`
  Explanation: state Step16 cost-equality proposition.
- L562: `  exact applyMatrixFreeSparseCost_eq_two_mul_matVecCost n r q`
  Explanation: proof body directly calls already-proved cost-bridge theorem.
- L563: ``
  Explanation: blank line: separate Step16 and Step17.
- L564: `/-- \`q10.tex\` Step 17 (full default package, all components together):`
  Explanation: comment line: Step17 starts, entering export of full default package.
- L565: `this exports the exact default final package object (same as \`q10_tex_final_answer\`). -/`
  Explanation: comment body: object exported by Step17 is identical to default final-answer object.
- L566: `def q10_tex_step17_full_default_package :=`
  Explanation: this line defines core packaging name of Step17: it points directly to fully-closed minimal-spectral final certificate object; in tex chain, it unifies Step10-16 components into one default delivery entry, so readers can follow one name to get full conclusion.
- L567: `  @q10_tex_complete_solution_certificate_fully_closed_minimal_spectral`
  Explanation: right side uses `@` to explicitly point to fully-closed minimal-spectral final certificate body, showing Step17 is not a new proof but export of total certificate.
- L568: ``
  Explanation: blank line: separate Step17 core and display alias.
- L569: `/-- Step 17 display form (same final package as Step 17 core,`
  Explanation: comment line: below is Step17 display alias.
- L570: `written as an explicit alias for human-first reading order). -/`
  Explanation: comment body: this alias is for reader-friendly ordering.
- L571: `def q10_tex_step17_full_default_package_display := q10_tex_step17_full_default_package`
  Explanation: this display name is fully value-identical to Step17 core, changing only entry name for tex-order browsing.
- L572: ``
  Explanation: blank line: separate display and readable-alias block.
- L573: `/-- Human-readable full answer alias:`
  Explanation: comment line: declare readable alias for full answer below.
- L574: `keeps tex-order readability while including every component of the default final package. -/`
  Explanation: comment body: this alias preserves tex reading order while keeping every component.
- L575: `abbrev q10_tex_human_aligned_full_answer := @q10_tex_step17_full_default_package`
  Explanation: assign a more paper-friendly name to final package; `abbrev` changes only notation, not object, so proof content remains unchanged.
- L576: ``
  Explanation: blank line: separate full-answer alias and default-entry alias.
- L577: `/-- Human-readable default export (full):`
  Explanation: comment line: declare default export entry below.
- L578: `use this object as the entrypoint when reading \`q10.tex\` and Lean side-by-side. -/`
  Explanation: comment body: recommended to enter from this object when reading tex and Lean side by side.
- L579: `abbrev q10_tex_human_aligned_default := @q10_tex_human_aligned_full_answer`
  Explanation: provide default entry name for unified external referencing; mathematically it is the same value as full answer and Step17 core object.
- L580: ``
  Explanation: blank line: separate main text and namespace closing.
- L581: `end`
  Explanation: close current `noncomputable section`, meaning the main proof body in this file is now fully delivered.
- L582: `end Q10`
  Explanation: close namespace `Q10`; no further local symbols for this question are added, only the outer `AutoProof` remains to close.
- L583: `end AutoProof`
  Explanation: end namespace `AutoProof`; file main body ends here.
## C. Quick Concept Reference (Definition + Location + Role in q10.tex)

This section is written as a "zero-barrier dictionary": each concept answers four questions.
1) What exactly is it (plain language)
2) What it represents mathematically
3) Which object it appears as in Lean
4) Which part of the full `q10.tex` chain it is responsible for

### C1. Problem Objects and Structural Packaging

- `Problem`
  Definition: this is the most basic "problem data package." You can treat it as a record containing raw inputs such as kernel matrix `K`, feature matrix `Z`, observation index `Ω`, and regularization parameter `lam`.
  Location: `autoproof/Q10/Core/Operators/ProblemModel.lean:16`.
  Role: all later operator/residual/cost formulas need this raw package before they can be written.

- `TexProblem`
  Definition: this is the version with "statement-semantic constraints" added on top of `Problem`. In plain words: it has both data and structural premises required by the tex solution.
  Location: `autoproof/Q10/Core/Operators/ProblemModel.lean:26`.
  Role: make statement conditions part of the type, avoiding repetition of the same assumption set in every theorem.

- `TexObservedProblem`
  Definition: this is a further packaging: besides structural premises of `TexProblem`, it directly binds the fact that "observed RHS is already determined by observation data" into the object.
  Location: `autoproof/Q10/Core/Operators/ProblemModel.lean:31`.
  Role: RHS locking in Step 2 can be called directly from object fields, without reproving each time.

- `toProblem`
  Definition: this is a "downgrade projection." When you hold `TexProblem`/`TexObservedProblem` but a theorem only accepts base `Problem`, use it to extract underlying data.
  Location: object-field section in the same `ProblemModel` file.
  Role: connect high-level statement objects and low-level generic theorems.

- `withKernelShift`
  Definition: add diagonal shift to kernel matrix: replace `K` by `K + nu I`, while keeping other fields (`Z, Ω, vals, B, lam`) unchanged.
  Location: `autoproof/Q10/Core/Operators/ProblemModel.lean:36`.
  Role: convert "only PSD" cases into usable "strictly SPD" cases, which is the key action in Step 9 toward PCG certificates.

- `TexObservedProblem.withKernelShift_posDef_of_posSemidef`
  Definition: this is a conclusion: if original `K` is PSD and `nu>0`, then shifted `(K + nu I)` is PD.
  Location: in `autoproof/Q10/Core/Operators/ProblemModel.lean` (`withKernelShift` theorem block).
  Role: Step 9 is not a verbal feasibility claim; this theorem formally seals PSD->SPD.

### C2. RHS Construction, Matrix-Free Operator, and Implementation Objects

- `sparseMTTKRP`
  Definition: build sparse version of `TZ` from observation indices and observation values; compute only at observed locations.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:83`.
  Role: convert tex `B=TZ` into directly computable object rather than leaving it at symbolic level.

- `rhsVec`
  Definition: interface that writes matrix RHS into vectorized linear-system RHS. In plain words: it aligns RHS between matrix form and vector form.
  Location: RHS-definition section in `autoproof/Q10/Core/Operators/ObservedOps.lean`.
  Role: when dense vector equation and matrix equation must communicate in Step 1, this interface aligns RHS expressions.

- `rhsFromObserved`
  Definition: function constructing RHS directly from observed data, without first assuming a free `B`.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:91`.
  Role: core object of Step 2, expressing that RHS is observation-determined rather than arbitrarily chosen.

- `rhsFromObservedRows`
  Definition: same mathematical quantity as `rhsFromObserved`, but input is an online row generator rather than explicit `Z`.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:546`.
  Role: allows online-implementation route to generate the same RHS and be compared with explicit route.

- `ObsFactorProvider`
  Definition: an interface type. Given an observation index, it provides required factor information for that observation (for online row generation).
  Location: near `obsRowFromFactors` in `autoproof/Q10/Core/Operators/ObservedOps.lean`.
  Role: modularize online data reading so we can prove "implementation is replaceable while results stay unchanged."

- `obsRowFromFactors`
  Definition: turn `ObsFactorProvider` into a function that directly returns observed rows.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:343`.
  Role: in Step 5, both online matvec and online RHS use it as input.

- `factorsGenerateObservedRows`
  Definition: this is a consistency assumption: online-generated observed rows equal corresponding explicit-`Z` rows at all observation locations.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:353`.
  Role: without this assumption, one cannot prove "online implementation = explicit formulas".

- `applyDenseVec`
  Definition: left operator in dense Kronecker/selection version (vectorized form).
  Location: related definitions under `autoproof/Q10/KernelOps` (imported via `TexAnswer`).
  Role: corresponds to the "explicit system equation" side in tex.

- `applyMatrixFree`
  Definition: abstract matrix-free operator definition, not bound to concrete implementation details (such as sparse or bucket).
  Location: abstract-definition section in `autoproof/Q10/Core/Operators/ObservedOps.lean`.
  Role: provides one unified "gold standard" so all implementations can prove equality with it.

- `applyMatrixFreeSparse`
  Definition: matrix-free implementation executed over sparse observed data.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:579`.
  Role: main operator in Step 1/3/4; this is the tex-mainline implementation version.

- `applyMatrixFreeBucketed`
  Definition: matrix-free implementation after grouping observations by CSR/bucket.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:591`.
  Role: engineering-optimized version; Step 4 proves its mathematical equivalence to sparse version.

- `applyMatrixFreeObserved`
  Definition: matvec version that takes an online observed-row function directly as input.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:487`.
  Role: core operator object of the online route in Step 5.

- `applyMatrixFreeBucketedPlan`
  Definition: returns not only bucketed computation result, but also a trace (execution record) for cost counting.
  Location: bucketed-plan section in `autoproof/Q10/Core/Operators/ObservedOps.lean`.
  Role: allows proving "value correctness" and "cost correctness" simultaneously on the same implementation.

- `gather`
  Definition: extract entries from a large object by observation indices, forming an observation vector.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean`.
  Role: baseline mathematical operation of Step-B in Step 3.

- `gatherKernelPredictSparse`
  Definition: gather version for sparse implementation.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:233`.
  Role: first prove it equals standard `gather`, then show implementation did not change mathematical meaning.

- `scatter`
  Definition: reverse of `gather`: backfill an observation vector into target shape by indices.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean`.
  Role: standard algebraic operation of Step-C in Step 3.

- `scatterMulSparse`
  Definition: combined operation "backfill then multiply `Z`" in sparse implementation.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:251`.
  Role: Step 3 rewrites it into standard `scatter(...) * Z` form.

- `canonicalObsBuckets`
  Definition: rule-based bucketing of observation indices (canonical bucket scheme).
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:271`.
  Role: Step 4 uses it to fix bucket strategy, making value/cost equivalence reproducible and comparable.

### C3. Equivalence Bridge Theorems (Align Implementation Forms to Mathematical Forms)

- `q10_mainline_system_equiv_matrixFree`
  Definition: proves dense vector system and matrix-free sparse system are the same equation.
  Location: `autoproof/Q10/KernelOps/SystemEquiv.lean:17`.
  Role: total bridge of Step 1, also reused by overview theorem.

- `gatherKernelPredictSparse_eq_gather`
  Definition: proves sparse gather implementation equals standard `gather`.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:240`.
  Role: first bridge in Step 3, ensuring Step-B does not deviate from mathematical definition.

- `scatterMulSparse_eq_scatter_mul`
  Definition: proves `scatterMulSparse` equals `scatter(...) * Z`.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:257`.
  Role: second bridge in Step 3, ensuring Step-C matches standard algebra.

- `applyMatrixFreeSparse_eq_applyMatrixFree`
  Definition: proves sparse implementation is fully equal to abstract `applyMatrixFree`.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:621`.
  Role: third bridge in Step 3, closing "implementation = definition".

- `applyMatrixFreeCanonicalBucketed_eq_sparse`
  Definition: proves canonical-bucketed output value matches sparse output pointwise.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:612`.
  Role: "numerical correctness" bridge in Step 4.

- `applyMatrixFreeCanonicalBucketedPlan_cost_eq`
  Definition: proves canonical-bucketed trace cost equals sparse theoretical cost.
  Location: same area in `autoproof/Q10/Core/Operators/ObservedOps.lean` (adjacent to above theorem).
  Role: "cost correctness" bridge in Step 4.

- `rhsFromObservedRows_from_factors_eq_rhsFromObserved`
  Definition: proves RHS from online row generation equals RHS from explicit `Z`.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:565`.
  Role: RHS-equivalence bridge in Step 5.

- `applyMatrixFreeObserved_from_factors_eq_sparse`
  Definition: proves online-row-generation matvec equals explicit sparse matvec.
  Location: `autoproof/Q10/Core/Operators/ObservedOps.lean:647`.
  Role: operator-equivalence bridge in Step 5.

### C4. Preconditioners and Closed-Form Expression

- `precond1Apply`
  Definition: action function of preconditioner 1; input residual matrix, output preconditioned matrix.
  Location: `autoproof/Q10/Core/Preconditioners/BaseDefs.lean:16`.
  Role: first PCG route in Step 6/7.

- `precond2Apply`
  Definition: action function of preconditioner 2.
  Location: `autoproof/Q10/Core/Preconditioners/BaseDefs.lean:112`.
  Role: second PCG route in Step 6/7.

- `precond2Matrix`
  Definition: object writing precond2 in matrix-operator form.
  Location: `autoproof/Q10/Core/Preconditioners/BaseDefs.lean:86`.
  Role: used in Step 6 left-inverse equality "recover original vector after action".

- `gramMatrix`
  Definition: Gram matrix `ZᵀZ`.
  Location: `autoproof/Q10/Core/Preconditioners/BaseDefs.lean:53`.
  Role: core of right inverse matrix in precond2 closed form `K⁻¹ * R * (ZᵀZ + λI)⁻¹`.

- `precond1ApplyLin`
  Definition: version viewing `precond1Apply` as a linear map.
  Location: `autoproof/Q10/TraceAndRates/RateTheory/PreconditionedKrylovInterval.lean`.
  Role: prepares linear-operator interface for spectral analysis.

- `precond2ApplyLin`
  Definition: version viewing `precond2Apply` as a linear map.
  Location: same as above.
  Role: allows precond2 route to enter the same spectral-analysis framework.

- `precondDenseVecLin`
  Definition: writes preconditioned system operator as a linear map on dense vector space.
  Location: `autoproof/Q10/TraceAndRates/RateTheory/PreconditionedKrylovInterval.lean:17`.
  Role: all "symmetry + spectral interval" assumptions in Step 7 are built on this object.

- `q10_mainline_preconditioner_action_bridge`
  Definition: unified bridge theorem giving "action correctness (left-inverse relation)" for both precond1 and precond2.
  Location: `autoproof/Q10/Preconditioners/ClosedForm.lean:17`.
  Role: first two conclusions in Step 6 call it directly.

- `q10_mainline_precond2_closed_form_bridge`
  Definition: bridge theorem giving closed form of precond2.
  Location: `autoproof/Q10/Preconditioners/ClosedForm.lean:32`.
  Role: third "explicit formula" conclusion in Step 6 is delivered by it.

### C5. PCG Residual, Spectral Interval, and Error Certificates

- `pcgR0`
  Definition: step-0 residual object of PCG at initial point `x0`.
  Location: `autoproof/Q10/Core/KrylovAlgorithm/DefsAndPoly.lean:34`.
  Role: starting point of initial-error upper bound `err0z` in Step 7.

- `pcgPrecondResidualPolyRec`
  Definition: object describing that "preconditioned residual at step k is obtained by applying a recurrence polynomial".
  Location: `autoproof/Q10/Core/KrylovAlgorithm/PreconditionedPoly.lean:220`.
  Role: turns convergence proof into a problem of "max polynomial value on spectral interval".

- `pcgResidualNorm`
  Definition: residual-norm function at step `k` of PCG.
  Location: `autoproof/Q10/TraceAndRates/RateTheory/Contraction.lean:101`.
  Role: this is exactly what Step 7 ultimately upper-bounds.

- `polyAbsBoundOnIcc`
  Definition: given interval `[mu,L]` and a polynomial, returns absolute-value upper bound of that polynomial on the interval.
  Location: `autoproof/Q10/TraceAndRates/RateTheory/PreconditionedKrylovInterval.lean:274`.
  Role: turns spectral information into an explicit coefficient multiplied in residual formulas.

- `precond1UndoBoundConst`
  Definition: constant needed on precond1 route to convert "preconditioned norm bound" back to "target residual bound".
  Location: `autoproof/Q10/Core/Preconditioners/BaseDefs.lean:305`.
  Role: first multiplicative factor on the right side of precond1 branch in Step 7.

- `precond2UndoBoundConst`
  Definition: corresponding undo constant on precond2 route.
  Location: `autoproof/Q10/Core/Preconditioners/BaseDefs.lean:309`.
  Role: first multiplicative factor on the right side of precond2 branch in Step 7.

- `q10_tex_pcg_spectral_interval_binding_certificate`
  Definition: turn assumptions "symmetry + spectrum in `[mu,L]`" into residual upper bounds for both preconditioned routes in one shot.
  Location: `autoproof/Q10/Mainline/TexAnswer.lean:997`.
  Role: Step 7 directly calls it by `exact`, finishing the entire proof segment.

- `LinearMap.toMatrixAlgEquiv'`
  Definition: convert a linear map into an equivalent matrix representation (another representation of the same linear object).
  Location: Mathlib.
  Role: in Step 7, "symmetry/spectrum" are stated at matrix level, so this conversion is needed first.

- `spectrum`
  Definition: spectrum of an operator (in finite-dimensional real case, it can be understood as the full set of eigenvalues).
  Location: Mathlib.
  Role: Step 7 uses it to express whether all eigenvalues lie in a given interval.

- `Set.Icc`
  Definition: closed interval set `[mu,L]`.
  Location: Mathlib.
  Role: target interval in Step 7 spectral-inclusion relation `spectrum ⊆ Set.Icc mu L`.

- `WithLp.toLp`
  Definition: standard interface embedding vectors into `Lp` norm space.
  Location: Mathlib.
  Role: used when Step 7 writes initial residual upper bound as `Lp` 2-norm.

### C6. Cost Models and Equality Bridges

- `kernelMulCost`
  Definition: cost primitive for one kernel-matrix-related multiplication.
  Location: `autoproof/Q10/Core/CostAndPSD.lean`.
  Role: base building block when expanding RHS and sparse costs.

- `gatherKernelPredictSparseCost`
  Definition: cost primitive for sparse gather-predict step.
  Location: same file.
  Role: "observation extraction" part in Step 8 fine-grained cost decomposition.

- `scatterMulSparseCost`
  Definition: cost primitive for sparse scatter followed by multiplying `Z`.
  Location: same file.
  Role: indispensable term in full sparse-cost expansion of Step 8.

- `matVecCost`
  Definition: dominant per-step cost scale, with explicit formula `n^2 r + q r`.
  Location: `autoproof/Q10/Core/CostAndPSD.lean:18`.
  Role: project complex implementation costs onto one main scale that readers care most about.

- `rhsFromObservedCost`
  Definition: cost model for constructing RHS.
  Location: `autoproof/Q10/Core/CostAndPSD.lean:174`.
  Role: Step 8 proves RHS preparation introduces no higher-order complexity.

- `applyMatrixFreeSparseCost`
  Definition: fine-grained cost model of sparse matvec (all step costs expanded).
  Location: `autoproof/Q10/Core/CostAndPSD.lean:149`.
  Role: connects implementation details and theoretical complexity conclusions.

- `applyMatrixFreeSparseCost_eq_two_mul_matVecCost`
  Definition: proves fine-grained sparse cost is exactly `2 * matVecCost`.
  Location: `autoproof/Q10/Core/CostAndPSD.lean:153`.
  Role: key "scale-unification bridge" in Step 8 and Step 16.

- `obsRowFromFactorsGenerationCost`
  Definition: extra cost for generating observed rows online from factors.
  Location: `autoproof/Q10/Core/CostAndPSD.lean:167`.
  Role: explains why online version has one extra cost term versus offline sparse version.

- `applyMatrixFreeObservedOnlineCost`
  Definition: online per-step total cost, equal to "sparse matvec cost + online row-generation cost".
  Location: `autoproof/Q10/Core/CostAndPSD.lean:170`.
  Role: core left-side object in Step 8 online complexity formulas.

- `sparseMatVecTraceCost`
  Definition: counting function that reads execution trace and computes sparse-route cost.
  Location: defined across `autoproof/Q10/Core/Operators/ObservedOps.lean` and cost module.
  Role: Step 4 uses it to align bucketed actual execution trace with theoretical cost model.

- `pcgSolveCostPrecond1Online`
  Definition: total-cost model of precond1 online PCG (includes fixed and iterative terms).
  Location: `autoproof/Q10/TraceAndRates/TraceModels.lean:165`.
  Role: Step 8 gives closed form for precond1 online total cost.

- `pcgSolveCostPrecond2Online`
  Definition: total-cost model of precond2 online PCG.
  Location: `autoproof/Q10/TraceAndRates/TraceModels.lean:171`.
  Role: Step 8 compares its cost with precond1 route.

- `pcgSolveCostPrecond1Online_eq`
  Definition: equality theorem expanding `pcgSolveCostPrecond1Online` into explicit polynomial.
  Location: `autoproof/Q10/TraceAndRates/TraceModels.lean`.
  Role: Step 8 uses `simpa using` to close the corresponding subgoal directly.

- `pcgSolveCostPrecond2Online_eq`
  Definition: equality theorem expanding `pcgSolveCostPrecond2Online` into explicit polynomial.
  Location: same file.
  Role: direct proof source for precond2 cost subgoal in Step 8.

- `denseDirectSolveCost`
  Definition: baseline cost model of dense direct method, formula `n^3 r^3`.
  Location: `autoproof/Q10/TraceAndRates/TraceModels.lean:191`.
  Role: baseline comparison for "if PCG is not used".

- `denseDirectSolveCost_eq`
  Definition: theorem expanding `denseDirectSolveCost` into explicit formula.
  Location: same file.
  Role: closes the final equality in Step 8.

### C7. Total-Certificate Components from `TexAnswer.lean` (Reused by Step 10-17)

- `q10_tex_complete_solution_certificate_minimal_input_spectralIndexed_ambientN`
  Definition: under minimal-input assumptions, gives full main certificate parameterized by spectral index and ambient-`N`.
  Location: `autoproof/Q10/Mainline/TexAnswer.lean:1352`.
  Role: core object of Step 10; many later default-package aliases are organized around it.

- `q10_tex_complete_solution_certificate_closed_loop_online_minimal_input_spectralIndexed_ambientN`
  Definition: full certificate that closes loop for online row generation, online matvec, and online cost together.
  Location: corresponding Step 11 section in `autoproof/Q10/Mainline/TexAnswer.lean`.
  Role: Step 11 component, responsible for "online path is also fully certifiable".

- `q10_tex_psd_to_shifted_pcg_certificate_minimal_input_spectralIndexed_ambientN`
  Definition: complete object connecting from PSD premise to PCG certificate through kernel shift.
  Location: corresponding Step 12 section in `autoproof/Q10/Mainline/TexAnswer.lean`.
  Role: Step 12 component, responsible for "weak-premise PSD can also close the loop".

- `q10_tex_complete_solution_certificate_polyEnvelope_closure_spectralIndexed`
  Definition: poly-envelope tolerance-closure certificate.
  Location: corresponding Step 13 section in `autoproof/Q10/Mainline/TexAnswer.lean`.
  Role: Step 13 component, responsible for non-stepwise error control.

- `q10_tex_precond2_choice_strong_branch_observed`
  Definition: optional strong-branch certificate for precond2, including stronger premises on Loewner/condition-number/rate comparisons.
  Location: corresponding Step 15 section in `autoproof/Q10/Mainline/TexAnswer.lean`.
  Role: Step 15 component, used for stronger comparison conclusions under extra assumptions.

- `q10_tex_complete_solution_certificate_fully_closed_minimal_spectral`
  Definition: default final fully-closed certificate object (uniform package of mainline components).
  Location: `autoproof/Q10/Mainline/TexAnswer.lean:1448`.
  Role: Step 17 final package and default export both point to it.

### C8. Names Exported by `TexAligned.lean` Itself (Entrypoints Readers See Directly in This File)

- `q10_tex_step1_system_equivalence`
  Definition: a `theorem` whose proposition is: dense form `applyDenseVec ... = rhsVec ...` is fully equivalent to matrix-free sparse form `applyMatrixFreeSparse ... = K * B`. It does not define a new operator; it bridges these two equations into one reusable conclusion.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:17`.
  Role: corresponds to Step 1 of `q10.tex`, formally grounding "system equation can be rewritten as matrix-free form" as a Lean entrypoint.

- `q10_tex_step2_rhs_from_observations`
  Definition: a `theorem` with proposition `rhsVec P.K P.B = rhsFromObserved P.K P.Ω P.vals P.Z`. Meaning: RHS vector is not freely chosen; it is uniquely determined by observation index `Ω`, observed values `vals`, and factor `Z`.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:31`.
  Role: corresponds to Step 2 of `q10.tex`, turning "RHS locking" from verbal explanation into machine-checkable equality.

- `q10_tex_step3_matrix_vector_pipeline`
  Definition: a `theorem` simultaneously giving three equalities: `gatherKernelPredictSparse` equals explicit `gather`, `scatterMulSparse` equals explicit `scatter ... * Z`, and `applyMatrixFreeSparse` equals `applyMatrixFree`.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:39`.
  Role: corresponds to Step 3, proving "implementation pipeline is only a rewrite, not a change of mathematical operator".

- `q10_tex_step4_bucketed_matvec_and_cost`
  Definition: a `theorem` whose first part states bucketed/CSR matvec output equals sparse output, and second part states bucketed trace-count cost equals `applyMatrixFreeSparseCost`.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:64`.
  Role: corresponds to Step 4, aligning engineering implementation (bucket) and theoretical object (sparse model) in both value and complexity.

- `q10_tex_step5_online_rows_equivalence`
  Definition: a `theorem` proving under `factorsGenerateObservedRows` that `rhsFromObservedRows` from online observed-row generation equals explicit-`Z` `rhsFromObserved`, and online `applyMatrixFreeObserved` equals `applyMatrixFreeSparse` for arbitrary `W`.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:87`.
  Role: corresponds to Step 5, confirming online row generation changes only implementation strategy, not the equation itself.

- `q10_tex_step6_preconditioners`
  Definition: a `theorem` proving under `λ>0` and positive-definite `K` that both preconditioner-1 and preconditioner-2 satisfy left-inverse correctness, and giving explicit matrix expression (closed form) of preconditioner-2.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:109`.
  Role: corresponds to Step 6, lifting "preconditioner is usable" from intuition to strict equality proof.

- `q10_tex_step7_pcg_residual_from_spectrum`
  Definition: a `theorem` that under assumptions such as `spectrum ⊆ [mu,L]`, writes PCG error/residual bounds as product of `polyAbsBoundOnIcc` and initial-error upper bound, covering preconditioner-1 and preconditioner-2 separately.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:135`.
  Role: corresponds to Step 7, converting spectral information into readable convergence inequalities.
- `q10_tex_step8_complexity_formulas`
  Definition: a `theorem` that centrally gives explicit equalities for `matVecCost`, `rhsFromObservedCost`, `applyMatrixFreeSparseCost`, online extra cost, total online PCG cost, and dense-direct baseline cost.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:187`.
  Role: corresponds to Step 8, turning every formula in complexity section into machine-checkable equality entries.

- `q10_tex_step9_psd_to_shift_core`
  Definition: a `theorem` that under semidefinite `K` and shift amount `nu>0`, defines `Kshift := withKernelShift P.K nu`, proves `Kshift` is positive definite and `λI + (G+nu I)` is positive definite, and migrates key conclusions of Step 6/7/8 to shifted objects.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:220`.
  Role: corresponds to Step 9, completing the core bridge "under PSD premises we can still enter PCG closed loop".

- `q10_tex_human_aligned_overview`
  Definition: a `theorem` that packages major conclusions of Step 1-9 in tex narrative order as an overview interface, enabling one-shot inspection of main assertions of the whole proof chain.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:233`.
  Role: mainline-layer entrypoint; readers can inspect this first and then return to line-by-line details.

- `q10_tex_step10_default_core`
  Definition: a `def` that renames `q10_tex_complete_solution_certificate_minimal_input_spectralIndexed_ambientN` after explicitly unfolding parameters in this file. Mathematical content is unchanged, but input assumptions and parameter order become immediately visible.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:290`.
  Role: corresponds to Step 10 as default-package component #1 (minimal input, spectral index, ambient-N main certificate).

- `q10_tex_step10_default_core_display`
  Definition: a `def` whose value is exactly `q10_tex_step10_default_core`, but keeps "all parameters explicitly written" style for manual checking of assumption correspondence.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:313`.
  Role: reader-friendly Step 10 entry, convenient for aligning with tex variable list.

- `q10_tex_step11_default_online_closure`
  Definition: a `def` exporting explicit-parameter form of `q10_tex_complete_solution_certificate_closed_loop_online_minimal_input_spectralIndexed_ambientN`. It states online row generation, online matvec, and online cost close the loop together.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:336`.
  Role: corresponds to Step 11 as default-package component #2 (online closure certificate).

- `q10_tex_step11_default_online_closure_display`
  Definition: a `def` fully equal in value to `q10_tex_step11_default_online_closure`, only keeping explicit parameter display style.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:359`.
  Role: manual-reading interface of Step 11, for checking online assumptions are complete.

- `q10_tex_step12_default_shifted_pcg`
  Definition: a `def` making `q10_tex_psd_to_shifted_pcg_certificate_minimal_input_spectralIndexed_ambientN` explicit and adding shift parameter `nu>0`. This object packages the full bridge "PSD + shift -> usable PCG".
  Location: `autoproof/Q10/Mainline/TexAligned.lean:382`.
  Role: corresponds to Step 12 as default-package component #3 (shifted-PCG closure).

- `q10_tex_step12_default_shifted_pcg_display`
  Definition: a `def` equal in value to `q10_tex_step12_default_shifted_pcg`, preserving explicit parameter display (especially `nu` and `hNu`).
  Location: `autoproof/Q10/Mainline/TexAligned.lean:408`.
  Role: Step 12 reading entry, helping readers quickly locate shift-parameter usage in proof.

- `q10_tex_step13_default_poly_envelope`
  Definition: a `def` exporting `q10_tex_complete_solution_certificate_polyEnvelope_closure_spectralIndexed` as local entry. It gives non-stepwise polynomial-envelope error-closure conclusion.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:434`.
  Role: corresponds to Step 13 as default-package component #4 (poly-envelope route).

- `q10_tex_step13_default_poly_envelope_display`
  Definition: a `def` equal in value to `q10_tex_step13_default_poly_envelope`, using fully explicit parameter display form.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:448`.
  Role: reader-friendly entry of Step 13, convenient for checking `mu,L,eps` and positivity assumptions.

- `q10_tex_step14_default_spectral_binding`
  Definition: a `theorem` binding spectral-interval assumptions `spectrum ⊆ [mu,L]` to concrete linear operators of precond1/precond2, producing two PCG residual upper-bound conclusions simultaneously.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:462`.
  Role: corresponds to Step 14 as default-package component #5 (spectral-binding component).

- `q10_tex_step15_default_strong_precond2_branch`
  Definition: a `theorem` that under stronger data-lower and `beta` constraints gives strong preconditioner-2 branch: Loewner comparison, condition-number comparison, convergence-rate comparison, and iteration-count comparison (`k2 ≤ k1`).
  Location: `autoproof/Q10/Mainline/TexAligned.lean:513`.
  Role: corresponds to Step 15 as default-package component #6 (optional stronger conclusion).

- `q10_tex_step16_default_cost_bridge`
  Definition: a `theorem` with proposition `applyMatrixFreeSparseCost n r q = 2 * matVecCost n r q`. It strictly bridges "fine-grained sparse cost" and "dominant matvec cost".
  Location: `autoproof/Q10/Mainline/TexAligned.lean:559`.
  Role: corresponds to Step 16 as default-package component #7 (unified cost scale).

- `q10_tex_step17_full_default_package`
  Definition: a `def` pointing directly to `q10_tex_complete_solution_certificate_fully_closed_minimal_spectral`. It is the final default object after integrating Step 10-16 components.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:566`.
  Role: corresponds to Step 17, packaging scattered components into one final delivery certificate.

- `q10_tex_step17_full_default_package_display`
  Definition: a `def` whose value equals `q10_tex_step17_full_default_package`, used only to provide a more intuitive reading-order name.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:571`.
  Role: Step 17 display entry, helping separate "core package" and "display name" in understanding.

- `q10_tex_human_aligned_full_answer`
  Definition: an `abbrev` assigning a reader-facing final-answer name to `q10_tex_step17_full_default_package`; `abbrev` means pure alias, introducing no new mathematical object.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:575`.
  Role: for paper-order reading, readers can cite final certificate with a more intuitive entry name.

- `q10_tex_human_aligned_default`
  Definition: an `abbrev` as default entry name, pointing to `q10_tex_human_aligned_full_answer`; essentially the same final object.
  Location: `autoproof/Q10/Mainline/TexAligned.lean:579`.
  Role: when reading `q10.tex` and Lean side by side, this is the recommended default entry name.

