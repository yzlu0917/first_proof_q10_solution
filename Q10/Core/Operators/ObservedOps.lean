import Mathlib

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Selection matrix associated to observed coordinates `Ω`. Each column has a single `1`. -/
def selectionMatrix (Ω : Fin q → Fin M × Fin n) : Matrix (Fin M × Fin n) (Fin q) Real :=
  fun ij t => if Ω t = ij then 1 else 0

/-- Gather observed entries of a mode-`k` unfolding matrix. -/
def gather (Ω : Fin q → Fin M × Fin n) (X : Matrix (Fin n) (Fin M) Real) : Fin q → Real :=
  (selectionMatrix Ω)ᵀ *ᵥ X.vec

/-- Scatter a `q`-vector back to an `n × M` matrix (unobserved positions are zero). -/
def scatter (Ω : Fin q → Fin M × Fin n) (u : Fin q → Real) : Matrix (Fin n) (Fin M) Real :=
  Matrix.of fun i j => ((selectionMatrix Ω) *ᵥ u) (j, i)

@[simp]
theorem gather_apply (Ω : Fin q → Fin M × Fin n) (X : Matrix (Fin n) (Fin M) Real) (t : Fin q) :
    gather Ω X t = X (Ω t).2 (Ω t).1 := by
  classical
  simp [gather, selectionMatrix, Matrix.mulVec, dotProduct]

@[simp]
theorem scatter_apply (Ω : Fin q → Fin M × Fin n) (u : Fin q → Real) (i : Fin n) (j : Fin M) :
    scatter Ω u i j = ∑ t : Fin q, (if Ω t = (j, i) then u t else 0) := by
  classical
  simp [scatter, selectionMatrix, Matrix.mulVec, dotProduct]

@[simp]
theorem vec_scatter (Ω : Fin q → Fin M × Fin n) (u : Fin q → Real) :
    (scatter Ω u).vec = (selectionMatrix Ω) *ᵥ u := by
  ext ij
  rcases ij with ⟨j, i⟩
  simp [scatter]

theorem selectionMatrix_transpose_mul_self_eq_one_of_injective
    (Ω : Fin q → Fin M × Fin n)
    (hInj : Function.Injective Ω) :
    (selectionMatrix Ω)ᵀ * selectionMatrix Ω = (1 : Matrix (Fin q) (Fin q) Real) := by
  classical
  ext t s
  by_cases hts : t = s
  · subst hts
    simp [Matrix.mul_apply, selectionMatrix]
  · have hneq : Ω t ≠ Ω s := by
      intro hΩ
      exact hts (hInj hΩ)
    simp [Matrix.mul_apply, selectionMatrix, hts, hneq]

theorem injective_of_selectionMatrix_transpose_mul_self_eq_one
    (Ω : Fin q → Fin M × Fin n)
    (hSS : (selectionMatrix Ω)ᵀ * selectionMatrix Ω = (1 : Matrix (Fin q) (Fin q) Real)) :
    Function.Injective Ω := by
  intro t s hΩ
  by_contra hts
  have hOff : ((selectionMatrix Ω)ᵀ * selectionMatrix Ω) t s = 0 := by
    have hEntry := congrArg (fun A => A t s) hSS
    simpa [hts] using hEntry
  have hOn : ((selectionMatrix Ω)ᵀ * selectionMatrix Ω) t s = 1 := by
    simp [Matrix.mul_apply, selectionMatrix, hΩ]
  linarith

theorem selectionMatrix_transpose_mul_self_eq_one_iff_injective
    (Ω : Fin q → Fin M × Fin n) :
    (selectionMatrix Ω)ᵀ * selectionMatrix Ω = (1 : Matrix (Fin q) (Fin q) Real) ↔
      Function.Injective Ω := by
  constructor
  · exact injective_of_selectionMatrix_transpose_mul_self_eq_one (Ω := Ω)
  · exact selectionMatrix_transpose_mul_self_eq_one_of_injective (Ω := Ω)

/-- Sparse MTTKRP from observed entries `(Ω, vals)`:
`B = UZ` with `U = scatter Ω vals` (no `N`-scale object). -/
def sparseMTTKRP
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real) : Matrix (Fin n) (Fin r) Real :=
  (scatter Ω vals) * Z

/-- Matrix-free RHS builder from observed entries:
`vec(K * sparseMTTKRP Ω vals Z) = (I ⊗ K) vec(sparseMTTKRP Ω vals Z)`. -/
def rhsFromObserved
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real) : Fin r × Fin n → Real :=
  ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ K) *ᵥ (sparseMTTKRP Ω vals Z).vec

/-- Step-C sparse accumulation formula:
`(scatter Ω u) * Z` equals row-filtered observed summation. -/
theorem scatter_mul_apply_observed
    (Ω : Fin q → Fin M × Fin n)
    (u : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (i : Fin n) (l : Fin r) :
    ((scatter Ω u) * Z) i l
      = ∑ t : Fin q, (if (Ω t).2 = i then u t else 0) * Z (Ω t).1 l := by
  classical
  calc
    ((scatter Ω u) * Z) i l
        = ∑ j : Fin M, (scatter Ω u i j) * Z j l := by
            simp [Matrix.mul_apply]
    _ = ∑ j : Fin M, (∑ t : Fin q, (if Ω t = (j, i) then u t else 0)) * Z j l := by
          simp [scatter_apply]
    _ = ∑ j : Fin M, ∑ t : Fin q, (if Ω t = (j, i) then u t else 0) * Z j l := by
          simp_rw [Finset.sum_mul]
    _ = ∑ t : Fin q, ∑ j : Fin M, (if Ω t = (j, i) then u t else 0) * Z j l := by
          rw [Finset.sum_comm]
    _ = ∑ t : Fin q, (if (Ω t).2 = i then u t else 0) * Z (Ω t).1 l := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          by_cases hi : (Ω t).2 = i
          · have hmul :
                (∑ j : Fin M, (if Ω t = (j, i) then u t else 0) * Z j l)
                  = ∑ j : Fin M, (if Ω t = (j, i) then u t * Z j l else 0) := by
                refine Fintype.sum_congr _ _ ?_
                intro j
                by_cases hji : Ω t = (j, i)
                · simp [hji]
                · simp [hji]
            have hterm :
                ∀ j : Fin M,
                  (if Ω t = (j, i) then u t * Z j l else 0)
                    = (if (Ω t).1 = j then u t * Z j l else 0) := by
              intro j
              have hcond : Ω t = (j, i) ↔ (Ω t).1 = j := by
                constructor
                · intro hji
                  exact congrArg Prod.fst hji
                · intro hj
                  exact Prod.ext hj hi
              by_cases hj : (Ω t).1 = j
              · simp [hcond, hj]
              · simp [hcond, hj]
            calc
              (∑ j : Fin M, (if Ω t = (j, i) then u t else 0) * Z j l)
                  = ∑ j : Fin M, (if Ω t = (j, i) then u t * Z j l else 0) := hmul
              _ = ∑ j : Fin M, (if (Ω t).1 = j then u t * Z j l else 0) := by
                    exact Fintype.sum_congr _ _ hterm
              _ = u t * Z (Ω t).1 l := by
                    simpa using (Fintype.sum_ite_eq (i := (Ω t).1)
                      (f := fun j : Fin M => u t * Z j l))
              _ = (if (Ω t).2 = i then u t else 0) * Z (Ω t).1 l := by
                    simp [hi]
          · have hneq : ∀ x : Fin M, Ω t ≠ (x, i) := by
              intro x hx
              exact hi (by simpa [hx] using congrArg Prod.snd hx)
            have hz :
                ∀ x : Fin M, (if Ω t = (x, i) then u t else 0) * Z x l = 0 := by
              intro x
              by_cases hx : Ω t = (x, i)
              · exact (hneq x hx).elim
              · simp [hx]
            calc
              (∑ x : Fin M, (if Ω t = (x, i) then u t else 0) * Z x l) = 0 := by
                exact Fintype.sum_eq_zero
                  (f := fun x : Fin M => (if Ω t = (x, i) then u t else 0) * Z x l) hz
              _ = (if (Ω t).2 = i then u t else 0) * Z (Ω t).1 l := by simp [hi]

theorem sparseMTTKRP_apply_observed
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (i : Fin n) (l : Fin r) :
    sparseMTTKRP Ω vals Z i l
      = ∑ t : Fin q, (if (Ω t).2 = i then vals t else 0) * Z (Ω t).1 l := by
  simpa [sparseMTTKRP] using scatter_mul_apply_observed (Ω := Ω) (u := vals) (Z := Z) i l

theorem rhsFromObserved_eq_vec
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real) :
    rhsFromObserved K Ω vals Z = (K * sparseMTTKRP Ω vals Z).vec := by
  unfold rhsFromObserved
  simp [Matrix.kronecker_mulVec_vec, Matrix.transpose_one, Matrix.mul_one]

/-- The dense vectorized operator from q10:
`((Z ⊗ K)ᵀ S Sᵀ (Z ⊗ K) + λ (I ⊗ K)) * vec(W)`. -/
def applyDenseVec
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real) (x : Fin r × Fin n → Real) : Fin r × Fin n → Real :=
  (((Z ⊗ₖ K)ᵀ * selectionMatrix Ω * (selectionMatrix Ω)ᵀ * (Z ⊗ₖ K))
      + lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ K)) *ᵥ x

/-- Matrix-free application of the same linear operator, written in `n × r` matrix form. -/
def applyMatrixFree
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) : Matrix (Fin n) (Fin r) Real :=
  let P := K * W
  let u := gather Ω (P * Zᵀ)
  let U := scatter Ω u
  K * (U * Z) + lam • P

/-- Step-B formula: each gathered observation is a row dot-product. -/
theorem gather_apply_kernelPredict
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (W : Matrix (Fin n) (Fin r) Real)
    (t : Fin q) :
    gather Ω (K * W * Zᵀ) t
      = ∑ l : Fin r, (K * W) (Ω t).2 l * Z (Ω t).1 l := by
  simpa [Matrix.mul_apply, dotProduct] using
    (gather_apply (Ω := Ω) (X := K * W * Zᵀ) t)

/-- Step-D matrix-free decomposition exactly matching method's `P/u/G` pipeline. -/
theorem applyMatrixFree_eq_pipeline
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real)
    (W : Matrix (Fin n) (Fin r) Real) :
    applyMatrixFree K Z Ω lam W
      = K * ((scatter Ω (gather Ω (K * W * Zᵀ))) * Z) + lam • (K * W) := by
  unfold applyMatrixFree
  simp [Matrix.mul_assoc]

/-- Sparse Step-B implementation: gather predicted values on `Ω` via row dot products. -/
def gatherKernelPredictSparse
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (W : Matrix (Fin n) (Fin r) Real) : Fin q → Real :=
  fun t => ∑ l : Fin r, (K * W) (Ω t).2 l * Z (Ω t).1 l

theorem gatherKernelPredictSparse_eq_gather
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (W : Matrix (Fin n) (Fin r) Real) :
    gatherKernelPredictSparse K Z Ω W = gather Ω (K * W * Zᵀ) := by
  funext t
  symm
  exact gather_apply_kernelPredict (K := K) (Z := Z) (Ω := Ω) (W := W) (t := t)

/-- Sparse Step-C implementation: compute `G = UZ` using observed-index accumulation only. -/
def scatterMulSparse
    (Ω : Fin q → Fin M × Fin n)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real) : Matrix (Fin n) (Fin r) Real :=
  Matrix.of fun i l => ∑ t : Fin q, (if (Ω t).2 = i then u t else 0) * Z (Ω t).1 l

theorem scatterMulSparse_eq_scatter_mul
    (Ω : Fin q → Fin M × Fin n)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real) :
    scatterMulSparse Ω Z u = (scatter Ω u) * Z := by
  ext i l
  simpa [scatterMulSparse] using (scatter_mul_apply_observed (Ω := Ω) (u := u) (Z := Z) (i := i) (l := l)).symm

/-- Row-bucketed observation index structure (CSR-style): `rows i` stores all observed ids with mode-k row `i`. -/
structure ObsBuckets (Ω : Fin q → Fin M × Fin n) where
  rows : Fin n → Finset (Fin q)
  mem_rows_iff : ∀ i : Fin n, ∀ t : Fin q, t ∈ rows i ↔ (Ω t).2 = i

/-- Canonical bucketization induced by filtering `univ` by row id. -/
def canonicalObsBuckets (Ω : Fin q → Fin M × Fin n) : ObsBuckets Ω where
  rows i := Finset.univ.filter (fun t : Fin q => (Ω t).2 = i)
  mem_rows_iff := by
    intro i t
    simp

/-- Bucketed Step-C implementation: for each row bucket, accumulate only bucket members. -/
def scatterMulBucketed
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real) : Matrix (Fin n) (Fin r) Real :=
  Matrix.of fun i l => ∑ t ∈ (B.rows i), u t * Z (Ω t).1 l

theorem scatterMulBucketed_apply
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real)
    (i : Fin n) (l : Fin r) :
    scatterMulBucketed Ω B Z u i l
      = ∑ t ∈ (B.rows i), u t * Z (Ω t).1 l := by
  simp [scatterMulBucketed]

theorem scatterMulBucketed_eq_scatterMulSparse
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real) :
    scatterMulBucketed Ω B Z u = scatterMulSparse Ω Z u := by
  ext i l
  have hRows :
      B.rows i = Finset.univ.filter (fun t : Fin q => (Ω t).2 = i) := by
    ext t
    simpa [B.mem_rows_iff i t]
  calc
    scatterMulBucketed Ω B Z u i l
        = ∑ t ∈ (B.rows i), u t * Z (Ω t).1 l := by
            simp [scatterMulBucketed]
    _ = ∑ t ∈ Finset.univ.filter (fun t : Fin q => (Ω t).2 = i), u t * Z (Ω t).1 l := by
          rw [hRows]
    _ = ∑ t : Fin q, (if (Ω t).2 = i then u t * Z (Ω t).1 l else 0) := by
          simpa using
            (Finset.sum_filter (s := Finset.univ)
              (p := fun t : Fin q => (Ω t).2 = i)
              (f := fun t : Fin q => u t * Z (Ω t).1 l))
    _ = ∑ t : Fin q, (if (Ω t).2 = i then u t else 0) * Z (Ω t).1 l := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          by_cases hi : (Ω t).2 = i
          · simp [hi]
          · simp [hi]
    _ = scatterMulSparse Ω Z u i l := by
          simp [scatterMulSparse]

theorem scatterMulCanonical_eq_scatterMulSparse
    (Ω : Fin q → Fin M × Fin n)
    (Z : Matrix (Fin M) (Fin r) Real)
    (u : Fin q → Real) :
    scatterMulBucketed Ω (canonicalObsBuckets Ω) Z u = scatterMulSparse Ω Z u := by
  exact scatterMulBucketed_eq_scatterMulSparse
    (Ω := Ω) (B := canonicalObsBuckets Ω) (Z := Z) (u := u)

/-- Observed-row provider: row `t` is generated on the fly as a length-`r` vector. -/
def ObsRowProvider (q r : Nat) := Fin q → Fin r → Real

/-- Factor-row provider for observed entries:
for each auxiliary mode `m`, observation `t`, and rank index `l`, return the factor value. -/
def ObsFactorProvider (d q r : Nat) := Fin d → Fin q → Fin r → Real

/-- Online observed-row generation by Hadamard product across factors:
`z^{(t)}_l = ∏_m F m t l`. -/
def obsRowFromFactors {d q r : Nat} (F : ObsFactorProvider d q r) : ObsRowProvider q r :=
  fun t l => ∏ m : Fin d, F m t l

@[simp]
theorem obsRowFromFactors_apply {d q r : Nat}
    (F : ObsFactorProvider d q r) (t : Fin q) (l : Fin r) :
    obsRowFromFactors F t l = ∏ m : Fin d, F m t l := rfl

/-- A factor provider `F` generates the same observed rows as explicit matrix `Z`
on coordinates selected by `Ω`. -/
def factorsGenerateObservedRows
    {d n M r q : Nat}
    (Ω : Fin q → Fin M × Fin n)
    (Z : Matrix (Fin M) (Fin r) Real)
    (F : ObsFactorProvider d q r) : Prop :=
  ∀ t : Fin q, obsRowFromFactors F t = fun l : Fin r => Z (Ω t).1 l

theorem factorsGenerateObservedRows_apply
    {d n M r q : Nat}
    (Ω : Fin q → Fin M × Fin n)
    (Z : Matrix (Fin M) (Fin r) Real)
    (F : ObsFactorProvider d q r)
    (hRows : factorsGenerateObservedRows (Ω := Ω) (Z := Z) F) :
    ∀ t : Fin q, ∀ l : Fin r, obsRowFromFactors F t l = Z (Ω t).1 l := by
  intro t l
  simpa using congrArg (fun g : Fin r → Real => g l) (hRows t)

/-- Khatri-Rao row model over a Cartesian-product row index type:
each row is the Hadamard product of factor rows. -/
def khatriRaoPi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (A : (i : ι) → Matrix (κ i) (Fin r) Real) :
    Matrix ((i : ι) → κ i) (Fin r) Real :=
  fun x l => ∏ i, A i (x i) l

/-- Entrywise product of per-mode Gram matrices:
`(a,b)` entry equals `∏ᵢ ((Aᵢᵀ Aᵢ)₍a,b₎)`. -/
def gramFromFactors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (A : (i : ι) → Matrix (κ i) (Fin r) Real) :
    Matrix (Fin r) (Fin r) Real :=
  fun a b => ∏ i, (((A i)ᵀ * (A i)) a b)

/-- Reindex matrix rows through an equivalence. -/
def reindexRows
    {α β : Type*}
    (e : α ≃ β)
    (Z : Matrix β (Fin r) Real) :
    Matrix α (Fin r) Real :=
  fun a l => Z (e a) l

theorem reindexRows_gram
    {α β : Type*}
    [Fintype α] [Fintype β]
    (e : α ≃ β)
    (Z : Matrix β (Fin r) Real) :
    (reindexRows (r := r) e Z)ᵀ * reindexRows (r := r) e Z = Zᵀ * Z := by
  ext a b
  simp [reindexRows, Matrix.mul_apply]
  exact Equiv.sum_comp e (fun x : β => Z x a * Z x b)

theorem khatriRaoPi_gram_entry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (A : (i : ι) → Matrix (κ i) (Fin r) Real)
    (a b : Fin r) :
    (((khatriRaoPi (r := r) A)ᵀ * (khatriRaoPi (r := r) A)) a b)
      = (gramFromFactors (r := r) A) a b := by
  classical
  unfold gramFromFactors
  simp [khatriRaoPi, Matrix.mul_apply]
  have hsumMul :
      (∑ x : (i : ι) → κ i,
        (∏ i, A i (x i) a) * (∏ i, A i (x i) b))
      = ∑ x : (i : ι) → κ i, ∏ i, (A i (x i) a * A i (x i) b) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.prod_mul_distrib]
  rw [hsumMul]
  calc
    ∑ x : (i : ι) → κ i, ∏ i, (A i (x i) a * A i (x i) b)
        = ∑ x ∈ (Fintype.piFinset fun i : ι => (Finset.univ : Finset (κ i))),
            ∏ i, (A i (x i) a * A i (x i) b) := by
              simp
    _ = ∏ i, ∑ j ∈ (Finset.univ : Finset (κ i)), (A i j a * A i j b) := by
          symm
          exact Finset.prod_univ_sum
            (t := fun i : ι => (Finset.univ : Finset (κ i)))
            (f := fun i j => A i j a * A i j b)
    _ = ∏ i, ∑ j : κ i, (A i j a * A i j b) := by
          simp
    _ = ∏ i, (((A i)ᵀ * (A i)) a b) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          simp [Matrix.mul_apply]

theorem khatriRaoPi_gram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (A : (i : ι) → Matrix (κ i) (Fin r) Real) :
    (khatriRaoPi (r := r) A)ᵀ * (khatriRaoPi (r := r) A)
      = gramFromFactors (r := r) A := by
  ext a b
  exact khatriRaoPi_gram_entry (r := r) (A := A) (a := a) (b := b)

/-- Step-B using an on-demand observed-row provider (no explicit `M × r` matrix required). -/
def gatherKernelPredictObserved
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (zObs : ObsRowProvider q r)
    (W : Matrix (Fin n) (Fin r) Real) : Fin q → Real :=
  fun t => ∑ l : Fin r, (K * W) (Ω t).2 l * zObs t l

theorem gatherKernelPredictObserved_eq_sparse
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (zObs : ObsRowProvider q r)
    (hRows : ∀ t : Fin q, zObs t = fun l : Fin r => Z (Ω t).1 l)
    (W : Matrix (Fin n) (Fin r) Real) :
    gatherKernelPredictObserved K Ω zObs W = gatherKernelPredictSparse K Z Ω W := by
  funext t
  simp [gatherKernelPredictObserved, gatherKernelPredictSparse, hRows t]

/-- Step-C with on-demand observed rows: sparse accumulation only over `q` observations. -/
def scatterMulObserved
    (Ω : Fin q → Fin M × Fin n)
    (zObs : ObsRowProvider q r)
    (u : Fin q → Real) : Matrix (Fin n) (Fin r) Real :=
  Matrix.of fun i l => ∑ t : Fin q, (if (Ω t).2 = i then u t else 0) * zObs t l

theorem scatterMulObserved_eq_sparse
    (Ω : Fin q → Fin M × Fin n)
    (Z : Matrix (Fin M) (Fin r) Real)
    (zObs : ObsRowProvider q r)
    (hRows : ∀ t : Fin q, zObs t = fun l : Fin r => Z (Ω t).1 l)
    (u : Fin q → Real) :
    scatterMulObserved Ω zObs u = scatterMulSparse Ω Z u := by
  ext i l
  simp [scatterMulObserved, scatterMulSparse, hRows]

/-- Fully matrix-free operator using only observed-row provider `zObs`. -/
def applyMatrixFreeObserved
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (zObs : ObsRowProvider q r)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) : Matrix (Fin n) (Fin r) Real :=
  let P := K * W
  let u := gatherKernelPredictObserved K Ω zObs W
  let G := scatterMulObserved Ω zObs u
  K * G + lam • P

theorem applyMatrixFreeObserved_eq_applyMatrixFree
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (zObs : ObsRowProvider q r)
    (hRows : ∀ t : Fin q, zObs t = fun l : Fin r => Z (Ω t).1 l)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    applyMatrixFreeObserved K Ω zObs lam W = applyMatrixFree K Z Ω lam W := by
  have hu :
      gatherKernelPredictObserved K Ω zObs W = gather Ω (K * W * Zᵀ) := by
    calc
      gatherKernelPredictObserved K Ω zObs W = gatherKernelPredictSparse K Z Ω W :=
        gatherKernelPredictObserved_eq_sparse (K := K) (Z := Z) (Ω := Ω)
          (zObs := zObs) (hRows := hRows) (W := W)
      _ = gather Ω (K * W * Zᵀ) := by
        exact gatherKernelPredictSparse_eq_gather (K := K) (Z := Z) (Ω := Ω) (W := W)
  have hG :
      scatterMulObserved Ω zObs (gatherKernelPredictObserved K Ω zObs W)
        = (scatter Ω (gather Ω (K * W * Zᵀ))) * Z := by
    calc
      scatterMulObserved Ω zObs (gatherKernelPredictObserved K Ω zObs W)
          = scatterMulSparse Ω Z (gatherKernelPredictObserved K Ω zObs W) :=
            scatterMulObserved_eq_sparse (Ω := Ω) (Z := Z) (zObs := zObs) (hRows := hRows)
              (u := gatherKernelPredictObserved K Ω zObs W)
      _ = scatterMulSparse Ω Z (gather Ω (K * W * Zᵀ)) := by simp [hu]
      _ = (scatter Ω (gather Ω (K * W * Zᵀ))) * Z :=
            scatterMulSparse_eq_scatter_mul (Ω := Ω) (Z := Z) (u := gather Ω (K * W * Zᵀ))
  unfold applyMatrixFreeObserved applyMatrixFree
  simpa [hG]

/-- Observed-data MTTKRP using on-demand observed rows `zObs`
(`z^{(t)}` from the solution note), without explicit `Z : M × r`. -/
def sparseMTTKRPObserved
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (zObs : ObsRowProvider q r) : Matrix (Fin n) (Fin r) Real :=
  Matrix.of fun i l => ∑ t : Fin q, (if (Ω t).2 = i then vals t else 0) * zObs t l

theorem sparseMTTKRPObserved_eq_sparseMTTKRP
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (zObs : ObsRowProvider q r)
    (hRows : ∀ t : Fin q, zObs t = fun l : Fin r => Z (Ω t).1 l) :
    sparseMTTKRPObserved Ω vals zObs = sparseMTTKRP Ω vals Z := by
  ext i l
  simp [sparseMTTKRPObserved, sparseMTTKRP_apply_observed, hRows]

/-- RHS from observed data using only `zObs` rows. -/
def rhsFromObservedRows
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (zObs : ObsRowProvider q r) : Fin r × Fin n → Real :=
  ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ K) *ᵥ (sparseMTTKRPObserved Ω vals zObs).vec

theorem rhsFromObservedRows_eq_rhsFromObserved
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (zObs : ObsRowProvider q r)
    (hRows : ∀ t : Fin q, zObs t = fun l : Fin r => Z (Ω t).1 l) :
    rhsFromObservedRows K Ω vals zObs = rhsFromObserved K Ω vals Z := by
  unfold rhsFromObservedRows rhsFromObserved
  rw [sparseMTTKRPObserved_eq_sparseMTTKRP
    (Ω := Ω) (vals := vals) (Z := Z) (zObs := zObs) (hRows := hRows)]

theorem rhsFromObservedRows_from_factors_eq_rhsFromObserved
    {d : Nat}
    (K : Matrix (Fin n) (Fin n) Real)
    (Ω : Fin q → Fin M × Fin n)
    (vals : Fin q → Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (F : ObsFactorProvider d q r)
    (hRows : factorsGenerateObservedRows (Ω := Ω) (Z := Z) F) :
    rhsFromObservedRows K Ω vals (obsRowFromFactors F) = rhsFromObserved K Ω vals Z := by
  exact rhsFromObservedRows_eq_rhsFromObserved
    (K := K) (Ω := Ω) (vals := vals) (Z := Z)
    (zObs := obsRowFromFactors F) (hRows := hRows)

/-- Fully sparse matrix-free operator: only `q`-indexed sums + `K`-matmul (no explicit `N` object). -/
def applyMatrixFreeSparse
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) : Matrix (Fin n) (Fin r) Real :=
  let P := K * W
  let u := gatherKernelPredictSparse K Z Ω W
  let G := scatterMulSparse Ω Z u
  K * G + lam • P

/-- Bucketed/CSR matrix-free operator:
same algebra as `applyMatrixFreeSparse`, but Step-C uses row buckets. -/
def applyMatrixFreeBucketed
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) : Matrix (Fin n) (Fin r) Real :=
  let P := K * W
  let u := gatherKernelPredictSparse K Z Ω W
  let G := scatterMulBucketed Ω B Z u
  K * G + lam • P

theorem applyMatrixFreeBucketed_eq_sparse
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (B : ObsBuckets Ω)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    applyMatrixFreeBucketed K Z Ω B lam W = applyMatrixFreeSparse K Z Ω lam W := by
  unfold applyMatrixFreeBucketed applyMatrixFreeSparse
  simp [scatterMulBucketed_eq_scatterMulSparse]

theorem applyMatrixFreeCanonicalBucketed_eq_sparse
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    applyMatrixFreeBucketed K Z Ω (canonicalObsBuckets Ω) lam W = applyMatrixFreeSparse K Z Ω lam W := by
  exact applyMatrixFreeBucketed_eq_sparse
    (K := K) (Z := Z) (Ω := Ω) (B := canonicalObsBuckets Ω) (lam := lam) (W := W)

theorem applyMatrixFreeSparse_eq_applyMatrixFree
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real)
    (W : Matrix (Fin n) (Fin r) Real) :
    applyMatrixFreeSparse K Z Ω lam W = applyMatrixFree K Z Ω lam W := by
  unfold applyMatrixFreeSparse applyMatrixFree
  simp [gatherKernelPredictSparse_eq_gather, scatterMulSparse_eq_scatter_mul]

theorem applyMatrixFreeObserved_eq_sparse
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (zObs : ObsRowProvider q r)
    (hRows : ∀ t : Fin q, zObs t = fun l : Fin r => Z (Ω t).1 l)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    applyMatrixFreeObserved K Ω zObs lam W = applyMatrixFreeSparse K Z Ω lam W := by
  calc
    applyMatrixFreeObserved K Ω zObs lam W = applyMatrixFree K Z Ω lam W :=
      applyMatrixFreeObserved_eq_applyMatrixFree (K := K) (Z := Z) (Ω := Ω)
        (zObs := zObs) (hRows := hRows) (lam := lam) (W := W)
    _ = applyMatrixFreeSparse K Z Ω lam W := by
      symm
      exact applyMatrixFreeSparse_eq_applyMatrixFree (K := K) (Z := Z) (Ω := Ω) (lam := lam) (W := W)

theorem applyMatrixFreeObserved_from_factors_eq_sparse
    {d : Nat}
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (F : ObsFactorProvider d q r)
    (hRows : factorsGenerateObservedRows (Ω := Ω) (Z := Z) F)
    (lam : Real) (W : Matrix (Fin n) (Fin r) Real) :
    applyMatrixFreeObserved K Ω (obsRowFromFactors F) lam W = applyMatrixFreeSparse K Z Ω lam W := by
  exact applyMatrixFreeObserved_eq_sparse
    (K := K) (Z := Z) (Ω := Ω) (zObs := obsRowFromFactors F)
    (hRows := hRows) (lam := lam) (W := W)

/-- The right-hand side in vectorized form: `(I ⊗ K) * vec(B)`. -/
def rhsVec
    (K : Matrix (Fin n) (Fin n) Real)
    (B : Matrix (Fin n) (Fin r) Real) : Fin r × Fin n → Real :=
  ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ K) *ᵥ B.vec

@[simp]
theorem rhsVec_eq_vec
    (K : Matrix (Fin n) (Fin n) Real)
    (B : Matrix (Fin n) (Fin r) Real) :
    rhsVec K B = (K * B).vec := by
  unfold rhsVec
  simp [Matrix.kronecker_mulVec_vec, Matrix.transpose_one, Matrix.mul_one]

/-- Core equivalence theorem for q10: dense Kronecker/selection form equals matrix-free form. -/
theorem applyDenseVec_eq_vec_applyMatrixFree
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real)
    (hK : Kᵀ = K)
    (W : Matrix (Fin n) (Fin r) Real) :
    applyDenseVec K Z Ω lam W.vec = (applyMatrixFree K Z Ω lam W).vec := by
  classical
  unfold applyDenseVec applyMatrixFree
  rw [Matrix.add_mulVec, Matrix.smul_mulVec]
  simp [Matrix.kronecker_mulVec_vec, Matrix.transpose_one, Matrix.mul_one, Matrix.vec_add,
    Matrix.vec_smul, Matrix.mul_assoc]
  rw [show (Z ⊗ₖ K)ᵀ = Zᵀ ⊗ₖ Kᵀ by
    simpa using (Matrix.kroneckerMap_transpose (f := (· * ·)) (A := Z) (B := K)).symm]
  rw [hK]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.kronecker_mulVec_vec]
  change (Zᵀ ⊗ₖ K) *ᵥ ((selectionMatrix Ω) *ᵥ ((selectionMatrix Ω)ᵀ *ᵥ (K * W * Zᵀ).vec)) =
      (K * (scatter Ω (gather Ω (K * (W * Zᵀ))) * Z)).vec
  rw [show (selectionMatrix Ω)ᵀ *ᵥ (K * W * Zᵀ).vec = gather Ω (K * W * Zᵀ) by rfl]
  rw [← vec_scatter (Ω := Ω) (u := gather Ω (K * W * Zᵀ))]
  rw [Matrix.kronecker_mulVec_vec]
  simp [Matrix.mul_assoc]

theorem applyDenseVec_eq_vec_applyMatrixFreeSparse
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real)
    (hK : Kᵀ = K)
    (W : Matrix (Fin n) (Fin r) Real) :
    applyDenseVec K Z Ω lam W.vec = (applyMatrixFreeSparse K Z Ω lam W).vec := by
  simpa [applyMatrixFreeSparse_eq_applyMatrixFree] using
    (applyDenseVec_eq_vec_applyMatrixFree (K := K) (Z := Z) (Ω := Ω)
      (lam := lam) (hK := hK) (W := W))

/-- Embed a vector as the first column of an `n × r` matrix (other columns zero). -/
def firstColMatrix (hr : 0 < r) (v : Fin n → Real) : Matrix (Fin n) (Fin r) Real :=
  Matrix.of fun i j => if j = ⟨0, hr⟩ then v i else 0

theorem firstColMatrix_ne_zero (hr : 0 < r) {v : Fin n → Real} (hv : v ≠ 0) :
    firstColMatrix (n := n) (r := r) hr v ≠ 0 := by
  intro h0
  apply hv
  funext i
  have hentry : firstColMatrix (n := n) (r := r) hr v i ⟨0, hr⟩ = 0 := by
    simpa using congrArg (fun M => M i ⟨0, hr⟩) h0
  simpa [firstColMatrix] using hentry

theorem K_mul_firstColMatrix_eq_zero
    (K : Matrix (Fin n) (Fin n) Real)
    (hr : 0 < r)
    {v : Fin n → Real}
    (hKv : K *ᵥ v = 0) :
    K * firstColMatrix (n := n) (r := r) hr v = 0 := by
  ext i j
  by_cases hj : j = ⟨0, hr⟩
  · subst hj
    have hi : (K *ᵥ v) i = 0 := by
      simpa using congrArg (fun f => f i) hKv
    simpa [firstColMatrix, Matrix.mul_apply, dotProduct] using hi
  · have hzero : ∀ k : Fin n, firstColMatrix (n := n) (r := r) hr v k j = 0 := by
      intro k
      simp [firstColMatrix, hj]
    calc
      (K * firstColMatrix (n := n) (r := r) hr v) i j
          = ∑ k : Fin n, K i k * firstColMatrix (n := n) (r := r) hr v k j := by
              simp [Matrix.mul_apply]
      _ = ∑ k : Fin n, 0 := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [hzero k]
      _ = 0 := by simp

theorem dense_operator_has_nontrivial_kernel_of_kernel_nullvec
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real)
    (hK : Kᵀ = K)
    (hr : 0 < r)
    {v : Fin n → Real}
    (hv : v ≠ 0)
    (hKv : K *ᵥ v = 0) :
    ∃ x : Fin r × Fin n → Real, x ≠ 0 ∧ applyDenseVec K Z Ω lam x = 0 := by
  let W : Matrix (Fin n) (Fin r) Real := firstColMatrix (n := n) (r := r) hr v
  have hWne : W ≠ 0 := firstColMatrix_ne_zero (n := n) (r := r) hr hv
  have hKW : K * W = 0 := by
    simpa [W] using K_mul_firstColMatrix_eq_zero (K := K) (hr := hr) (hKv := hKv)
  have hSparse : applyMatrixFreeSparse K Z Ω lam W = 0 := by
    have hu : gatherKernelPredictSparse K Z Ω W = 0 := by
      funext t
      simp [gatherKernelPredictSparse, hKW]
    have hG : scatterMulSparse Ω Z (0 : Fin q → Real) = 0 := by
      ext i l
      simp [scatterMulSparse]
    unfold applyMatrixFreeSparse
    simp [hKW, hu, hG]
  refine ⟨W.vec, ?_, ?_⟩
  · intro hvec
    exact hWne (Matrix.vec_eq_zero_iff.mp hvec)
  · calc
      applyDenseVec K Z Ω lam W.vec = (applyMatrixFreeSparse K Z Ω lam W).vec :=
        applyDenseVec_eq_vec_applyMatrixFreeSparse
          (K := K) (Z := Z) (Ω := Ω) (lam := lam) (hK := hK) (W := W)
      _ = 0 := by simpa [hSparse]

/-- Intermediate equivalence lemma: dense vectorized form equals matrix-free matrix form. -/
theorem q10_system_equiv_matrixFree
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real)
    (hK : Kᵀ = K)
    (W B : Matrix (Fin n) (Fin r) Real) :
    applyDenseVec K Z Ω lam W.vec = rhsVec K B ↔ applyMatrixFree K Z Ω lam W = K * B := by
  rw [applyDenseVec_eq_vec_applyMatrixFree (K := K) (Z := Z) (Ω := Ω) (lam := lam) (hK := hK)
      (W := W), rhsVec_eq_vec]
  exact Matrix.vec_inj

theorem q10_system_equiv_matrixFreeSparse
    (K : Matrix (Fin n) (Fin n) Real)
    (Z : Matrix (Fin M) (Fin r) Real)
    (Ω : Fin q → Fin M × Fin n)
    (lam : Real)
    (hK : Kᵀ = K)
    (W B : Matrix (Fin n) (Fin r) Real) :
    applyDenseVec K Z Ω lam W.vec = rhsVec K B ↔ applyMatrixFreeSparse K Z Ω lam W = K * B := by
  rw [applyDenseVec_eq_vec_applyMatrixFreeSparse (K := K) (Z := Z) (Ω := Ω) (lam := lam) (hK := hK)
      (W := W), rhsVec_eq_vec]
  exact Matrix.vec_inj


end
end Q10
end AutoProof
