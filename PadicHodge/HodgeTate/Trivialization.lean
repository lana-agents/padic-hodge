/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.HodgeTate.FiniteImage
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Representations trivialised over `ℂ_p` are Hodge–Tate of weight `0`

Let `ρ` be a representation of `G_L` on `V` with basis `b`, and `R(σ)` the matrix of `ρ(σ)`.
If some `X ∈ GL_h(ℂ_p)` satisfies `R(σ) σ(X) = X` for all `σ ∈ G_L` (e.g. by Hilbert 90 for
`\hat{ℚ_p^{ur}}` if `ρ` is unramified), then the columns `w_j = ∑_i X_{ij} ⊗ b_i` of `X` are
`G_L`-invariant and `ℂ_p`-linearly independent, so `dim_L (ℂ_p ⊗ V)^{G_L} = dim V`
(`le_finrank_DHT_zero_of_matrix`): `V` is Hodge–Tate with all weights `0`
(`isHodgeTate_of_matrix`).
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] L] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  [FiniteDimensional ℚ_[p] V]
  (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V)
  {h : ℕ} (b : Basis (Fin h) ℚ_[p] V) (X : Matrix (Fin h) (Fin h) ℂ_[p]) (hX : IsUnit X.det)
  (hinv : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
    (LinearMap.toMatrix b b (ρ σ)).map (algebraMap ℚ_[p] ℂ_[p]) * X.map (galCp L σ) = X)

include hX hinv in
/-- **The columns of a trivialising matrix are independent invariants.** -/
theorem le_finrank_DHT_zero_of_matrix : h ≤ finrank L (DHT ρ 0) := by
  classical
  let B : Basis (Fin h) ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) := Algebra.TensorProduct.basis ℂ_[p] b
  have hB : ∀ i, B i = (1 : ℂ_[p]) ⊗ₜ b i := fun i => Algebra.TensorProduct.basis_apply b i
  let e := Matrix.toLinearEquiv B X hX
  let w : Fin h → ℂ_[p] ⊗[ℚ_[p]] V := fun j => e (B j)
  have hw : ∀ j, w j = ∑ i, X i j ⊗ₜ b i := by
    intro j
    simp only [w, e]
    rw [Matrix.toLinearEquiv_apply, Matrix.toLin_self]
    simp only [hB, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hli : LinearIndependent ℂ_[p] w := (B.map e).linearIndependent
  have hρb : ∀ σ i, ρ σ (b i) = ∑ l, (LinearMap.toMatrix b b (ρ σ) l i) • b l := by
    intro σ i
    simp only [LinearMap.toMatrix_apply]
    exact (b.sum_repr _).symm
  have hinvw : ∀ σ j, TensorProduct.map (galCpLin L σ) (ρ σ) (w j) = w j := by
    intro σ j
    rw [hw, map_sum]
    have e1 : ∀ i, TensorProduct.map (galCpLin L σ) (ρ σ) (X i j ⊗ₜ b i) =
        ∑ l, (algebraMap ℚ_[p] ℂ_[p] (LinearMap.toMatrix b b (ρ σ) l i) *
          galCp L σ (X i j)) ⊗ₜ b l := by
      intro i
      rw [TensorProduct.map_tmul, galCpLin_apply, hρb, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
    rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← TensorProduct.sum_tmul]
    congr 1
    have hx := congrFun (congrFun (hinv σ) l) j
    rw [Matrix.mul_apply] at hx
    rw [← hx]
    rfl
  have hmem : ∀ j, cpt ρ (w j) ∈ DHT ρ 0 := by
    intro j
    rw [mem_DHT]
    intro σ
    rw [(htSetup L).ψ_zero σ, one_smul, gal_smul_cpTensor]
    exact hinvw σ j
  have hli' : LinearIndependent ℂ_[p] (fun j => cpt ρ (w j)) := hli
  have hliL : LinearIndependent L (fun j => cpt ρ (w j)) :=
    hli'.restrict_scalars' L
  have hliD : LinearIndependent L (fun j => (⟨cpt ρ (w j), hmem j⟩ : DHT ρ 0)) :=
    LinearIndependent.of_comp (DHT ρ 0).subtype hliL
  simpa using hliD.fintype_card_le_finrank

include hX hinv in
/-- **A representation trivialised over `ℂ_p` is Hodge–Tate with all weights `0`.** -/
theorem isHodgeTate_of_matrix :
    IsHodgeTate ρ ∧ (htWeights ρ).count 0 = finrank ℚ_[p] V := by
  classical
  have hle := le_finrank_DHT_zero_of_matrix ρ b X hX hinv
  have hh : finrank ℚ_[p] V = h := by rw [finrank_eq_card_basis b, Fintype.card_fin]
  have hD : finrank L (DHT ρ 0) = finrank ℚ_[p] V := by
    refine le_antisymm ?_ (hh ▸ hle)
    simpa using sum_finrank_DHT_le ρ {0}
  refine ⟨le_antisymm (htDim_le ρ) ?_, by rw [count_htWeights, hD]⟩
  set S := (finite_support_DHT ρ).toFinset ∪ {0}
  rw [htDim_eq_sum ρ (S := S) (fun q hq => Finset.mem_union_left _ (by simpa using hq))]
  calc finrank ℚ_[p] V = finrank L (DHT ρ 0) := hD.symm
    _ ≤ ∑ q ∈ S, finrank L (DHT ρ q) :=
      Finset.single_le_sum (f := fun q => finrank L (DHT ρ q)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_union_right _ (Finset.mem_singleton_self 0))

end PadicHodge
