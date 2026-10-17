/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.HodgeTate.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Representations with finite image are Hodge–Tate of weight `0`

Let `L / ℚ_p` be finite and `ρ : G_L → GL(V)` a representation which is trivial on `G_M` for a
finite extension `M / L` inside `ℚ̄_p` (`ρ` has finite image). Then
`dim_L (ℂ_p ⊗ V)^{G_L} = dim V` (`finrank_DHT_zero_of_trivial_on`), so `V` is Hodge–Tate with all
Hodge–Tate weights `0` (`isHodgeTate_of_trivial_on`, `count_htWeights_zero_of_trivial_on`).
(For instance the Tate module of an étale `p`-divisible group over `O_K` whose Galois action
factors through a finite quotient; the general étale case needs Hilbert 90 for `\hat{K^{ur}}`,
see `Blueprint.md`.)

Proof (Galois descent, standard; written up here): for each `L`-embedding `e : M → ℚ̄_p` choose
`σ_e ∈ G_L` extending it (`AlgHom.liftNormal`). For `m ∈ M`, `v ∈ V` the trace
`Tr(m ⊗ v) = ∑_e σ_e (m ⊗ v) = ∑_e e(m) (1 ⊗ ρ(σ_e) v)` is `G_L`-invariant (`trace_mem_DHT`: for
`σ ∈ G_L`, `σ σ_e` and `σ_{σ ∘ e}` agree on `M`, and `G_M` fixes `m ⊗ v`). The matrix
`(e(m_j))_{e, j}` for an `L`-basis `(m_j)` of `M` is square (`#Hom_L(M, ℚ̄_p) = [M : L]`,
`AlgHom.card`) with linearly independent rows (Dedekind), hence invertible; so `1 ⊗ v` is a
`ℚ̄_p`-combination of the `Tr(m_j ⊗ v)` (take the row of the inclusion `M ⊆ ℚ̄_p`, with
`ρ(σ_ι) = 1`). Thus the invariants span `ℂ_p ⊗ V` over `ℂ_p`, and an `L`-basis of them is a
`ℂ_p`-basis by the Serre–Tate lemma (`SerreTate.linearIndependent_of_eigen_single`).
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V)

/-- A tensor, viewed in `CpTensor ρ`. -/
def cpt (x : ℂ_[p] ⊗[ℚ_[p]] V) : CpTensor ρ := x

theorem cpt_smul (c : ℂ_[p]) (x : ℂ_[p] ⊗[ℚ_[p]] V) : c • cpt ρ x = cpt ρ (c • x) := rfl

theorem gal_smul_tmul (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (c : ℂ_[p]) (v : V) :
    σ • cpt ρ (c ⊗ₜ v) = cpt ρ (galCp L σ c ⊗ₜ ρ σ v) := by
  rw [cpt, gal_smul_cpTensor, TensorProduct.map_tmul, galCpLin_apply]
  rfl

variable (M : IntermediateField L (PadicAlgCl p))

instance : Normal L (PadicAlgCl p) := Normal.tower_top_of_normal ℚ_[p] L (PadicAlgCl p)

/-- An element of `G_L` extending an `L`-embedding `M → ℚ̄_p`. -/
def liftEmb (e : M →ₐ[L] PadicAlgCl p) : PadicAlgCl p ≃ₐ[L] PadicAlgCl p :=
  AlgEquiv.ofBijective (e.liftNormal (PadicAlgCl p)) (AlgHom.normal_bijective L _ _ _)

theorem liftEmb_apply (e : M →ₐ[L] PadicAlgCl p) (m : M) :
    liftEmb M e (m : PadicAlgCl p) = e m :=
  e.liftNormal_commutes (PadicAlgCl p) m

variable {ρ M}
variable (hρ : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, (∀ m ∈ M, σ m = m) → ρ σ = 1)

include hρ

/-- The vector `m ⊗ v ∈ ℂ_p ⊗ V` for `m ∈ M`. -/
abbrev mTensor (m : M) (v : V) : CpTensor ρ :=
  cpt ρ (((m : PadicAlgCl p) : ℂ_[p]) ⊗ₜ v)

omit hρ in
theorem smul_mTensor (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (m : M) (v : V) :
    σ • mTensor (ρ := ρ) m v = cpt ρ (((σ m : PadicAlgCl p) : ℂ_[p]) ⊗ₜ ρ σ v) := by
  rw [mTensor, gal_smul_tmul, galCp_coe]

theorem smul_mTensor_of_fix (τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (hτ : ∀ m ∈ M, τ m = m)
    (m : M) (v : V) : τ • mTensor (ρ := ρ) m v = mTensor m v := by
  rw [smul_mTensor, hτ m m.2, hρ τ hτ]
  rfl

omit hρ in
theorem liftEmb_val_fix : ∀ m ∈ M, liftEmb M (IntermediateField.val M) m = m := by
  intro m hm
  exact liftEmb_apply M _ ⟨m, hm⟩

variable [FiniteDimensional ℚ_[p] L] [FiniteDimensional L M]

/-- The trace `Tr(w) = ∑_e σ_e w`. -/
def galTrace (w : CpTensor ρ) : CpTensor ρ := ∑ e : M →ₐ[L] PadicAlgCl p, liftEmb M e • w

theorem trace_mem_DHT (m : M) (v : V) : galTrace (M := M) (mTensor (ρ := ρ) m v) ∈ DHT ρ 0 := by
  rw [mem_DHT]
  intro σ
  rw [(htSetup L).ψ_zero σ, one_smul, galTrace, Finset.smul_sum]
  -- `σ σ_e` and `σ_{σ ∘ e}` agree on `M`
  let f : (M →ₐ[L] PadicAlgCl p) ≃ (M →ₐ[L] PadicAlgCl p) :=
    { toFun := fun e => (σ : PadicAlgCl p →ₐ[L] PadicAlgCl p).comp e
      invFun := fun e => (σ.symm : PadicAlgCl p →ₐ[L] PadicAlgCl p).comp e
      left_inv := fun e => by ext; simp
      right_inv := fun e => by ext; simp }
  have key : ∀ e, σ • liftEmb M e • mTensor (ρ := ρ) m v = liftEmb M (f e) • mTensor m v := by
    intro e
    set τ := (liftEmb M (f e))⁻¹ * σ * liftEmb M e
    have hτ : ∀ x ∈ M, τ x = x := by
      intro x hx
      change (liftEmb M (f e)).symm (σ (liftEmb M e x)) = x
      rw [AlgEquiv.symm_apply_eq]
      have h1 := liftEmb_apply M e ⟨x, hx⟩
      have h2 := liftEmb_apply M (f e) ⟨x, hx⟩
      simp only at h1 h2
      rw [h1, h2]
      rfl
    have : σ * liftEmb M e = liftEmb M (f e) * τ := by
      simp only [τ, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [← mul_smul, this, mul_smul, smul_mTensor_of_fix hρ τ hτ]
  simp_rw [key]
  exact Equiv.sum_comp f (fun e => liftEmb M e • mTensor (ρ := ρ) m v)

omit hρ [FiniteDimensional ℚ_[p] L] in
theorem trace_eq_sum (m : M) (v : V) :
    galTrace (M := M) (mTensor (ρ := ρ) m v) =
      ∑ e : M →ₐ[L] PadicAlgCl p, (((e m : PadicAlgCl p) : ℂ_[p])) •
        cpt ρ ((1 : ℂ_[p]) ⊗ₜ ρ (liftEmb M e) v) := by
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [smul_mTensor, liftEmb_apply, cpt_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

omit hρ [FiniteDimensional ℚ_[p] L] [FiniteDimensional L M] in
/-- Dedekind: the rows `(e(m_j))_j` of the embeddings are linearly independent. -/
theorem linearIndependent_emb {ι : Type*} [Finite ι] (b : Basis ι L M) :
    LinearIndependent (PadicAlgCl p)
      (fun e : M →ₐ[L] PadicAlgCl p => fun j => e (b j)) := by
  classical
  have := Fintype.ofFinite ι
  rw [linearIndependent_iff']
  intro s g hg e0 he0
  have hval : ∀ m : M, ∑ e ∈ s, g e * e m = 0 := by
    intro m
    have hi : ∀ j, ∑ e ∈ s, g e * e (b j) = 0 := fun j => by
      have := congrFun hg j
      simpa [Finset.sum_apply] using this
    conv_lhs => rw [← b.sum_repr m]
    simp only [map_sum, Algebra.smul_def, map_mul, AlgHom.commutes, Finset.mul_sum]
    simp_rw [mul_left_comm (g _)]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, hi]
  let χ : (M →ₐ[L] PadicAlgCl p) → (M →* PadicAlgCl p) := fun e => (e : M →* PadicAlgCl p)
  have hχ : Function.Injective χ := fun e e' h => AlgHom.ext fun m => DFunLike.congr_fun h m
  have hD := (linearIndependent_monoidHom M (PadicAlgCl p)).comp χ hχ
  rw [linearIndependent_iff'] at hD
  refine hD s g ?_ e0 he0
  funext m
  simpa [Finset.sum_apply, χ] using hval m

/-- `1 ⊗ v` lies in the `ℂ_p`-span of the `G_L`-invariants. -/
theorem one_tmul_mem_span (v : V) :
    cpt ρ ((1 : ℂ_[p]) ⊗ₜ v) ∈ Submodule.span ℂ_[p] (DHT ρ 0 : Set (CpTensor ρ)) := by
  classical
  let b := Module.finBasis L M
  set n := finrank L M
  have hcard : Fintype.card (M →ₐ[L] PadicAlgCl p) = Fintype.card (Fin n) := by
    rw [AlgHom.card, Fintype.card_fin]
  let eq := Fintype.equivOfCardEq hcard
  let X : Matrix (Fin n) (Fin n) (PadicAlgCl p) := fun r j => (eq.symm r) (b j)
  have hX : IsUnit X := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact (linearIndependent_emb b).comp eq.symm eq.symm.injective
  let ι : M →ₐ[L] PadicAlgCl p := IntermediateField.val M
  let c : Fin n → PadicAlgCl p := X⁻¹.mulVec (Pi.single (eq ι) 1)
  have hc : ∀ e : M →ₐ[L] PadicAlgCl p, ∑ j, e (b j) * c j = if e = ι then 1 else 0 := by
    intro e
    have h1 : X.mulVec c = Pi.single (eq ι) 1 := by
      simp only [c, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det
        X).mp hX), Matrix.one_mulVec]
    have h2 := congrFun h1 (eq e)
    simp only [Matrix.mulVec, dotProduct, X, Equiv.symm_apply_apply] at h2
    rw [h2, Pi.single_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  -- `∑_j c_j Tr(m_j ⊗ v) = 1 ⊗ ρ(σ_ι) v = 1 ⊗ v`
  have hsum : ∑ j, (((c j : PadicAlgCl p) : ℂ_[p])) •
      galTrace (M := M) (mTensor (ρ := ρ) (b j) v) = cpt ρ ((1 : ℂ_[p]) ⊗ₜ v) := by
    simp_rw [trace_eq_sum, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    rw [Finset.sum_eq_single ι]
    · have : ∑ j, ((c j : PadicAlgCl p) : ℂ_[p]) * ((ι (b j) : PadicAlgCl p) : ℂ_[p]) = 1 := by
        have := hc ι
        rw [if_pos rfl] at this
        rw [← map_one (algebraMap (PadicAlgCl p) ℂ_[p]), ← this, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, mul_comm]
        rfl
      rw [this, one_smul, hρ _ (liftEmb_val_fix (M := M))]
      rfl
    · intro e _ he
      have : ∑ j, ((c j : PadicAlgCl p) : ℂ_[p]) * ((e (b j) : PadicAlgCl p) : ℂ_[p]) = 0 := by
        have := hc e
        rw [if_neg he] at this
        rw [← map_zero (algebraMap (PadicAlgCl p) ℂ_[p]), ← this, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, mul_comm]
        rfl
      rw [this, zero_smul]
    · simp
  rw [← hsum]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact trace_mem_DHT hρ (b j) v

/-- **The `G_L`-invariants of `ℂ_p ⊗ V` have dimension `dim V`** if `ρ` is trivial on `G_M`. -/
theorem finrank_DHT_zero_of_trivial_on [FiniteDimensional ℚ_[p] V] :
    finrank L (DHT ρ 0) = finrank ℚ_[p] V := by
  classical
  let B := Module.finBasis L (DHT ρ 0)
  let f : Fin (finrank L (DHT ρ 0)) → CpTensor ρ := fun i => (B i : CpTensor ρ)
  have hli : LinearIndependent ℂ_[p] f :=
    SerreTate.linearIndependent_of_eigen_single (htSetup L) (smul_distrib_cpTensor ρ) 0 f
      (fun i => (B i).2) (B.linearIndependent.map' (DHT ρ 0).subtype (Submodule.ker_subtype _))
  have hD : (DHT ρ 0 : Set (CpTensor ρ)) ⊆ Submodule.span ℂ_[p] (Set.range f) := by
    intro x hx
    have h1 : (⟨x, hx⟩ : DHT ρ 0) ∈ Submodule.span L (Set.range B) := by
      rw [B.span_eq]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (DHT ρ 0).subtype h1
    rw [← Set.range_comp] at h2
    exact Submodule.span_le_restrictScalars L ℂ_[p] _ h2
  have hspan : ⊤ ≤ Submodule.span ℂ_[p] (Set.range f) := by
    intro w _
    have hw : ∀ w : ℂ_[p] ⊗[ℚ_[p]] V, cpt ρ w ∈ Submodule.span ℂ_[p] (Set.range f) := by
      intro w
      induction w with
      | zero => exact Submodule.zero_mem _
      | tmul c v =>
        have h1 : cpt ρ (c ⊗ₜ v) = c • cpt ρ ((1 : ℂ_[p]) ⊗ₜ v) := by
          rw [cpt_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h1]
        refine Submodule.smul_mem _ _ ?_
        exact Submodule.span_le.mpr hD (one_tmul_mem_span hρ v)
      | add x y hx hy => exact Submodule.add_mem _ hx hy
    exact hw w
  have := Module.finrank_eq_card_basis (Basis.mk hli hspan)
  rw [Fintype.card_fin, finrank_cpTensor] at this
  exact this.symm

/-- **A representation with finite image is Hodge–Tate.** -/
theorem isHodgeTate_of_trivial_on [FiniteDimensional ℚ_[p] V] : IsHodgeTate ρ := by
  classical
  refine le_antisymm (htDim_le ρ) ?_
  set S := (finite_support_DHT ρ).toFinset ∪ {0}
  rw [htDim_eq_sum ρ (S := S) (fun q hq => Finset.mem_union_left _ (by simpa using hq))]
  calc finrank ℚ_[p] V = finrank L (DHT ρ 0) := (finrank_DHT_zero_of_trivial_on hρ).symm
    _ ≤ ∑ q ∈ S, finrank L (DHT ρ q) :=
      Finset.single_le_sum (f := fun q => finrank L (DHT ρ q)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_union_right _ (Finset.mem_singleton_self 0))

/-- **All Hodge–Tate weights of a representation with finite image are `0`.** -/
theorem count_htWeights_zero_of_trivial_on [FiniteDimensional ℚ_[p] V] :
    (htWeights ρ).count 0 = finrank ℚ_[p] V ∧
      Multiset.card (htWeights ρ) = finrank ℚ_[p] V := by
  refine ⟨by rw [count_htWeights, finrank_DHT_zero_of_trivial_on hρ], ?_⟩
  exact (isHodgeTate_iff_card_htWeights ρ).mp (isHodgeTate_of_trivial_on hρ)

end PadicHodge
