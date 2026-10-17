/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.HodgeTate.SerreTate
import PadicHodge.TateSen.Twist
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RepresentationTheory.Basic

/-!
# Hodge–Tate representations

Let `L / ℚ_p` be finite (inside `ℚ̄_p`) and `ρ : G_L → GL(V)` a representation on a
finite-dimensional `ℚ_p`-vector space. On `W = ℂ_p ⊗_{ℚ_p} V` the group `G_L` acts
semilinearly by `σ (c ⊗ v) = σ(c) ⊗ ρ(σ) v`. For `q ∈ ℤ` let
`D_q(V) = {w ∈ W | σ w = χ(σ)^{-q} w}` (an `L`-vector space; this is `W[q]` of
[BC, Remark 2.3.2], isomorphic to `W{q} = (W(q))^{G_L}` and to `D_HT^q(V) = (V ⊗ ℂ_p(q))^{G_L}`).

* `sum_finrank_DHT_le`: `∑_{q ∈ S} dim_L D_q(V) ≤ dim_{ℚ_p} V` (Serre–Tate, [BC, Lemma 2.3.1],
  using Tate's theorem `ℂ_p(j)^{G_L} = 0`, `j ≠ 0`, and Ax–Sen–Tate `ℂ_p^{G_L} = L`);
* `IsHodgeTate ρ`: equality `∑_q dim_L D_q(V) = dim_{ℚ_p} V` ([BC, Def. 2.3.4]);
* `isHodgeTate_of_exact`: in a short exact sequence `0 → V' → V → V'' → 0` of representations
  with `V` Hodge–Tate, `V'` and `V''` are Hodge–Tate ([BC, Prop. 2.4.4]; the case of quotients
  is quoted in [LocAn], Introduction).
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- `G_L` acts on `ℂ_p`. -/
instance galCpAction : MulSemiringAction (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) ℂ_[p] :=
  MulSemiringAction.compHom ℂ_[p] (galCp L)

theorem gal_smul_cp (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (c : ℂ_[p]) :
    σ • c = galCp L σ c := rfl

theorem algebraMap_L_cp (a : L) : algebraMap L ℂ_[p] a = ((a : PadicAlgCl p) : ℂ_[p]) := rfl

theorem algebraMap_L_cp_algebraMap (t : ℚ_[p]) :
    algebraMap L ℂ_[p] (algebraMap ℚ_[p] L t) = algebraMap ℚ_[p] ℂ_[p] t := by
  rw [algebraMap_L_cp, IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]
  rfl

theorem chiL_add (a b : ℤ) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) :
    chiL L (a + b) σ = chiL L a σ * chiL L b σ := by
  simp only [chiL, chiPow, MonoidHom.comp_apply, zpowGroupHom_apply, zpow_add, map_mul,
    Units.val_mul]

theorem chiL_zero (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) : chiL L 0 σ = 1 := by
  simp [chiL, chiPow]

section Tensor

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- `galCp L σ` as a `ℚ_p`-linear map. -/
def galCpLin (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] where
  toFun := galCp L σ
  map_add' := map_add _
  map_smul' := galCp_smul σ

theorem galCpLin_apply (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (c : ℂ_[p]) :
    galCpLin L σ c = galCp L σ c := rfl

variable {L}

theorem map_galCpLin_smul (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (f : V →ₗ[ℚ_[p]] V) (c : ℂ_[p])
    (w : ℂ_[p] ⊗[ℚ_[p]] V) :
    TensorProduct.map (galCpLin L σ) f (c • w) =
      galCp L σ c • TensorProduct.map (galCpLin L σ) f w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c' v =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      galCpLin_apply, galCpLin_apply, smul_eq_mul, map_mul, TensorProduct.smul_tmul',
      smul_eq_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `ℂ_p ⊗_{ℚ_p} V` for a representation `ρ` of `G_L` on `V` (a type synonym carrying the
semilinear `G_L`-action). -/
@[nolint unusedArguments]
def CpTensor (_ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V) : Type _ :=
  ℂ_[p] ⊗[ℚ_[p]] V

variable (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V)

instance : AddCommGroup (CpTensor ρ) := inferInstanceAs (AddCommGroup (ℂ_[p] ⊗[ℚ_[p]] V))
instance : Module ℂ_[p] (CpTensor ρ) := inferInstanceAs (Module ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V))
instance : Module L (CpTensor ρ) := Module.compHom (CpTensor ρ) (algebraMap L ℂ_[p])

instance : IsScalarTower L ℂ_[p] (CpTensor ρ) where
  smul_assoc a c w := by
    rw [Algebra.smul_def, mul_smul]
    rfl

/-- The semilinear action `σ (c ⊗ v) = σ(c) ⊗ ρ(σ) v`, as a monoid hom to `ℚ_p`-endomorphisms. -/
def tensorAct : (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) →* Module.End ℚ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) where
  toFun σ := TensorProduct.map (galCpLin L σ) (ρ σ)
  map_one' := by
    have h1 : galCpLin L (1 : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) = LinearMap.id := by
      ext c; rw [galCpLin_apply, map_one]; rfl
    rw [h1, map_one]
    exact TensorProduct.map_id
  map_mul' σ τ := by
    have h1 : galCpLin L (σ * τ) = galCpLin L σ * galCpLin L τ := by
      ext c; rw [galCpLin_apply, map_mul]; rfl
    rw [h1, map_mul]
    exact TensorProduct.map_mul _ _ _ _

instance : DistribMulAction (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (CpTensor ρ) :=
  DistribMulAction.compHom (ℂ_[p] ⊗[ℚ_[p]] V) (tensorAct ρ)

theorem gal_smul_cpTensor (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (w : CpTensor ρ) :
    σ • w = (TensorProduct.map (galCpLin L σ) (ρ σ) w : ℂ_[p] ⊗[ℚ_[p]] V) := rfl

theorem smul_distrib_cpTensor (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (c : ℂ_[p])
    (w : CpTensor ρ) : σ • c • w = (σ • c) • (σ • w) :=
  map_galCpLin_smul σ (ρ σ) c w

instance [FiniteDimensional ℚ_[p] V] : FiniteDimensional ℂ_[p] (CpTensor ρ) :=
  inferInstanceAs (FiniteDimensional ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V))

theorem finrank_cpTensor [FiniteDimensional ℚ_[p] V] :
    finrank ℂ_[p] (CpTensor ρ) = finrank ℚ_[p] V :=
  Module.finrank_baseChange

end Tensor

section Setup

variable [FiniteDimensional ℚ_[p] L]

/-- The Serre–Tate setup for `G_L` acting on `ℂ_p`, with `ψ_q = χ^{-q}`. -/
def htSetup : SerreTate.Setup (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) ℂ_[p] L where
  ψ q σ := algebraMap ℚ_[p] L (chiL L (-q) σ)
  ψ_add a b σ := by rw [neg_add, chiL_add, map_mul]
  ψ_zero σ := by rw [neg_zero, chiL_zero, map_one]
  fixed_iff c := by
    change (∀ g, galCp L g c = c) ↔ _
    rw [galCp_eq_self_iff_mem, mem_cpSubmodule]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, a.2, rfl⟩
  tate q hq c hc := by
    refine eq_zero_of_galCp_eq_chi_smul (L := L) (j := -q) (neg_ne_zero.mpr hq) fun σ => ?_
    have h := hc σ
    change galCp L σ c = _ at h
    rw [h, algebraMap_L_cp_algebraMap, ← Algebra.smul_def]
    rfl

end Setup

section HT

variable {L} [FiniteDimensional ℚ_[p] L] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V)

/-- `D_q(V) = {w ∈ ℂ_p ⊗ V | σ w = χ(σ)^{-q} w}`, an `L`-subspace. -/
def DHT (q : ℤ) : Submodule L (CpTensor ρ) :=
  SerreTate.eigen (htSetup L) (CpTensor ρ) (smul_distrib_cpTensor ρ) q

theorem mem_DHT {q : ℤ} {w : CpTensor ρ} :
    w ∈ DHT ρ q ↔ ∀ σ, σ • w = (htSetup L).ψ q σ • w := Iff.rfl

variable [FiniteDimensional ℚ_[p] V]

instance (q : ℤ) : FiniteDimensional L (DHT ρ q) :=
  SerreTate.finiteDimensional_eigen (htSetup L) (smul_distrib_cpTensor ρ) q

/-- **Serre–Tate** for `ℂ_p ⊗ V`: `∑_{q ∈ S} dim_L D_q(V) ≤ dim_{ℚ_p} V`. -/
theorem sum_finrank_DHT_le (S : Finset ℤ) :
    ∑ q ∈ S, finrank L (DHT ρ q) ≤ finrank ℚ_[p] V := by
  rw [← finrank_cpTensor ρ]
  exact SerreTate.sum_finrank_le (htSetup L) (smul_distrib_cpTensor ρ) S

theorem finite_support_DHT : (Function.support fun q => finrank L (DHT ρ q)).Finite := by
  by_contra h
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq h (finrank ℚ_[p] V + 1)
  have h1 := sum_finrank_DHT_le ρ S
  have h2 : S.card ≤ ∑ q ∈ S, finrank L (DHT ρ q) := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun q hq => ?_
    have := hS hq
    rw [Function.mem_support] at this
    omega
  omega

/-- The total Hodge–Tate dimension `∑_q dim_L D_q(V)`. -/
def htDim : ℕ := ∑ᶠ q, finrank L (DHT ρ q)

omit [FiniteDimensional ℚ_[p] V] in
theorem htDim_eq_sum {S : Finset ℤ}
    (hS : Function.support (fun q => finrank L (DHT ρ q)) ⊆ S) :
    htDim ρ = ∑ q ∈ S, finrank L (DHT ρ q) :=
  finsum_eq_sum_of_support_subset _ hS

theorem htDim_le : htDim ρ ≤ finrank ℚ_[p] V := by
  rw [htDim_eq_sum ρ (S := (finite_support_DHT ρ).toFinset) (by simp)]
  exact sum_finrank_DHT_le ρ _

/-- `V` is **Hodge–Tate** if `∑_q dim_L D_q(V) = dim_{ℚ_p} V` ([BC, Def. 2.3.4]). -/
def IsHodgeTate : Prop := htDim ρ = finrank ℚ_[p] V

end HT

section Functoriality

variable {L} {V V' : Type*} [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup V'] [Module ℚ_[p] V']
  {ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V}
  {ρ' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V'}

/-- The map `ℂ_p ⊗ V → ℂ_p ⊗ V'` induced by a `ℚ_p`-linear map. -/
def tensorMap (f : V →ₗ[ℚ_[p]] V') : CpTensor ρ → CpTensor ρ' :=
  fun w => (f.lTensor ℂ_[p] : ℂ_[p] ⊗[ℚ_[p]] V → ℂ_[p] ⊗[ℚ_[p]] V') w

theorem tensorMap_add (f : V →ₗ[ℚ_[p]] V') (w w' : CpTensor ρ) :
    tensorMap (ρ' := ρ') f (w + w') = tensorMap f w + tensorMap f w' :=
  map_add (f.lTensor ℂ_[p]) w w'

theorem lTensor_cp_smul (f : V →ₗ[ℚ_[p]] V') (c : ℂ_[p]) (w : ℂ_[p] ⊗[ℚ_[p]] V) :
    f.lTensor ℂ_[p] (c • w) = c • f.lTensor ℂ_[p] w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul c' v => rw [TensorProduct.smul_tmul', LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem tensorMap_smul (f : V →ₗ[ℚ_[p]] V') (c : ℂ_[p]) (w : CpTensor ρ) :
    tensorMap (ρ' := ρ') f (c • w) = c • tensorMap f w :=
  lTensor_cp_smul f c w

theorem tensorMap_smulL (f : V →ₗ[ℚ_[p]] V') (a : L) (w : CpTensor ρ) :
    tensorMap (ρ' := ρ') f (a • w) = a • tensorMap f w :=
  tensorMap_smul f (algebraMap L ℂ_[p] a) w

theorem tensorMap_gal (f : V →ₗ[ℚ_[p]] V') (hf : ∀ σ, f ∘ₗ ρ σ = ρ' σ ∘ₗ f)
    (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (w : CpTensor ρ) :
    tensorMap (ρ' := ρ') f (σ • w) = σ • tensorMap f w := by
  change f.lTensor ℂ_[p] (TensorProduct.map (galCpLin L σ) (ρ σ) w) =
    TensorProduct.map (galCpLin L σ) (ρ' σ) (f.lTensor ℂ_[p] w)
  induction (w : ℂ_[p] ⊗[ℚ_[p]] V) using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.map_tmul]
    congr 1
    exact LinearMap.congr_fun (hf σ) v
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem tensorMap_injective {f : V →ₗ[ℚ_[p]] V'} (hf : Function.Injective f) :
    Function.Injective (tensorMap (ρ := ρ) (ρ' := ρ') f) :=
  Module.Flat.lTensor_preserves_injective_linearMap f hf

variable [FiniteDimensional ℚ_[p] L]

theorem tensorMap_mem_DHT (f : V →ₗ[ℚ_[p]] V') (hf : ∀ σ, f ∘ₗ ρ σ = ρ' σ ∘ₗ f) {q : ℤ}
    {w : CpTensor ρ} (hw : w ∈ DHT ρ q) : tensorMap (ρ' := ρ') f w ∈ DHT ρ' q := by
  intro σ
  rw [← tensorMap_gal f hf, hw σ, tensorMap_smulL]

/-- The `L`-linear map `D_q(V) → D_q(V')` induced by an intertwining map `V → V'`. -/
def DHTmap (f : V →ₗ[ℚ_[p]] V') (hf : ∀ σ, f ∘ₗ ρ σ = ρ' σ ∘ₗ f) (q : ℤ) :
    DHT ρ q →ₗ[L] DHT ρ' q where
  toFun w := ⟨tensorMap f w, tensorMap_mem_DHT f hf w.2⟩
  map_add' w w' := Subtype.ext (tensorMap_add f (w : CpTensor ρ) w')
  map_smul' a w := Subtype.ext (tensorMap_smulL f a (w : CpTensor ρ))

theorem DHTmap_apply (f : V →ₗ[ℚ_[p]] V') (hf : ∀ σ, f ∘ₗ ρ σ = ρ' σ ∘ₗ f) (q : ℤ)
    (w : DHT ρ q) : ((DHTmap f hf q w : DHT ρ' q) : CpTensor ρ') = tensorMap f (w : CpTensor ρ) :=
  rfl

end Functoriality

section Exact

variable {L} [FiniteDimensional ℚ_[p] L]
  {V' V V'' : Type*} [AddCommGroup V'] [Module ℚ_[p] V'] [AddCommGroup V] [Module ℚ_[p] V]
  [AddCommGroup V''] [Module ℚ_[p] V'']
  {ρ' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V'}
  {ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V}
  {ρ'' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V''}
  {f : V' →ₗ[ℚ_[p]] V} {g : V →ₗ[ℚ_[p]] V''}
  (hf : ∀ σ, f ∘ₗ ρ' σ = ρ σ ∘ₗ f) (hg : ∀ σ, g ∘ₗ ρ σ = ρ'' σ ∘ₗ g)
  (hfi : Function.Injective f) (hgs : Function.Surjective g) (hfg : Function.Exact f g)
include hf hg hfi hgs hfg

omit hgs in
/-- `0 → D_q(V') → D_q(V) → D_q(V'')` is exact, hence
`dim D_q(V) ≤ dim D_q(V') + dim D_q(V'')`. -/
theorem finrank_DHT_le_add [FiniteDimensional ℚ_[p] V'] [FiniteDimensional ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V''] (q : ℤ) :
    finrank L (DHT ρ q) ≤ finrank L (DHT ρ' q) + finrank L (DHT ρ'' q) := by
  let G := DHTmap (ρ := ρ) (ρ' := ρ'') g hg q
  let F := DHTmap (ρ := ρ') (ρ' := ρ) f hf q
  have hex : Function.Exact (f.lTensor ℂ_[p]) (g.lTensor ℂ_[p]) :=
    Module.Flat.lTensor_exact ℂ_[p] hfg
  have hker : LinearMap.ker G ≤ LinearMap.range F := by
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have hw' : g.lTensor ℂ_[p] ((w : CpTensor ρ) : ℂ_[p] ⊗[ℚ_[p]] V) = 0 := by
      have := congrArg Subtype.val hw
      rw [DHTmap_apply] at this
      exact this
    obtain ⟨w', hw'⟩ := (hex _).mp hw'
    have e : tensorMap (ρ := ρ') (ρ' := ρ) f (w' : CpTensor ρ') = (w : CpTensor ρ) := hw'
    have hmem : (w' : CpTensor ρ') ∈ DHT ρ' q := by
      intro σ
      apply tensorMap_injective (ρ := ρ') (ρ' := ρ) hfi
      rw [tensorMap_gal f hf, tensorMap_smulL, e]
      exact w.2 σ
    exact ⟨⟨w', hmem⟩, Subtype.ext (by rw [DHTmap_apply]; exact e)⟩
  have hFi : Function.Injective F := fun a b h => by
    have h' := congrArg Subtype.val h
    simp only [F, DHTmap_apply] at h'
    exact Subtype.ext (tensorMap_injective (ρ := ρ') (ρ' := ρ) hfi h')
  have h1 := LinearMap.finrank_range_add_finrank_ker G
  have h2 : finrank L (LinearMap.range G) ≤ finrank L (DHT ρ'' q) :=
    Submodule.finrank_le _
  have h3 : finrank L (LinearMap.ker G) ≤ finrank L (LinearMap.range F) :=
    Submodule.finrank_mono hker
  have h4 : finrank L (LinearMap.range F) = finrank L (DHT ρ' q) :=
    LinearMap.finrank_range_of_inj hFi
  omega

/-- **Sub- and quotient representations of Hodge–Tate representations are Hodge–Tate**
([BC, Prop. 2.4.4]). -/
theorem isHodgeTate_of_exact [FiniteDimensional ℚ_[p] V'] [FiniteDimensional ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V''] (h : IsHodgeTate ρ) : IsHodgeTate ρ' ∧ IsHodgeTate ρ'' := by
  classical
  set S := (finite_support_DHT ρ').toFinset ∪ (finite_support_DHT ρ).toFinset ∪
    (finite_support_DHT ρ'').toFinset with hS
  have hS' : Function.support (fun q => finrank L (DHT ρ' q)) ⊆ S := by
    intro q hq; simp [hS, hq]
  have hSV : Function.support (fun q => finrank L (DHT ρ q)) ⊆ S := by
    intro q hq; simp [hS, hq]
  have hS'' : Function.support (fun q => finrank L (DHT ρ'' q)) ⊆ S := by
    intro q hq; simp [hS, hq]
  have hdim : finrank ℚ_[p] V = finrank ℚ_[p] V' + finrank ℚ_[p] V'' := by
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [LinearMap.range_eq_top.mpr hgs, finrank_top] at h1
    have h2 : LinearMap.ker g = LinearMap.range f := (LinearMap.exact_iff.mp hfg)
    rw [h2, LinearMap.finrank_range_of_inj hfi] at h1
    omega
  have hsum : ∑ q ∈ S, finrank L (DHT ρ q) ≤
      ∑ q ∈ S, finrank L (DHT ρ' q) + ∑ q ∈ S, finrank L (DHT ρ'' q) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun q _ => finrank_DHT_le_add hf hg hfi hfg q
  have e := htDim_eq_sum ρ hSV
  have e' := htDim_eq_sum ρ' hS'
  have e'' := htDim_eq_sum ρ'' hS''
  have b' := sum_finrank_DHT_le ρ' S
  have b'' := sum_finrank_DHT_le ρ'' S
  unfold IsHodgeTate at h ⊢
  constructor <;> omega

end Exact

section Decomposition

variable {L} [FiniteDimensional ℚ_[p] L] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  [FiniteDimensional ℚ_[p] V] (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V)

/-- **Hodge–Tate decomposition** ([BC, Lemma 2.3.1 and Example 2.3.5]): `V` is Hodge–Tate iff
`ℂ_p ⊗ V` has a `ℂ_p`-basis of vectors `w_i` with `σ w_i = χ(σ)^{-q_i} w_i`, i.e.
`ℂ_p ⊗ V ≅ ⊕_i ℂ_p(-q_i)`. -/
theorem isHodgeTate_iff_exists_basis :
    IsHodgeTate ρ ↔ ∃ (ι : Type) (_ : Fintype ι) (b : Basis ι ℂ_[p] (CpTensor ρ)) (q : ι → ℤ),
      ∀ i, b i ∈ DHT ρ (q i) := by
  classical
  constructor
  · intro h
    set S := (finite_support_DHT ρ).toFinset
    have hS := htDim_eq_sum ρ (S := S) (by simp [S])
    have heq : ∑ q ∈ S, finrank L (DHT ρ q) = finrank ℂ_[p] (CpTensor ρ) := by
      rw [finrank_cpTensor, ← hS]; exact h
    obtain ⟨ι, hι, b, q, -, hb⟩ :=
      SerreTate.exists_eigenbasis (htSetup L) (smul_distrib_cpTensor ρ) S heq
    exact ⟨ι, hι, b, q, hb⟩
  · rintro ⟨ι, hι, b, q, hb⟩
    set S := Finset.univ.image q ∪ (finite_support_DHT ρ).toFinset
    have h1 := SerreTate.sum_finrank_eq_of_eigenbasis (htSetup L) (smul_distrib_cpTensor ρ) b q hb S
      (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem q (Finset.mem_univ i)))
    have hS := htDim_eq_sum ρ (S := S) (fun q hq => Finset.mem_union_right _ (by simpa using hq))
    unfold IsHodgeTate
    rw [hS, ← finrank_cpTensor ρ]
    exact h1

end Decomposition

section Hom

variable {L} [FiniteDimensional ℚ_[p] L]

/-- There are no nonzero `G_L`-equivariant `ℂ_p`-linear maps `ℂ_p(a) → ℂ_p(b)` for `a ≠ b`
([BC, discussion after Thm. 2.2.7]): such a map is multiplication by `λ = f(1)`, and
`σ(λ) = χ(σ)^{a-b} λ` forces `λ = 0` by Tate's theorem. -/
theorem eq_zero_of_twist_equivariant {a b : ℤ} (hab : a ≠ b) (f : ℂ_[p] →ₗ[ℂ_[p]] ℂ_[p])
    (hf : ∀ σ x, f (cpTwistRep L a σ x) = cpTwistRep L b σ (f x)) : f = 0 := by
  have hlam : f 1 = 0 := by
    refine eq_zero_of_galCp_eq_chi_smul (L := L) (j := a - b) (sub_ne_zero.mpr hab) fun σ => ?_
    have h := hf σ 1
    rw [cpTwistRep_apply, cpTwistRep_apply, map_one] at h
    have h' : f (chiL L a σ • (1 : ℂ_[p])) = chiL L a σ • f 1 := by
      rw [← algebraMap_smul ℂ_[p] (chiL L a σ) (1 : ℂ_[p]), map_smul, algebraMap_smul]
    rw [h'] at h
    -- `χ^a • f 1 = χ^b • σ(f 1)`
    have hb0 : chiL L b σ ≠ 0 := Units.ne_zero _
    have e : galCp L σ (f 1) = (chiL L b σ)⁻¹ • chiL L a σ • f 1 := by
      rw [h, smul_smul, inv_mul_cancel₀ hb0, one_smul]
    rw [e, smul_smul]
    congr 1
    simp only [chiL, chiPow, MonoidHom.comp_apply, zpowGroupHom_apply]
    rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, ← map_inv, ← map_mul, zpow_sub, mul_comm]
  exact LinearMap.ext_ring hlam

end Hom

end PadicHodge
