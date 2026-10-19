/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.HodgeTate.Dual
import PadicHodge.HodgeTate.Orthogonal
import PadicHodge.FormalGroup.DAlphaHT
import PadicHodge.HodgeTate.Splitting

/-!
# `Hom_{ℤ_p}(T, ℂ_p)` for a `ℤ_p`-lattice `T` with a `G_L`-action

Generic set-up for (FoInt) ([Fo, §5.7]): `T` is a free `ℤ_p`-module of finite rank with a
`ℤ_p`-linear action `act` of `G_L = Gal(ℚ̄_p/L)` (e.g. `T = T_p H(ℚ̄_p)` for a `p`-divisible group
`H` over `L`), `V = ℚ_p ⊗ T` the associated representation (`HomRep.repQ`), and
`W = Hom_{ℤ_p}(T, ℂ_p)` with the semilinear action `(τ f)(x) = τ(f(τ⁻¹ x))` (`HomRep.HomT`).

* `PhiA`/`PhiAL`: `ℂ_p ⊗ (ℚ_p ⊗ A)^∨ → Hom_{ℤ_p}(A, ℂ_p)`, `w ↦ (a ↦ w(1 ⊗ 1 ⊗ a))`,
  injective (`PhiAL_injective`), bijective for `A` free of finite rank (`PhiAL_bijective`);
* `HomRep.PhiAL_gal`: it is `G_L`-equivariant, hence (`HomRep.mem_E_iff`) it identifies
  `D_q(V^∨)` with the `ψ_q`-eigenspace `E q` of `W` (`ψ_q = χ^{-q}`), `finrank_E`;
* `HomRep.PhiAL_comp`: compatibility with `ℤ_p`-linear maps `T' → T` (restriction of linear forms
  is the transpose);
* `HomRep.mem_E_zero_iff`, `HomRep.mem_E_one_iff`: `E 0` = the `G_L`-equivariant maps,
  `E 1` = the maps `f` with `f(σ x) = χ(σ) σ(f x)` (`ℂ_p(1)` trivialised);
* **`HomRep.eq_zero_of_isTwist`**: if `E 0` has `L`-dimension `≥ rank T` (e.g. `V` Hodge–Tate of
  weight `0`), every `f` with `f(σ x) = χ(σ)^j σ(f x)` for `σ ∈ G_{L'}`, `j ≠ 0`, `L ⊆ L'`
  finite, is zero (Tate's `ℂ_p(j)^{G_{L'}} = 0`);
* **`HomRep.exists_lattice`** (the lattice lemma, [Fo, §5.9] in the weak form needed by
  (FoInt)(c)): for `ℂ_p`-linearly independent `ρ_1, …, ρ_d ∈ W` and a complement `V₁` of their
  span, `p^c M ⊆ p^N ρ(O_{ℂ_p}^d) + V₁` for `M = Hom_{ℤ_p}(T, O_{ℂ_p})`, any `N` with `p^N ρ`
  integral; `HomRep.exists_pow_norm_le` provides such an `N`.
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

section GenericDual

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]

theorem dualEquiv_qsmul {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
    (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] V) (q : ℚ_[p]) (y : ℂ_[p] ⊗[ℚ_[p]] V) :
    dualEquiv (V := V) w (q • y) = algebraMap ℚ_[p] ℂ_[p] q * dualEquiv (V := V) w y := by
  rw [← algebraMap_smul ℂ_[p] q y, map_smul, smul_eq_mul]

variable (p) in
/-- `a ↦ 1 ⊗ 1 ⊗ a ∈ ℂ_p ⊗ (ℚ_p ⊗ A)`. -/
def yA (a : A) : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] A) := (1 : ℂ_[p]) ⊗ₜ ((1 : ℚ_[p]) ⊗ₜ a)

theorem yA_add (a b : A) : yA p (a + b) = yA p a + yA p b := by
  simp only [yA, tmul_add]

theorem yA_smul (c : ℤ_[p]) (a : A) :
    yA p (c • a) = (algebraMap ℤ_[p] ℚ_[p] c) • yA p a := by
  rw [yA, yA, tmul_smul, ← algebraMap_smul ℚ_[p] c ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] a), tmul_smul]

variable [Module.Finite ℤ_[p] A]

/-- `w ↦ (a ↦ w(1 ⊗ 1 ⊗ a))`, `ℂ_p ⊗ (ℚ_p ⊗ A)^∨ → Hom_{ℤ_p}(A, ℂ_p)`. -/
def PhiA (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] A)) : A →ₗ[ℤ_[p]] ℂ_[p] where
  toFun a := dualEquiv w (yA p a)
  map_add' a b := by rw [yA_add, map_add]
  map_smul' c a := by
    rw [yA_smul, dualEquiv_qsmul, RingHom.id_apply, Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] ℂ_[p]]

/-- `ℂ_p ⊗ (ℚ_p ⊗ A)^∨ → Hom_{ℤ_p}(A, ℂ_p)`, `ℂ_p`-linear. -/
def PhiAL : (ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] A)) →ₗ[ℂ_[p]] (A →ₗ[ℤ_[p]] ℂ_[p]) where
  toFun := PhiA
  map_add' w w' := LinearMap.ext fun a => by
    change dualEquiv (w + w') _ = dualEquiv w _ + dualEquiv w' _
    rw [map_add, LinearMap.add_apply]
  map_smul' c w := LinearMap.ext fun a => by
    change dualEquiv (c • w) _ = c • dualEquiv w _
    rw [map_smul, LinearMap.smul_apply]

theorem PhiAL_apply (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] A)) (a : A) :
    PhiAL w a = dualEquiv w (yA p a) := rfl

theorem PhiAL_injective :
    Function.Injective (PhiAL : (ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] A)) →ₗ[ℂ_[p]] _) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have h1 : ∀ a : A, dualEquiv w ((1 : ℂ_[p]) ⊗ₜ ((1 : ℚ_[p]) ⊗ₜ a)) = 0 := fun a =>
    LinearMap.congr_fun hw a
  have h2 : ∀ v : ℚ_[p] ⊗[ℤ_[p]] A, dualEquiv w ((1 : ℂ_[p]) ⊗ₜ v) = 0 := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => rw [tmul_zero, map_zero]
    | tmul q a =>
      have : (q ⊗ₜ[ℤ_[p]] a : ℚ_[p] ⊗[ℤ_[p]] A) = q • ((1 : ℚ_[p]) ⊗ₜ a) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [this, tmul_smul, dualEquiv_qsmul, h1, mul_zero]
    | add v v' hv hv' => rw [tmul_add, map_add, hv, hv', add_zero]
  have h3 : dualEquiv w = 0 := by
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.zero_apply]
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul c v =>
      have : (c ⊗ₜ[ℚ_[p]] v : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] A)) = c • ((1 : ℂ_[p]) ⊗ₜ v) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, h2, smul_zero]
    | add y y' hy hy' => rw [map_add, hy, hy', add_zero]
  exact (LinearEquiv.map_eq_zero_iff _).mp h3

/-- **Restriction of linear forms is the transpose**: `Φ(w) ∘ u = Φ((1 ⊗ (u_{ℚ_p})^∨) w)`. -/
theorem PhiAL_comp {B : Type*} [AddCommGroup B] [Module ℤ_[p] B] [Module.Finite ℤ_[p] B]
    (u : B →ₗ[ℤ_[p]] A) (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] A)) :
    PhiAL w ∘ₗ u =
      PhiAL ((Module.Dual.transpose (R := ℚ_[p]) (u.baseChange ℚ_[p])).lTensor ℂ_[p] w) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, PhiAL_apply, PhiAL_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a φ =>
    rw [LinearMap.lTensor_tmul, yA, yA, dualEquiv_tmul_tmul, dualEquiv_tmul_tmul,
      Module.Dual.transpose_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul]
  | add w w' hw hw' => simp only [map_add, LinearMap.add_apply, hw, hw']

variable [Module.Free ℤ_[p] A]

/-- `Hom_{ℤ_p}(A, ℂ_p) ≅ ℂ_p^{rank A}` via a `ℤ_p`-basis of `A`. -/
def homEquivFun : (Fin (finrank ℤ_[p] A) → ℂ_[p]) ≃ₗ[ℂ_[p]] (A →ₗ[ℤ_[p]] ℂ_[p]) :=
  (Module.finBasis ℤ_[p] A).constr ℂ_[p]

instance : FiniteDimensional ℂ_[p] (A →ₗ[ℤ_[p]] ℂ_[p]) := Module.Finite.equiv homEquivFun

theorem finrank_hom_cp : finrank ℂ_[p] (A →ₗ[ℤ_[p]] ℂ_[p]) = finrank ℤ_[p] A := by
  rw [← (homEquivFun (p := p) (A := A)).finrank_eq, finrank_fin_fun]

theorem PhiAL_bijective :
    Function.Bijective (PhiAL : (ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] A)) →ₗ[ℂ_[p]] _) := by
  refine ⟨PhiAL_injective, ?_⟩
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [LinearMap.finrank_range_of_inj PhiAL_injective, finrank_hom_cp, Module.finrank_baseChange,
    Subspace.dual_finrank_eq, Module.finrank_baseChange]

end GenericDual

namespace HomRep

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]
  (act : Representation ℤ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) T)

local notation "K" => PadicAlgCl p

theorem galCp_mul_inv_apply (τ : K ≃ₐ[L] K) (z : ℂ_[p]) : galCp L τ (galCp L τ⁻¹ z) = z := by
  change (galCp L τ * galCp L τ⁻¹) z = z
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

theorem galCp_mul_apply (a b : K ≃ₐ[L] K) (z : ℂ_[p]) :
    galCp L (a * b) z = galCp L a (galCp L b z) := by
  rw [map_mul]; rfl

theorem act_inv_apply (σ : K ≃ₐ[L] K) (x : T) : act σ⁻¹ (act σ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem act_apply_inv (σ : K ≃ₐ[L] K) (x : T) : act σ (act σ⁻¹ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- `V = ℚ_p ⊗ T` as a representation of `G_L`. -/
def repQ : Representation ℚ_[p] (K ≃ₐ[L] K) (ℚ_[p] ⊗[ℤ_[p]] T) where
  toFun σ := (act σ).baseChange ℚ_[p]
  map_one' := by rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id]; rfl
  map_mul' σ τ := by rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]; rfl

theorem repQ_apply (σ : K ≃ₐ[L] K) : repQ act σ = (act σ).baseChange ℚ_[p] := rfl

/-- `σ ∈ G_L` as a `ℤ_p`-linear map of `ℂ_p`. -/
def galCpZp (τ : K ≃ₐ[L] K) : ℂ_[p] →ₗ[ℤ_[p]] ℂ_[p] :=
  (galCpLin L τ).restrictScalars ℤ_[p]

/-- The semilinear action `(τ f)(x) = τ(f(τ⁻¹ x))` on `Hom_{ℤ_p}(T, ℂ_p)`. -/
def gact (τ : K ≃ₐ[L] K) (f : T →ₗ[ℤ_[p]] ℂ_[p]) : T →ₗ[ℤ_[p]] ℂ_[p] :=
  galCpZp τ ∘ₗ f ∘ₗ act τ⁻¹

theorem gact_apply (τ : K ≃ₐ[L] K) (f : T →ₗ[ℤ_[p]] ℂ_[p]) (x : T) :
    gact act τ f x = galCp L τ (f (act τ⁻¹ x)) := rfl

/-- `Hom_{ℤ_p}(T, ℂ_p)` as a type carrying the semilinear `G_L`-action. -/
@[nolint unusedArguments]
def HomT (_act : Representation ℤ_[p] (K ≃ₐ[L] K) T) : Type _ := T →ₗ[ℤ_[p]] ℂ_[p]

instance : AddCommGroup (HomT act) := inferInstanceAs (AddCommGroup (T →ₗ[ℤ_[p]] ℂ_[p]))
instance : Module ℂ_[p] (HomT act) := inferInstanceAs (Module ℂ_[p] (T →ₗ[ℤ_[p]] ℂ_[p]))
instance : Module L (HomT act) := Module.compHom (HomT act) (algebraMap L ℂ_[p])

instance : IsScalarTower L ℂ_[p] (HomT act) where
  smul_assoc a c w := by
    rw [Algebra.smul_def, mul_smul]
    rfl

/-- `HomT act = Hom_{ℤ_p}(T, ℂ_p)`. -/
def toW : HomT act → (T →ₗ[ℤ_[p]] ℂ_[p]) := id

/-- `Hom_{ℤ_p}(T, ℂ_p) = HomT act`. -/
def ofW : (T →ₗ[ℤ_[p]] ℂ_[p]) → HomT act := id

instance : DistribMulAction (K ≃ₐ[L] K) (HomT act) where
  smul τ f := ofW act (gact act τ (toW act f))
  one_smul f := LinearMap.ext fun x => by
    change gact act 1 (toW act f) x = toW act f x
    rw [gact_apply, inv_one, map_one, map_one, Module.End.one_apply]
    rfl
  mul_smul a b f := LinearMap.ext fun x => by
    change gact act (a * b) (toW act f) x = gact act a (gact act b (toW act f)) x
    rw [gact_apply, gact_apply, gact_apply, mul_inv_rev, map_mul act b⁻¹ a⁻¹,
      Module.End.mul_apply, galCp_mul_apply]
  smul_zero τ := LinearMap.ext fun x => by
    change gact act τ 0 x = 0
    rw [gact_apply, LinearMap.zero_apply, map_zero]
  smul_add τ f g := LinearMap.ext fun x => by
    change gact act τ (toW act f + toW act g) x =
      gact act τ (toW act f) x + gact act τ (toW act g) x
    rw [gact_apply, gact_apply, gact_apply, LinearMap.add_apply, map_add]

theorem smul_homT (τ : K ≃ₐ[L] K) (f : HomT act) : τ • f = ofW act (gact act τ (toW act f)) :=
  rfl

theorem smul_distrib_homT (τ : K ≃ₐ[L] K) (c : ℂ_[p]) (f : HomT act) :
    τ • c • f = (τ • c) • (τ • f) := LinearMap.ext fun x => by
  change galCp L τ (c * _) = galCp L τ c * galCp L τ _
  rw [map_mul]
  rfl

variable [FiniteDimensional ℚ_[p] L]

/-- The `ψ_q`-eigenspaces of `Hom_{ℤ_p}(T, ℂ_p)` (`ψ_q = χ^{-q}`). -/
def E (q : ℤ) : Submodule L (HomT act) :=
  SerreTate.eigen (htSetup L) (HomT act) (smul_distrib_homT act) q

/-- `f : T → ℂ_p` is `G_L`-equivariant. -/
def IsEquiv (f : T →ₗ[ℤ_[p]] ℂ_[p]) : Prop :=
  ∀ (σ : K ≃ₐ[L] K) (x : T), f (act σ x) = galCp L σ (f x)

theorem mem_E_zero_iff (f : T →ₗ[ℤ_[p]] ℂ_[p]) : ofW act f ∈ E act 0 ↔ IsEquiv act f := by
  change (∀ τ, τ • ofW act f = (htSetup L).ψ 0 τ • ofW act f) ↔ _
  simp only [(htSetup L).ψ_zero, one_smul]
  constructor
  · intro h σ x
    have := LinearMap.congr_fun (h σ) (act σ x)
    change gact act σ f _ = f _ at this
    rw [gact_apply, act_inv_apply] at this
    exact this.symm
  · intro h τ
    refine LinearMap.ext fun x => ?_
    change gact act τ f x = f x
    rw [gact_apply, h]
    exact galCp_mul_inv_apply τ _

theorem mem_E_one_iff (f : T →ₗ[ℤ_[p]] ℂ_[p]) :
    ofW act f ∈ E act 1 ↔ ∀ (σ : K ≃ₐ[L] K) (x : T),
      f (act σ x) = algebraMap ℚ_[p] ℂ_[p] (chiL L 1 σ) * galCp L σ (f x) := by
  change (∀ τ, τ • ofW act f = (htSetup L).ψ 1 τ • ofW act f) ↔ _
  constructor
  · intro h σ x
    have := LinearMap.congr_fun (h σ) (act σ x)
    change gact act σ f _ = algebraMap L ℂ_[p] (algebraMap ℚ_[p] L (chiL L (-1) σ)) * f _ at this
    rw [gact_apply, act_inv_apply, algebraMap_L_cp_algebraMap] at this
    have h1 : algebraMap ℚ_[p] ℂ_[p] (chiL L 1 σ) * algebraMap ℚ_[p] ℂ_[p] (chiL L (-1) σ) = 1 := by
      rw [← map_mul, ← chiL_add, add_neg_cancel, chiL_zero, map_one]
    rw [this, ← mul_assoc, h1, one_mul]
  · intro h τ
    refine LinearMap.ext fun x => ?_
    change gact act τ f x = algebraMap L ℂ_[p] (algebraMap ℚ_[p] L (chiL L (-1) τ)) * f x
    rw [gact_apply, algebraMap_L_cp_algebraMap]
    have h2 := h τ (act τ⁻¹ x)
    rw [act_apply_inv] at h2
    have h1 : algebraMap ℚ_[p] ℂ_[p] (chiL L (-1) τ) * algebraMap ℚ_[p] ℂ_[p] (chiL L 1 τ) = 1 := by
      rw [← map_mul, ← chiL_add, neg_add_cancel, chiL_zero, map_one]
    rw [h2, ← mul_assoc, h1, one_mul]

/-! ### `ℂ_p ⊗ V^∨ ≅ Hom_{ℤ_p}(T, ℂ_p)` is equivariant -/

variable [Module.Finite ℤ_[p] T]
  {ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (ℚ_[p] ⊗[ℤ_[p]] T)}
  (hρ : ∀ σ, ρ σ = (act σ).baseChange ℚ_[p])

/-! The statements below take the rational representation `ρ` as a parameter with
`ρ σ = (act σ) ⊗ ℚ_p` (e.g. `ρ = V_p H` for `T = T_p H`, `hρ := fun _ => rfl`), so that they
apply without unifying `ρ` with `repQ act`. -/

omit [FiniteDimensional ℚ_[p] L] [Module.Finite ℤ_[p] T] in
include hρ in
theorem tensorAct_yA (σ : K ≃ₐ[L] K) (x : T) :
    TensorProduct.map (galCpLin L σ) (ρ σ) (yA p x) = yA p (act σ x) := by
  rw [yA, yA, TensorProduct.map_tmul, galCpLin_apply, map_one, hρ, LinearMap.baseChange_tmul]

omit [FiniteDimensional ℚ_[p] L] in
include hρ in
/-- **`Φ(σ w) = σ Φ(w)`.** -/
theorem PhiAL_gal (σ : K ≃ₐ[L] K)
    (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T)) :
    PhiAL (TensorProduct.map (galCpLin L σ) (ρ.dual σ) w) = gact act σ (PhiAL w) := by
  refine LinearMap.ext fun x => ?_
  rw [gact_apply, PhiAL_apply, PhiAL_apply]
  have h := dualEquiv_gal ρ σ w (yA p (act σ⁻¹ x))
  rw [tensorAct_yA act hρ, act_apply_inv] at h
  exact h

omit [FiniteDimensional ℚ_[p] L] in
theorem PhiAL_smulL (a : L) (w : CpTensor ρ.dual) :
    ofW act (PhiAL (A := T) (a • w)) = a • ofW act (PhiAL (A := T) w) := by
  change PhiAL (algebraMap L ℂ_[p] a • (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T))) =
    algebraMap L ℂ_[p] a • PhiAL (A := T) w
  exact map_smul _ _ _

include hρ in
/-- **`D_q(V^∨) ≅ E q`**: `Φ(w)` is a `ψ_q`-eigenvector iff `w ∈ D_q(V^∨)`. -/
theorem mem_E_iff (q : ℤ) (w : CpTensor ρ.dual) :
    ofW act (PhiAL (A := T) w) ∈ E act q ↔ w ∈ DHT ρ.dual q := by
  rw [mem_DHT]
  change (∀ τ, τ • ofW act (PhiAL w) = (htSetup L).ψ q τ • ofW act (PhiAL w)) ↔ _
  refine forall_congr' fun τ => ?_
  have e1 : τ • ofW act (PhiAL (A := T) w) = ofW act (PhiAL (A := T) (τ • w)) := by
    change gact act τ (PhiAL w) =
      PhiAL (TensorProduct.map (galCpLin L τ) (ρ.dual τ) w)
    exact (PhiAL_gal act hρ τ w).symm
  rw [e1, ← PhiAL_smulL]
  exact ⟨fun h => PhiAL_injective h, fun h => by rw [h]⟩

variable [Module.Free ℤ_[p] T]

/-- `D_q(V^∨) ≃ E q` as `L`-vector spaces. -/
def eEquiv (q : ℤ) : DHT ρ.dual q ≃ₗ[L] E act q :=
  LinearEquiv.ofBijective
    { toFun := fun w => ⟨ofW act (PhiAL (A := T) w.1), (mem_E_iff act hρ q w.1).mpr w.2⟩
      map_add' := fun w w' => Subtype.ext (map_add PhiAL w.1 w'.1)
      map_smul' := fun a w => by
        apply Subtype.ext
        exact PhiAL_smulL act a w.1 }
    ⟨fun w w' h => Subtype.ext (PhiAL_injective (congrArg Subtype.val h)), fun f => by
      obtain ⟨w, hw⟩ := (PhiAL_bijective (p := p) (A := T)).2 (toW act f.1)
      refine ⟨⟨w, (mem_E_iff act hρ q w).mp ?_⟩, Subtype.ext hw⟩
      rw [hw]
      exact f.2⟩

include hρ in
theorem finrank_E (q : ℤ) : finrank L (E act q) = finrank L (DHT ρ.dual q) :=
  (eEquiv act hρ q).finrank_eq.symm

instance : FiniteDimensional ℂ_[p] (HomT act) :=
  inferInstanceAs (FiniteDimensional ℂ_[p] (T →ₗ[ℤ_[p]] ℂ_[p]))

instance (q : ℤ) : FiniteDimensional L (E act q) :=
  SerreTate.finiteDimensional_eigen (htSetup L) (smul_distrib_homT act) q

/-! ### Lifting weight-`1` classes along an extension -/

section Lift

variable {T' T'' : Type*} [AddCommGroup T'] [Module ℤ_[p] T'] [Module.Finite ℤ_[p] T']
  [Module.Free ℤ_[p] T'] [AddCommGroup T''] [Module ℤ_[p] T''] [Module.Finite ℤ_[p] T'']
  (act' : Representation ℤ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) T')
  (act'' : Representation ℤ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) T'')
  {ρ' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (ℚ_[p] ⊗[ℤ_[p]] T')}
  {ρ'' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (ℚ_[p] ⊗[ℤ_[p]] T'')}
  (hρ' : ∀ σ, ρ' σ = (act' σ).baseChange ℚ_[p]) (hρ'' : ∀ σ, ρ'' σ = (act'' σ).baseChange ℚ_[p])

omit [Module.Free ℤ_[p] T] in
include hρ hρ' hρ'' in
/-- **Lifting weight-`1` classes**: for an equivariant exact sequence `0 → T' → T → T'' → 0` of
`ℤ_p`-lattices with `ℂ_p ⊗ V''^∨` without weight `1`, every `f' : T' → ℂ_p` with
`f'(σ x) = χ(σ) σ(f' x)` extends to such an `f : T → ℂ_p` (Tate's `H¹(G_L, ℂ_p(j)) = 0`,
`exists_DHT_lift` applied to `0 → V''^∨ → V^∨ → V'^∨ → 0`). -/
theorem exists_lift_E_one (u : T' →ₗ[ℤ_[p]] T) (v : T →ₗ[ℤ_[p]] T'')
    (hu : Function.Injective u) (hv : Function.Surjective v) (huv : Function.Exact u v)
    (hue : ∀ σ x, u (act' σ x) = act σ (u x)) (hve : ∀ σ x, v (act σ x) = act'' σ (v x))
    (hcont : ∀ (φ : Dual ℚ_[p] (Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T))) (w : Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T)),
      Continuous fun σ => φ (ρ.dual σ w))
    (hHT : IsHodgeTate ρ''.dual) (hq : DHT ρ''.dual 1 = ⊥)
    (f' : T' →ₗ[ℤ_[p]] ℂ_[p]) (hf' : ofW act' f' ∈ E act' 1) :
    ∃ f : T →ₗ[ℤ_[p]] ℂ_[p], ofW act f ∈ E act 1 ∧ f ∘ₗ u = f' := by
  haveI : Module.Flat ℤ_[p] ℚ_[p] := IsLocalization.flat ℚ_[p] (nonZeroDivisors ℤ_[p])
  let uQ := u.baseChange ℚ_[p]
  let vQ := v.baseChange ℚ_[p]
  have huQ : ∀ σ, uQ ∘ₗ ρ' σ = ρ σ ∘ₗ uQ := fun σ => by
    rw [hρ', hρ, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    exact LinearMap.ext fun x => hue σ x
  have hvQ : ∀ σ, vQ ∘ₗ ρ σ = ρ'' σ ∘ₗ vQ := fun σ => by
    rw [hρ'', hρ, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    exact LinearMap.ext fun x => hve σ x
  have huQi : Function.Injective uQ := by
    change Function.Injective (u.baseChange ℚ_[p])
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hu
  have hvQs : Function.Surjective vQ := by
    change Function.Surjective (v.baseChange ℚ_[p])
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ hv
  have hex : Function.Exact uQ vQ := by
    change Function.Exact (u.baseChange ℚ_[p]) (v.baseChange ℚ_[p])
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact _root_.lTensor_exact ℚ_[p] huv hv
  have hf'' : ∀ σ, vQ.dualMap ∘ₗ ρ''.dual σ = ρ.dual σ ∘ₗ vQ.dualMap :=
    fun σ => LinearMap.ext fun χ => LinearMap.ext fun w => by
      simp only [LinearMap.comp_apply, Representation.dual_apply, Module.Dual.transpose_apply,
        LinearMap.dualMap_apply]
      exact congrArg χ (LinearMap.congr_fun (hvQ σ⁻¹) w).symm
  have hg'' : ∀ σ, uQ.dualMap ∘ₗ ρ.dual σ = ρ'.dual σ ∘ₗ uQ.dualMap :=
    fun σ => LinearMap.ext fun χ => LinearMap.ext fun w => by
      simp only [LinearMap.comp_apply, Representation.dual_apply, Module.Dual.transpose_apply,
        LinearMap.dualMap_apply]
      exact congrArg χ (LinearMap.congr_fun (huQ σ⁻¹) w).symm
  have hfi : Function.Injective vQ.dualMap := LinearMap.dualMap_injective_of_surjective hvQs
  have hgs : Function.Surjective uQ.dualMap := LinearMap.dualMap_surjective_of_injective huQi
  have hex' : Function.Exact vQ.dualMap uQ.dualMap := by
    rw [LinearMap.exact_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range,
      LinearMap.range_dualMap_eq_dualAnnihilator_ker, LinearMap.exact_iff.mp hex]
  obtain ⟨w, hw⟩ := (PhiAL_bijective (p := p) (A := T')).2 f'
  have hwD : w ∈ DHT ρ'.dual 1 := (mem_E_iff act' hρ' 1 w).mp (by rw [hw]; exact hf')
  obtain ⟨wH, hwH, hwH'⟩ := exists_DHT_lift hf'' hg'' hfi hgs hex' hcont hHT hq hwD
  refine ⟨PhiAL wH, (mem_E_iff act hρ 1 wH).mpr hwH, ?_⟩
  rw [PhiAL_comp]
  exact (congrArg PhiAL hwH').trans hw

end Lift

/-! ### Weight vanishing -/

/-- `σ ∈ G_{L'}` as an element of `G_L` for `L ⊆ L'`. -/
def resGal {L' : IntermediateField ℚ_[p] K} (h : L ≤ L') (σ : K ≃ₐ[L'] K) : K ≃ₐ[L] K :=
  { σ.toRingEquiv with commutes' := fun z => σ.commutes ⟨z, h z.2⟩ }

omit [FiniteDimensional ℚ_[p] L] in
theorem galCp_resGal {L' : IntermediateField ℚ_[p] K} (h : L ≤ L') (σ : K ≃ₐ[L'] K)
    (z : ℂ_[p]) : galCp L (resGal h σ) z = galCp L' σ z := rfl

/-- **Weight vanishing**: if `dim_L E 0 ≥ rank T` (i.e. `ℂ_p ⊗ V` is trivial, Hodge–Tate of
weight `0`), then for `L ⊆ L'` finite and `j ≠ 0` every `f` with `f(σ x) = χ(σ)^j σ(f x)` on
`G_{L'}` vanishes. -/
theorem eq_zero_of_isTwist (h0 : finrank ℤ_[p] T ≤ finrank L (E act 0))
    {L' : IntermediateField ℚ_[p] K} [FiniteDimensional ℚ_[p] L'] (hLL' : L ≤ L') {j : ℤ}
    (hj : j ≠ 0) (f : T →ₗ[ℤ_[p]] ℂ_[p])
    (hf : ∀ (σ : K ≃ₐ[L'] K) (x : T),
      f (act (resGal hLL' σ) x) = algebraMap ℚ_[p] ℂ_[p] (chiL L' j σ) * galCp L' σ (f x)) :
    f = 0 := by
  classical
  set n := finrank L (E act 0)
  set b := Module.finBasis L (E act 0)
  set e : Fin n → HomT act := fun i => (b i : HomT act)
  have he : LinearIndependent ℂ_[p] e :=
    SerreTate.linearIndependent_of_eigen_single (htSetup L) (smul_distrib_homT act) 0 e
      (fun i => (b i).2) (b.linearIndependent.map' (E act 0).subtype (Submodule.ker_subtype _))
  have hcard : Fintype.card (Fin n) = finrank ℂ_[p] (HomT act) := by
    have h1 := he.fintype_card_le_finrank
    have h2 : finrank ℂ_[p] (HomT act) = finrank ℤ_[p] T := finrank_hom_cp
    rw [Fintype.card_fin] at h1 ⊢
    omega
  set B := basisOfLinearIndependentOfCardEqFinrank' e he hcard
  have hBe : ∀ i, B i = e i := fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  have hfix : ∀ (τ : K ≃ₐ[L] K) i, τ • B i = B i := fun τ i => by
    rw [hBe]
    have := (b i).2 τ
    rw [(htSetup L).ψ_zero, one_smul] at this
    exact this
  have hχ : ∀ σ : K ≃ₐ[L'] K, algebraMap ℚ_[p] ℂ_[p] (chiL L' (-j) σ) *
      algebraMap ℚ_[p] ℂ_[p] (chiL L' j σ) = 1 := fun σ => by
    rw [← map_mul, ← chiL_add, neg_add_cancel, chiL_zero, map_one]
  have hact : ∀ σ : K ≃ₐ[L'] K, resGal hLL' σ • ofW act f =
      algebraMap ℚ_[p] ℂ_[p] (chiL L' (-j) σ) • ofW act f := by
    intro σ
    refine LinearMap.ext fun x => ?_
    change galCp L (resGal hLL' σ) (f (act (resGal hLL' σ)⁻¹ x)) =
      algebraMap ℚ_[p] ℂ_[p] (chiL L' (-j) σ) * f x
    have h1 := hf σ (act (resGal hLL' σ)⁻¹ x)
    rw [act_apply_inv] at h1
    rw [galCp_resGal, h1, ← mul_assoc, hχ, one_mul]
  have hc : ∀ i, B.repr (ofW act f) i = 0 := by
    intro i
    refine eq_zero_of_galCp_eq_chi_smul (L := L') (j := -j) (neg_ne_zero.mpr hj) fun σ => ?_
    set c := B.repr (ofW act f)
    have hsum := B.sum_repr (ofW act f)
    have h3 := hact σ
    rw [← hsum, Finset.smul_sum, Finset.smul_sum] at h3
    simp only [smul_distrib_homT, hfix, smul_smul] at h3
    have h2 : ∑ i, (galCp L' σ (c i) - algebraMap ℚ_[p] ℂ_[p] (chiL L' (-j) σ) * c i) • B i =
        0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      exact h3
    have h4 := Fintype.linearIndependent_iff.mp B.linearIndependent _ h2 i
    change galCp L' σ (c i) = chiL L' (-j) σ • c i
    rw [Algebra.smul_def]
    exact sub_eq_zero.mp h4
  have : ofW act f = 0 := by
    rw [← B.sum_repr (ofW act f)]
    simp [hc]
  exact this

/-- If `dim_L E 0 ≥ rank T`, the `G_L`-equivariant maps span `Hom_{ℤ_p}(T, ℂ_p)` over `ℂ_p`. -/
theorem span_isEquiv_eq_top (h0 : finrank ℤ_[p] T ≤ finrank L (E act 0)) :
    Submodule.span ℂ_[p] {f : HomT act | IsEquiv act (toW act f)} = ⊤ := by
  classical
  set n := finrank L (E act 0)
  set b := Module.finBasis L (E act 0)
  set e : Fin n → HomT act := fun i => (b i : HomT act)
  have he : LinearIndependent ℂ_[p] e :=
    SerreTate.linearIndependent_of_eigen_single (htSetup L) (smul_distrib_homT act) 0 e
      (fun i => (b i).2) (b.linearIndependent.map' (E act 0).subtype (Submodule.ker_subtype _))
  have hcard : Fintype.card (Fin n) = finrank ℂ_[p] (HomT act) := by
    have h1 := he.fintype_card_le_finrank
    have h2 : finrank ℂ_[p] (HomT act) = finrank ℤ_[p] T := finrank_hom_cp
    rw [Fintype.card_fin] at h1 ⊢
    omega
  have hspan := he.span_eq_top_of_card_eq_finrank' hcard
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ((mem_E_zero_iff act _).mp (b i).2)

/-! ### The lattice lemma -/

omit [FiniteDimensional ℚ_[p] L] in
theorem norm_p_cp_lt_one' : ‖(p : ℂ_[p])‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

omit [FiniteDimensional ℚ_[p] L] in
/-- `δ_j = b_j^*`, for the `ℤ_p`-basis `b` of `T`. -/
def delta (j : Fin (finrank ℤ_[p] T)) : T →ₗ[ℤ_[p]] ℂ_[p] :=
  Algebra.linearMap ℤ_[p] ℂ_[p] ∘ₗ (Module.finBasis ℤ_[p] T).coord j

omit [FiniteDimensional ℚ_[p] L] in
theorem eq_sum_delta (f : T →ₗ[ℤ_[p]] ℂ_[p]) :
    f = ∑ j, f (Module.finBasis ℤ_[p] T j) • delta j := by
  refine (Module.finBasis ℤ_[p] T).ext fun i => ?_
  simp [delta, Finsupp.single_apply]

omit [FiniteDimensional ℚ_[p] L] in
theorem norm_zp_smul_le (c : ℤ_[p]) (z : ℂ_[p]) : ‖c • z‖ ≤ ‖z‖ := by
  rw [← algebraMap_smul ℚ_[p] c z, ← algebraMap_smul ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] c) z,
    smul_eq_mul, norm_mul, norm_algebraMap']
  exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one c)

omit [FiniteDimensional ℚ_[p] L] in
/-- A `ℤ_p`-linear map `T → ℂ_p` is bounded. -/
theorem exists_norm_le (f : T →ₗ[ℤ_[p]] ℂ_[p]) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  refine ⟨∑ j, ‖f (Module.finBasis ℤ_[p] T j)‖, fun x => ?_⟩
  conv_lhs => rw [← (Module.finBasis ℤ_[p] T).sum_repr x]
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_smul]
  exact norm_zp_smul_le _ _

omit [FiniteDimensional ℚ_[p] L] in
/-- **`p^N ρ` is integral** for some `N`. -/
theorem exists_pow_norm_le {d : ℕ} (ρ : Fin d → T →ₗ[ℤ_[p]] ℂ_[p]) :
    ∃ N : ℕ, ∀ a : Fin d → ℂ_[p], (∀ l, ‖a l‖ ≤ 1) → ∀ x : T,
      ‖(p : ℂ_[p]) ^ N * ∑ l, a l * ρ l x‖ ≤ 1 := by
  choose C hC using fun l => exists_norm_le (ρ l)
  set D : ℝ := ∑ l, |C l| + 1 with hD
  have hDpos : 0 < D := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hDpos) (norm_p_cp_lt_one' (p := p))
  refine ⟨N, fun a ha x => ?_⟩
  have h1 : ‖∑ l, a l * ρ l x‖ ≤ D := by
    refine (norm_sum_le _ _).trans ?_
    have : ∑ l, ‖a l * ρ l x‖ ≤ ∑ l, |C l| := Finset.sum_le_sum fun l _ => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (ha l)).trans ((hC l x).trans (le_abs_self _))
    linarith
  rw [norm_mul, norm_pow]
  calc ‖(p : ℂ_[p])‖ ^ N * ‖∑ l, a l * ρ l x‖ ≤ D⁻¹ * D :=
        mul_le_mul hN.le h1 (norm_nonneg _) (inv_pos.mpr hDpos).le
    _ = 1 := inv_mul_cancel₀ hDpos.ne'

omit [FiniteDimensional ℚ_[p] L] in
/-- **The lattice lemma** ((FoInt)(c), [Fo, §5.9] in weak form): for `ℂ_p`-linearly independent
`ρ_1, …, ρ_d ∈ Hom_{ℤ_p}(T, ℂ_p)`, a complement `V₁` of their span and `N` with `p^N ρ`
integral, there is `c` such that for every `f ∈ M = Hom_{ℤ_p}(T, O_{ℂ_p})` there is
`a ∈ O_{ℂ_p}^d` with `p^c f - p^N ∑_l a_l ρ_l ∈ V₁ ∩ M`. -/
theorem exists_lattice {d : ℕ} (ρ : Fin d → T →ₗ[ℤ_[p]] ℂ_[p]) (hρ : LinearIndependent ℂ_[p] ρ)
    (V1 : Submodule ℂ_[p] (T →ₗ[ℤ_[p]] ℂ_[p]))
    (hc : IsCompl (Submodule.span ℂ_[p] (Set.range ρ)) V1) (N : ℕ)
    (hN : ∀ a : Fin d → ℂ_[p], (∀ l, ‖a l‖ ≤ 1) → ∀ x : T,
      ‖(p : ℂ_[p]) ^ N * ∑ l, a l * ρ l x‖ ≤ 1) :
    ∃ c : ℕ, ∀ f : T →ₗ[ℤ_[p]] ℂ_[p], (∀ x, ‖f x‖ ≤ 1) → ∃ a : Fin d → ℂ_[p],
      (∀ l, ‖a l‖ ≤ 1) ∧ (p : ℂ_[p]) ^ c • f - (p : ℂ_[p]) ^ N • ∑ l, a l • ρ l ∈ V1 ∧
      ∀ x, ‖((p : ℂ_[p]) ^ c • f - (p : ℂ_[p]) ^ N • ∑ l, a l • ρ l) x‖ ≤ 1 := by
  set V0 := Submodule.span ℂ_[p] (Set.range ρ)
  set bV0 : Basis (Fin d) ℂ_[p] V0 := Basis.span hρ
  have hbV0 : ∀ l, (bV0 l : T →ₗ[ℤ_[p]] ℂ_[p]) = ρ l := fun l =>
    congrArg Subtype.val (Basis.span_apply _ _)
  set kappa : Fin d → (T →ₗ[ℤ_[p]] ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] := fun l =>
    bV0.coord l ∘ₗ V0.projectionOnto V1 hc
  have hsub : ∀ f, f - ∑ l, kappa l f • ρ l ∈ V1 := by
    intro f
    have h1 : ((V0.projectionOnto V1 hc f : V0) : T →ₗ[ℤ_[p]] ℂ_[p]) =
        ∑ l, kappa l f • ρ l := by
      conv_lhs => rw [← bV0.sum_repr (V0.projectionOnto V1 hc f)]
      simp only [Submodule.coe_sum, Submodule.coe_smul, hbV0, kappa, LinearMap.comp_apply,
        Basis.coord_apply]
    rw [← h1, Submodule.coe_projectionOnto_apply]
    exact Submodule.sub_projection_mem _ f
  set K0 : ℝ := ∑ l, ∑ j, ‖kappa l (delta j)‖ + 1 with hKdef
  have hK : 0 < K0 := by positivity
  have hp1 := norm_p_cp_lt_one' (p := p)
  obtain ⟨c', hc'⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hK) hp1
  refine ⟨N + c', fun f hf => ?_⟩
  set a : Fin d → ℂ_[p] := fun l => (p : ℂ_[p]) ^ c' * kappa l f with hadef
  have ha : ∀ l, ‖a l‖ ≤ 1 := by
    intro l
    have hk : ‖kappa l f‖ ≤ K0 := by
      conv_lhs => rw [eq_sum_delta f]
      rw [map_sum]
      calc ‖∑ j, kappa l (f (Module.finBasis ℤ_[p] T j) • delta j)‖
          ≤ ∑ j, ‖kappa l (f (Module.finBasis ℤ_[p] T j) • delta j)‖ := norm_sum_le _ _
        _ ≤ ∑ j, ‖kappa l (delta j)‖ := Finset.sum_le_sum fun j _ => by
            rw [map_smul, smul_eq_mul, norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) (hf _)
        _ ≤ ∑ l, ∑ j, ‖kappa l (delta j)‖ :=
            Finset.single_le_sum (f := fun l => ∑ j, ‖kappa l (delta j)‖)
              (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ l)
        _ ≤ K0 := by linarith
    rw [hadef, norm_mul, norm_pow]
    calc ‖(p : ℂ_[p])‖ ^ c' * ‖kappa l f‖ ≤ K0⁻¹ * K0 :=
          mul_le_mul hc'.le hk (norm_nonneg _) (inv_pos.mpr hK).le
      _ = 1 := inv_mul_cancel₀ hK.ne'
  refine ⟨a, ha, ?_, fun x => ?_⟩
  · have : (p : ℂ_[p]) ^ (N + c') • f - (p : ℂ_[p]) ^ N • ∑ l, a l • ρ l =
        (p : ℂ_[p]) ^ (N + c') • (f - ∑ l, kappa l f • ρ l) := by
      rw [smul_sub, Finset.smul_sum, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, smul_smul, hadef, pow_add, mul_assoc]
    rw [this]
    exact Submodule.smul_mem _ _ (hsub f)
  · have h2 : (∑ l, a l • ρ l) x = ∑ l, a l * ρ l x := by
      simp [LinearMap.sum_apply, smul_eq_mul]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
      smul_eq_mul, h2]
    have h1 : ‖(p : ℂ_[p]) ^ (N + c') * f x‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hp1.le) (norm_nonneg _) (hf x)
    have h3 := hN a ha x
    have hu : ‖(p : ℂ_[p]) ^ (N + c') * f x - (p : ℂ_[p]) ^ N * ∑ l, a l * ρ l x‖ ≤
        max ‖(p : ℂ_[p]) ^ (N + c') * f x‖ ‖(p : ℂ_[p]) ^ N * ∑ l, a l * ρ l x‖ := by
      simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max
        ((p : ℂ_[p]) ^ (N + c') * f x) (-((p : ℂ_[p]) ^ N * ∑ l, a l * ρ l x))
    exact hu.trans (max_le h1 h3)

end HomRep

namespace PDivGroup

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- `T_p X(ℚ̄_p)` with its `G_L`-action as a `ℤ_p`-representation, for `X` over `L`. -/
def galRepZ (X : PDivGroup L p) :
    Representation ℤ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
      (Additive (X.TateModule (PadicAlgCl p))) where
  toFun := X.galLin
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

theorem galRepZ_apply (X : PDivGroup L p) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) :
    X.galRepZ σ = X.galLin σ := rfl

theorem repQ_galRepZ (X : PDivGroup L p) : HomRep.repQ X.galRepZ = X.tateRepOver := rfl

end PDivGroup

end PadicHodge
