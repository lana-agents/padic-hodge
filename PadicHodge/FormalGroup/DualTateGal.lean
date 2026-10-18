/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.DualTateZp
import PadicHodge.GroupScheme.TateRep

/-!
# `T_p(G^∨)(O_{ℂ_p})`: Galois action, `ℤ_p`-module structure, `ℤ_p`-linearity of `dα`

In the proof of [Hong, Thm. 3.4.10] the target `W = Hom_{ℤ_p}(T_p(G^∨), ℂ_p)` of
`dα : t_G(ℂ_p) → W` ([Hong, Prop. 3.4.9]) is compared, `Γ`-equivariantly, with
`T_p(G_{ℚ_p}^∨)(ℚ̄_p)`, where the Cartier pairing with values in `ℤ_p(1)` lives
(`tatePairingZp`). This file provides, for a `p`-divisible group `G` over `ℤ_p` (`ZpD p`):

* `PDivGroup.galDualGen`: the action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` fixing `R` on `T_p(G^∨)(O_{ℂ_p})`
  through its extension to `O_{ℂ_p}` (`PDivFGL.galS`), for any `G` over `R ⊆ O_{ℂ_p}`; for
  `G = F[p^∞]` it is `PDivFGL.galDual` (`PDivFGL.galDual_eq_galDualGen`); `galDualZp` for `ℤ_p`;
* `dualTateGenEquiv_spec`: `T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G_F^∨)(ℚ̄_p)` (`dualTateGenEquiv`, generic
  fibre over a field `F ⊆ ℚ̄_p`, e.g. `ℚ_p` or `K'`) is characterised levelwise by
  `z_v(f_F) = y_v(f)` in `ℂ_p`, `f ∈ A_v^∨`;
* **`dualTateGenEquiv_gal`**, `dualTateZpEquiv_gal`: it is equivariant for `σ ∈ Gal(ℚ̄_p/F)`
  fixing `R`, for the action `galTate` on `T_p(G_F^∨)`;
* `instModuleZpDual`: the `ℤ_p`-module structure on `T_p(G^∨)(S)` for any `G`, `S`
  (`a · y = (y_v^{a mod p^v})_v`, as `instModuleZp` for Tate modules), and
  **`dualTateGenLinearEquiv`**, `dualTateZpLinearEquiv`: the comparison is `ℤ_p`-linear;
* `DualTate.exists_pow_eq_of_val_eq_one_OC`: `y ∈ T_p(G^∨)(O_{ℂ_p})` with `y_v = 1` is a
  `p^v`-th power;
* **`PDivFGL.dalpha_zpSmul`**: `dα(z)(a · y) = a · dα(z)(y)` for `a ∈ ℤ_p` ([Hong, Prop. 3.4.9]:
  `dα` lands in `Hom_{ℤ_p}(T_p(G^∨), ℂ_p)`), over any `R`. Proof: for `n ≡ a mod p^v`,
  `(a·y) y^{-n}` is a `p^v`-th power, so by additivity `|∂U_{a·y}(0) − a ∂U_y(0)| ≤ 2|p|^v`
  for all `v`.
-/

noncomputable section

open WithConv IsLocalRing

namespace PadicHodge

namespace PDivGroup

open FFGroupScheme

universe u

theorem pi_subgroup_pow_val {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)]
    {H : Subgroup ((i : ι) → M i)} (y : H) (n : ℕ) (i : ι) : (y ^ n).1 i = y.1 i ^ n := by
  rw [SubgroupClass.coe_pow, Pi.pow_apply]

/-! ### The `ℤ_p`-module structure on `T_p(G^∨)(S)` -/

section Module

variable {R : Type u} [CommRing R] {p : ℕ} [hp : Fact p.Prime] (G : PDivGroup R p)
  (S : Type u) [CommRing S] [Algebra R S]

omit hp in
/-- `G_v^∨` is killed by `p^v`, levelwise on `T_p(G^∨)(S)`. -/
theorem dualTate_pow_eq_one [NeZero p] (y : G.DualTate S) (v : ℕ) : y.1 v ^ (p ^ v) = 1 :=
  (G.G v).dual.pow_eq_one_of_univPt (G.dual_univPt_pow_eq_one v) _

local instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- `y ↦ y^a` on `T_p(G^∨)(S)`, for `a ∈ ℤ_p`. -/
def dualZpPow (a : ℤ_[p]) (y : G.DualTate S) : G.DualTate S :=
  ⟨fun v => y.1 v ^ expo a v, fun v => by
    beta_reduce
    rw [map_pow, ← y.2 v, ← expo_succ a v, pow_mod_eq (G.dualTate_pow_eq_one S y v)]⟩

theorem dualZpPow_val (a : ℤ_[p]) (y : G.DualTate S) (v : ℕ) :
    (G.dualZpPow S a y).1 v = y.1 v ^ expo a v := rfl

omit hp in
theorem addDualTate_ext [NeZero p] {x y : Additive (G.DualTate S)}
    (h : ∀ v, (Additive.toMul x).1 v = (Additive.toMul y).1 v) : x = y :=
  Additive.toMul.injective (Subtype.ext (funext h))

/-- **`T_p(G^∨)(S)` is a `ℤ_p`-module**: `a · y = (y_v^{a mod p^v})_v`. -/
instance instModuleZpDual : Module ℤ_[p] (Additive (G.DualTate S)) where
  smul a y := Additive.ofMul (G.dualZpPow S a (Additive.toMul y))
  one_smul y := G.addDualTate_ext S fun v => by
    change (Additive.toMul y).1 v ^ expo 1 v = _
    rw [expo, map_one, ZMod.val_one_eq_one_mod, pow_mod_eq (G.dualTate_pow_eq_one S _ v),
      pow_one]
  mul_smul a b y := G.addDualTate_ext S fun v => by
    change (Additive.toMul y).1 v ^ expo (a * b) v =
      ((Additive.toMul y).1 v ^ expo b v) ^ expo a v
    rw [expo, map_mul, ZMod.val_mul, pow_mod_eq (G.dualTate_pow_eq_one S _ v), ← pow_mul,
      mul_comm]
  smul_zero a := G.addDualTate_ext S fun v => by
    change (1 : (G.G v).dual.points S) ^ expo a v = 1
    rw [one_pow]
  smul_add a x y := G.addDualTate_ext S fun v => by
    change ((Additive.toMul x).1 v * (Additive.toMul y).1 v) ^ expo a v =
      (Additive.toMul x).1 v ^ expo a v * (Additive.toMul y).1 v ^ expo a v
    rw [mul_pow]
  add_smul a b y := G.addDualTate_ext S fun v => by
    change (Additive.toMul y).1 v ^ expo (a + b) v =
      (Additive.toMul y).1 v ^ expo a v * (Additive.toMul y).1 v ^ expo b v
    rw [expo, map_add, ZMod.val_add, pow_mod_eq (G.dualTate_pow_eq_one S _ v), pow_add]
  zero_smul y := G.addDualTate_ext S fun v => by
    change (Additive.toMul y).1 v ^ expo 0 v = 1
    rw [expo, map_zero, ZMod.val_zero, pow_zero]

theorem dualSmul_val (a : ℤ_[p]) (y : Additive (G.DualTate S)) (v : ℕ) :
    (Additive.toMul (a • y)).1 v = (Additive.toMul y).1 v ^ expo a v := rfl

end Module

/-! ### `y_v = 1` implies `y ∈ p^v T_p(G^∨)(O_{ℂ_p})` -/

section PowOC

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [Nontrivial R] [Algebra R (OC p)]
  (G : PDivGroup R p)

local instance : NeZero p := ⟨hp.out.ne_zero⟩

omit hp [Nontrivial R] [Algebra R (OC p)] in
theorem DualTate.val_eq_one_of_le {T : Type} [CommRing T] [Algebra R T] (z : G.DualTate T)
    {a b : ℕ} (hab : a ≤ b) : z.1 b = 1 → z.1 a = 1 := by
  induction b, hab using Nat.le_induction with
  | base => exact id
  | succ b _ ih => exact fun hz => ih (by rw [z.2 b, hz, map_one])

/-- `quot_v^∨` is injective on `O_{ℂ_p}`-points. -/
theorem dual_quot_injective_OC (v : ℕ) :
    Function.Injective ((G.quot v).dual.mapPoints (OC p)) := by
  letI := algebraCpOfOC (p := p) R
  intro w w' h
  apply (G.G v).dual.pointsOCEquiv.injective
  exact G.dual_quot_injective_of_card ℂ_[p] G.card_points_Cp v
    (congrArg (G.G (v + 1)).dual.pointsOCEquiv h)

/-- **A point `y ∈ T_p(G^∨)(O_{ℂ_p})` with `y_v = 1` is a `p^v`-th power.** -/
theorem DualTate.exists_pow_eq_of_val_eq_one_OC (v : ℕ) (z : G.DualTate (OC p))
    (hz : z.1 v = 1) : ∃ w : G.DualTate (OC p), w ^ (p ^ v) = z := by
  induction v generalizing z with
  | zero => exact ⟨z, by rw [pow_zero, pow_one]⟩
  | succ v ih =>
    obtain ⟨w, hw⟩ := DualTate.exists_pow_eq_OC G z
      (DualTate.val_eq_one_of_le G z (by omega) hz)
    have hw1 : w.1 v = 1 := by
      apply G.dual_quot_injective_OC v
      rw [DualTate.dual_quot_succ, map_one, ← pi_subgroup_pow_val, hw, hz]
    obtain ⟨u, hu⟩ := ih w hw1
    exact ⟨u, by rw [pow_succ, pow_mul, hu, hw]⟩

end PowOC

/-! ### Galois equivariance of `T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G_{ℚ_p}^∨)(ℚ̄_p)` -/

section GalGen

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [Algebra R (OC p)]
  (G : PDivGroup R p)

/-- **The Galois action on `T_p(G^∨)(O_{ℂ_p})`** for `G` over `R ⊆ O_{ℂ_p}`: `σ` acts on
`O_{ℂ_p}` by `R`-algebra automorphisms if it fixes `R` (`PDivFGL.galS`). -/
def galDualGen (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hR : ∀ r : R, autCp σ ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r) :
    G.DualTate (OCd p) →* G.DualTate (OCd p) where
  toFun y := ⟨fun v => (G.G v).dual.postComp (PDivFGL.galS σ hR) (y.1 v),
    fun v => by
      beta_reduce
      rw [y.2 v]
      rfl⟩
  map_one' := by ext1; funext v; exact map_one _
  map_mul' x y := by ext1; funext v; exact map_mul _ _ _

theorem galDualGen_congr {σ₁ σ₂ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (h : σ₁ = σ₂)
    (h₁ : ∀ r : R, autCp σ₁ ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r)
    (h₂ : ∀ r : R, autCp σ₂ ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r)
    (y : G.DualTate (OCd p)) : G.galDualGen σ₁ h₁ y = G.galDualGen σ₂ h₂ y := by
  subst h
  rfl

theorem galDualGen_apply (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hR : ∀ r : R, autCp σ ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r)
    (y : G.DualTate (OCd p)) (v : ℕ) (f : Cartier.Dual R (G.G v).A) :
    ((OCd.toOC (ofConv ((G.galDualGen σ hR y).1 v) f) : OC p) : ℂ_[p]) =
      autCp σ ((OCd.toOC (ofConv (y.1 v) f) : OC p) : ℂ_[p]) :=
  PDivFGL.galS_apply σ hR _

variable [Nontrivial R] {F : Type} [Field F] [CharZero F] [Algebra R F] [Algebra F (PadicAlgCl p)]
  [Algebra R (PadicAlgCl p)] [IsScalarTower R F (PadicAlgCl p)]
  (hRF : ∀ r : R, ((algebraMap R (PadicAlgCl p) r : PadicAlgCl p) : ℂ_[p]) =
    ((algebraMap R (OC p) r : OC p) : ℂ_[p]))

include hRF

/-- **Levelwise description of `dualTateGenEquiv`**: `z_v(f_F) = y_v(f)` in `ℂ_p`. -/
theorem dualTateGenEquiv_spec (y : G.DualTate (OCd p)) (v : ℕ)
    (f : Cartier.Dual R (G.G v).A) :
    ((ofConv ((G.dualTateGenEquiv (F := F) hRF y).1 v) ((G.G v).dualBC (S := F) f) :
      PadicAlgCl p) : ℂ_[p]) = ((OCd.toOC (ofConv (y.1 v) f) : OC p) : ℂ_[p]) := by
  letI := algebraCpOfOC (p := p) R
  have h1 : (G.G v).dualBaseChangePointsEquiv (S := F) ((G.dualTateGenEquiv hRF y).1 v) =
      (G.dualPointsQbarCpOf hRF v).symm ((G.G v).dual.pointsOCEquiv (p := p) (y.1 v)) := by
    change (G.G v).dualBaseChangePointsEquiv (S := F)
      (((G.G v).dualBaseChangePointsEquiv (S := F)).symm _) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have h2 := congrArg (fun χ : (G.G v).dual.points ℂ_[p] => ofConv χ f)
    (MulEquiv.apply_symm_apply (G.dualPointsQbarCpOf hRF v)
      ((G.G v).dual.pointsOCEquiv (p := p) (y.1 v)))
  change qbarToCpOf hRF (ofConv ((G.G v).dualBaseChangePointsEquiv (S := F)
    ((G.dualTateGenEquiv hRF y).1 v)) f) = _
  rw [h1]
  exact h2

/-- `dualTateGenEquiv` is determined levelwise by `dualTateGenEquiv_spec`. -/
theorem dualTateGenEquiv_val_eq (y : G.DualTate (OCd p)) (v : ℕ)
    (z : ((G.G v).baseChange F).dual.points (PadicAlgCl p))
    (h : ∀ f : Cartier.Dual R (G.G v).A,
      ((ofConv z ((G.G v).dualBC (S := F) f) : PadicAlgCl p) : ℂ_[p]) =
        ((OCd.toOC (ofConv (y.1 v) f) : OC p) : ℂ_[p])) :
    (G.dualTateGenEquiv hRF y).1 v = z := by
  apply ((G.G v).dualBaseChangePointsEquiv (S := F) (T := PadicAlgCl p)).injective
  apply WithConv.ofConv_injective
  refine AlgHom.ext fun f => (algebraMap (PadicAlgCl p) ℂ_[p]).injective ?_
  exact (G.dualTateGenEquiv_spec hRF y v f).trans (h f).symm

/-- The level-`v` component of `dualTateGenEquiv y` only depends on `y_v`. -/
theorem dualTateGenEquiv_val_congr {y y' : G.DualTate (OCd p)} {v : ℕ} (h : y.1 v = y'.1 v) :
    (G.dualTateGenEquiv (F := F) hRF y).1 v = (G.dualTateGenEquiv hRF y').1 v :=
  G.dualTateGenEquiv_val_eq hRF y v _ fun f =>
    (G.dualTateGenEquiv_spec hRF y' v f).trans (by rw [h])

variable [Algebra ℚ_[p] F] [IsScalarTower ℚ_[p] F (PadicAlgCl p)]

theorem dualTateGenEquiv_gal_val (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p)
    (hR : ∀ r : R, autCp (σ.restrictScalars ℚ_[p]) ((algebraMap R (OC p) r : OC p) : ℂ_[p]) =
      algebraMap R (OC p) r)
    (y : G.DualTate (OCd p)) (v : ℕ) :
    (G.dualTateGenEquiv hRF (G.galDualGen (σ.restrictScalars ℚ_[p]) hR y)).1 v =
      galPoints ((G.G v).baseChange F).dual σ ((G.dualTateGenEquiv hRF y).1 v) := by
  refine G.dualTateGenEquiv_val_eq hRF _ v _ fun f => ?_
  exact ((autCp_coe (σ.restrictScalars ℚ_[p]) _).symm.trans
    (congrArg (autCp (σ.restrictScalars ℚ_[p])) (G.dualTateGenEquiv_spec hRF y v f))).trans
    (G.galDualGen_apply (σ.restrictScalars ℚ_[p]) hR y v f).symm

/-- **Galois equivariance of `T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G_F^∨)(ℚ̄_p)`** for `σ ∈ Gal(ℚ̄_p/F)`
fixing `R`. -/
theorem dualTateGenEquiv_gal (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p)
    (hR : ∀ r : R, autCp (σ.restrictScalars ℚ_[p]) ((algebraMap R (OC p) r : OC p) : ℂ_[p]) =
      algebraMap R (OC p) r)
    (y : G.DualTate (OCd p)) :
    G.dualTateGenEquiv hRF (G.galDualGen (σ.restrictScalars ℚ_[p]) hR y) =
      (G.baseChange F).dualPDiv.galTate σ (G.dualTateGenEquiv hRF y) :=
  Subtype.ext (funext fun v => G.dualTateGenEquiv_gal_val hRF σ hR y v)

omit [Algebra ℚ_[p] F] [IsScalarTower ℚ_[p] F (PadicAlgCl p)]

local instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- **`T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G_F^∨)(ℚ̄_p)` is `ℤ_p`-linear.** -/
def dualTateGenLinearEquiv : Additive (G.DualTate (OCd p)) ≃ₗ[ℤ_[p]]
    Additive ((G.baseChange F).dualPDiv.TateModule (PadicAlgCl p)) :=
  AddEquiv.toLinearEquiv (MulEquiv.toAdditive (G.dualTateGenEquiv hRF)) fun a y =>
    (G.baseChange F).dualPDiv.addTate_ext _ fun v => by
      rw [smul_val]
      change (G.dualTateGenEquiv hRF (Additive.toMul (a • y))).1 v =
        (G.dualTateGenEquiv hRF (Additive.toMul y)).1 v ^ expo a v
      rw [G.dualTateGenEquiv_val_congr hRF (y' := Additive.toMul y ^ expo a v) (v := v)
        (by rw [pi_subgroup_pow_val]; rfl), map_pow, pi_subgroup_pow_val]

theorem dualTateGenLinearEquiv_apply (y : Additive (G.DualTate (OCd p))) :
    Additive.toMul (G.dualTateGenLinearEquiv (F := F) hRF y) =
      G.dualTateGenEquiv hRF (Additive.toMul y) := rfl

end GalGen

/-! ### `R = ℤ_p`, `F = ℚ_p` -/

section Gal

variable {p : ℕ} [hp : Fact p.Prime] (G : PDivGroup (ZpD p) p)

/-- **The Galois action on `T_p(G^∨)(O_{ℂ_p})`** for `G` over `ℤ_p`: `σ` acts on `O_{ℂ_p}` by
`ℤ_p`-algebra automorphisms (`PDivFGL.galS`; `ℤ_p` is fixed, `ZpD.galFixed`). -/
def galDualZp (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    G.DualTate (OCd p) →* G.DualTate (OCd p) :=
  G.galDualGen σ (ZpD.galFixed σ)

/-- **Galois equivariance of `T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G_{ℚ_p}^∨)(ℚ̄_p)`.** -/
theorem dualTateZpEquiv_gal (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (y : G.DualTate (OCd p)) :
    G.dualTateZpEquiv (G.galDualZp σ y) =
      (G.baseChange ℚ_[p]).dualPDiv.galTate σ (G.dualTateZpEquiv y) :=
  G.dualTateGenEquiv_gal ZpD.algebraMap_qbar_cp σ (ZpD.galFixed σ) y

/-- **`T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G_{ℚ_p}^∨)(ℚ̄_p)` is `ℤ_p`-linear.** -/
def dualTateZpLinearEquiv : Additive (G.DualTate (OCd p)) ≃ₗ[ℤ_[p]]
    Additive ((G.baseChange ℚ_[p]).dualPDiv.TateModule (PadicAlgCl p)) :=
  G.dualTateGenLinearEquiv ZpD.algebraMap_qbar_cp

theorem dualTateZpLinearEquiv_apply (y : Additive (G.DualTate (OCd p))) :
    Additive.toMul (G.dualTateZpLinearEquiv y) = G.dualTateZpEquiv (Additive.toMul y) := rfl

end Gal

end PDivGroup

/-! ### `p`-divisible formal group laws over `ℤ_p` -/

namespace PDivFGL

open PDivGroup

section General

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  (hpm : (p : R) ∈ maximalIdeal R) {d : ℕ} (P : PDivFGL R d p)

local instance : NeZero p := ⟨hp.out.ne_zero⟩

omit [UniformSpace R] [DiscreteUniformity R]
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)] in
/-- For `G = F[p^∞]`, the Galois action `galDual` of `AlphaGal.lean` is `galDualGen`. -/
theorem galDual_eq_galDualGen (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hR : ∀ r : R, autCp σ ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r)
    (y : P.pdivGroup.DualTate (OCd p)) :
    P.galDual σ hR y = P.pdivGroup.galDualGen σ hR y := rfl

theorem dU_one (j : Fin d) : P.dU hpm 1 j = 0 := by
  have h := P.dU_mul hpm 1 1 j
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem dU_pow (y : P.pdivGroup.DualTate (OCd p)) (n : ℕ) (j : Fin d) :
    P.dU hpm (y ^ n) j = n • P.dU hpm y j := by
  induction n with
  | zero => rw [pow_zero, dU_one, zero_smul]
  | succ n ih => rw [pow_succ, dU_mul, ih, succ_nsmul]

/-- **`∂U_{a·y}/∂T_j(0) = a ∂U_y/∂T_j(0)`** for `a ∈ ℤ_p` (in `ℂ_p`). -/
theorem dU_smul (a : ℤ_[p]) (y : P.pdivGroup.DualTate (OCd p)) (j : Fin d) :
    ((OCd.toOC (P.dU hpm (Additive.toMul (a • Additive.ofMul y)) j) : OC p) : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p] a * ((OCd.toOC (P.dU hpm y j) : OC p) : ℂ_[p]) := by
  set D := ((OCd.toOC (P.dU hpm (Additive.toMul (a • Additive.ofMul y)) j) : OC p) : ℂ_[p]) -
    algebraMap ℚ_[p] ℂ_[p] a * ((OCd.toOC (P.dU hpm y j) : OC p) : ℂ_[p])
  -- `‖D‖ ≤ |p|^v` for all `v`
  have hD : ∀ v : ℕ, ‖D‖ ≤ 2 * FGL.np p ^ v := by
    intro v
    set n := expo a v
    set y' := Additive.toMul (a • Additive.ofMul y)
    obtain ⟨b, hb⟩ : ∃ b : ℤ_[p], b * (p : ℤ_[p]) ^ v = a - (n : ℤ_[p]) := by
      have hk : a - (n : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) v) := by
        rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
      rw [PadicInt.ker_toZModPow] at hk
      exact Ideal.mem_span_singleton'.mp hk
    have hA : algebraMap ℚ_[p] ℂ_[p] a =
        (n : ℂ_[p]) + (p : ℂ_[p]) ^ v * algebraMap ℚ_[p] ℂ_[p] b := by
      have h1 : (a : ℚ_[p]) = (n : ℚ_[p]) + (p : ℚ_[p]) ^ v * (b : ℚ_[p]) := by
        have := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hb
        simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
          PadicInt.coe_sub] at this
        linear_combination -this
      rw [h1, map_add, map_mul, map_pow, map_natCast, map_natCast]
    set z := y' * (y ^ n)⁻¹
    have hz : z.1 v = 1 := by
      change y.1 v ^ n * ((y ^ n)⁻¹ : P.pdivGroup.DualTate (OCd p)).1 v = 1
      rw [InvMemClass.coe_inv, Pi.inv_apply, pi_subgroup_pow_val, mul_inv_cancel]
    obtain ⟨w, hw⟩ : ∃ w : P.pdivGroup.DualTate (OCd p), w ^ (p ^ v) = z :=
      DualTate.exists_pow_eq_of_val_eq_one_OC P.pdivGroup v z hz
    have hy' : y' = y ^ n * z := by rw [mul_comm, inv_mul_cancel_right]
    have hdU : P.dU hpm y' j = (n : OCd p) * P.dU hpm y j + (p : OCd p) ^ v * P.dU hpm w j := by
      rw [hy', dU_mul, dU_pow, ← hw, dU_pow, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_pow]
    have key : D = (p : ℂ_[p]) ^ v * (((OCd.toOC (P.dU hpm w j) : OC p) : ℂ_[p]) -
        algebraMap ℚ_[p] ℂ_[p] b * ((OCd.toOC (P.dU hpm y j) : OC p) : ℂ_[p])) := by
      have e : ((OCd.toOC (P.dU hpm y' j) : OC p) : ℂ_[p]) =
          (n : ℂ_[p]) * ((OCd.toOC (P.dU hpm y j) : OC p) : ℂ_[p]) +
            (p : ℂ_[p]) ^ v * ((OCd.toOC (P.dU hpm w j) : OC p) : ℂ_[p]) := by
        rw [hdU]
        push_cast [OCd.toOC]
        rfl
      change ((OCd.toOC (P.dU hpm y' j) : OC p) : ℂ_[p]) - _ = _
      rw [e, hA]
      ring
    have hb1 : ‖algebraMap ℚ_[p] ℂ_[p] b‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
        PadicComplex.norm_extends' p]
      exact PadicInt.norm_le_one b
    rw [key, norm_mul, norm_pow, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) v)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h1 := norm_OC_le (OCd.toOC (P.dU hpm w j))
    have h2 := norm_OC_le (OCd.toOC (P.dU hpm y j))
    nlinarith [norm_nonneg (algebraMap ℚ_[p] ℂ_[p] b),
      norm_nonneg ((OCd.toOC (P.dU hpm y j) : OC p) : ℂ_[p])]
  have hD0 : D = 0 := by
    by_contra hne
    have hpos : 0 < ‖D‖ / 2 := by have := norm_pos_iff.mpr hne; positivity
    obtain ⟨v, hv⟩ := exists_pow_lt_of_lt_one hpos (FGL.np_lt_one (p := p))
    have := hD v
    linarith
  exact sub_eq_zero.mp hD0

/-- **`dα` is `ℤ_p`-linear in `y`**: `dα(z)(a · y) = a · dα(z)(y)` ([Hong, Prop. 3.4.9]:
`dα(z) ∈ Hom_{ℤ_p}(T_p(G^∨), ℂ_p)`). -/
theorem dalpha_zpSmul (z : Fin d → ℂ_[p]) (a : ℤ_[p]) (y : P.pdivGroup.DualTate (OCd p)) :
    P.dalpha hpm z (Additive.toMul (a • Additive.ofMul y)) =
      (a : ℚ_[p]) • P.dalpha hpm z y := by
  rw [dalpha, dalpha, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dU_smul, Algebra.smul_def, mul_assoc]

end General

end PDivFGL

end PadicHodge
