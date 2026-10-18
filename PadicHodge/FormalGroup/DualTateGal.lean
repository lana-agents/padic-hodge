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

* `PDivGroup.galDualZp`: the action of `σ ∈ Gal(ℚ̄_p/ℚ_p)` on `T_p(G^∨)(O_{ℂ_p})` through its
  extension to `O_{ℂ_p}` (`PDivFGL.galS`), for any `G` over `ℤ_p`; for `G = F[p^∞]` it is
  `PDivFGL.galDual` (`PDivFGL.galDual_eq_galDualZp`);
* `dualTateZpEquiv_spec`: `T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G_{ℚ_p}^∨)(ℚ̄_p)` (`dualTateZpEquiv`) is
  characterised levelwise by `z_v((f)_{ℚ_p}) = y_v(f)` in `ℂ_p`, `f ∈ A_v^∨`;
* **`dualTateZpEquiv_gal`**, **`dualTateZpEquiv'_gal`**: it is Galois-equivariant, both for the
  action `galTate` on `T_p(G_{ℚ_p}^∨) = (G_{ℚ_p})^∨`'s Tate module and for `galDualTate` on the
  second argument of the Cartier pairing (`dualTateZpEquiv'`);
* `instModuleZpDual`: the `ℤ_p`-module structure on `T_p(G^∨)(S)` for any `G`, `S`
  (`a · y = (y_v^{a mod p^v})_v`, as `instModuleZp` for Tate modules), and
  **`dualTateZpLinearEquiv`**, `dualTateZpLinearEquiv'`: `dualTateZpEquiv` is `ℤ_p`-linear;
* `DualTate.exists_pow_eq_of_val_eq_one_OC`: `y ∈ T_p(G^∨)(O_{ℂ_p})` with `y_v = 1` is a
  `p^v`-th power;
* **`PDivFGL.dalpha_zpSmul`**: `dα(z)(a · y) = a · dα(z)(y)` for `a ∈ ℤ_p` ([Hong, Prop. 3.4.9]:
  `dα` lands in `Hom_{ℤ_p}(T_p(G^∨), ℂ_p)`). Proof: for `n ≡ a mod p^v`, `(a·y) y^{-n}` is a
  `p^v`-th power, so by additivity `∂U_{a·y}(0) − a ∂U_y(0) ∈ p^v O_{ℂ_p}` for all `v`, and
  `O_{ℂ_p}` is `p`-adically separated.
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

section Gal

variable {p : ℕ} [hp : Fact p.Prime] (G : PDivGroup (ZpD p) p)

/-- **The Galois action on `T_p(G^∨)(O_{ℂ_p})`** for `G` over `ℤ_p`: `σ` acts on `O_{ℂ_p}` by
`ℤ_p`-algebra automorphisms (`PDivFGL.galS`; `ℤ_p` is fixed, `ZpD.galFixed`). -/
def galDualZp (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    G.DualTate (OCd p) →* G.DualTate (OCd p) where
  toFun y := ⟨fun v => (G.G v).dual.postComp (PDivFGL.galS σ (ZpD.galFixed σ)) (y.1 v),
    fun v => by
      beta_reduce
      rw [y.2 v]
      rfl⟩
  map_one' := by ext1; funext v; exact map_one _
  map_mul' x y := by ext1; funext v; exact map_mul _ _ _

theorem galDualZp_apply (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : G.DualTate (OCd p))
    (v : ℕ) (f : Cartier.Dual (ZpD p) (G.G v).A) :
    ((OCd.toOC (ofConv ((G.galDualZp σ y).1 v) f) : OC p) : ℂ_[p]) =
      autCp σ ((OCd.toOC (ofConv (y.1 v) f) : OC p) : ℂ_[p]) :=
  PDivFGL.galS_apply σ (ZpD.galFixed σ) _

theorem dualTateZpEquiv_val (y : G.DualTate (OCd p)) (v : ℕ) :
    letI := algebraCpOfOC (p := p) (ZpD p)
    (G.dualTateZpEquiv y).1 v = ((G.G v).dualBaseChangePointsEquiv (S := ℚ_[p])).symm
      ((G.dualPointsQbarCp v).symm ((G.G v).dual.pointsOCEquiv (p := p) (y.1 v))) :=
  rfl

/-- **Levelwise description of `dualTateZpEquiv`**: `z_v(f_{ℚ_p}) = y_v(f)` in `ℂ_p`. -/
theorem dualTateZpEquiv_spec (y : G.DualTate (OCd p)) (v : ℕ)
    (f : Cartier.Dual (ZpD p) (G.G v).A) :
    ((ofConv ((G.dualTateZpEquiv y).1 v) ((G.G v).dualBC (S := ℚ_[p]) f) : PadicAlgCl p) :
      ℂ_[p]) = ((OCd.toOC (ofConv (y.1 v) f) : OC p) : ℂ_[p]) := by
  letI := algebraCpOfOC (p := p) (ZpD p)
  have h1 : (G.G v).dualBaseChangePointsEquiv (S := ℚ_[p]) ((G.dualTateZpEquiv y).1 v) =
      (G.dualPointsQbarCp v).symm ((G.G v).dual.pointsOCEquiv (p := p) (y.1 v)) := by
    rw [dualTateZpEquiv_val, MulEquiv.apply_symm_apply]
  have h2 := congrArg (fun χ : (G.G v).dual.points ℂ_[p] => ofConv χ f)
    (MulEquiv.apply_symm_apply (G.dualPointsQbarCp v)
      ((G.G v).dual.pointsOCEquiv (p := p) (y.1 v)))
  change ZpD.qbarToCp (ofConv ((G.G v).dualBaseChangePointsEquiv (S := ℚ_[p])
    ((G.dualTateZpEquiv y).1 v)) f) = _
  rw [h1]
  exact h2

/-- `dualTateZpEquiv` is determined levelwise by `dualTateZpEquiv_spec`. -/
theorem dualTateZpEquiv_val_eq (y : G.DualTate (OCd p)) (v : ℕ)
    (z : ((G.G v).baseChange ℚ_[p]).dual.points (PadicAlgCl p))
    (h : ∀ f : Cartier.Dual (ZpD p) (G.G v).A,
      ((ofConv z ((G.G v).dualBC (S := ℚ_[p]) f) : PadicAlgCl p) : ℂ_[p]) =
        ((OCd.toOC (ofConv (y.1 v) f) : OC p) : ℂ_[p])) :
    (G.dualTateZpEquiv y).1 v = z := by
  apply ((G.G v).dualBaseChangePointsEquiv (S := ℚ_[p]) (T := PadicAlgCl p)).injective
  apply WithConv.ofConv_injective
  refine AlgHom.ext fun f => (algebraMap (PadicAlgCl p) ℂ_[p]).injective ?_
  exact (G.dualTateZpEquiv_spec y v f).trans (h f).symm

/-- The level-`v` component of `dualTateZpEquiv y` only depends on `y_v`. -/
theorem dualTateZpEquiv_val_congr {y y' : G.DualTate (OCd p)} {v : ℕ} (h : y.1 v = y'.1 v) :
    (G.dualTateZpEquiv y).1 v = (G.dualTateZpEquiv y').1 v :=
  G.dualTateZpEquiv_val_eq y v _ fun f => (G.dualTateZpEquiv_spec y' v f).trans (by rw [h])

theorem dualTateZpEquiv_gal_val (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (y : G.DualTate (OCd p)) (v : ℕ) :
    (G.dualTateZpEquiv (G.galDualZp σ y)).1 v =
      galPoints ((G.G v).baseChange ℚ_[p]).dual σ ((G.dualTateZpEquiv y).1 v) := by
  refine G.dualTateZpEquiv_val_eq _ v _ fun f => ?_
  exact ((autCp_coe σ _).symm.trans (congrArg (autCp σ) (G.dualTateZpEquiv_spec y v f))).trans
    (G.galDualZp_apply σ y v f).symm

/-- **Galois equivariance of `T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G_{ℚ_p}^∨)(ℚ̄_p)`.** -/
theorem dualTateZpEquiv_gal (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (y : G.DualTate (OCd p)) :
    G.dualTateZpEquiv (G.galDualZp σ y) =
      (G.baseChange ℚ_[p]).dualPDiv.galTate σ (G.dualTateZpEquiv y) :=
  Subtype.ext (funext fun v => G.dualTateZpEquiv_gal_val σ y v)

/-- `dualTateZpEquiv` with target the second argument `DualTate` of the Cartier pairing
`tatePairingZp` of `G_{ℚ_p}`. -/
def dualTateZpEquiv' :
    G.DualTate (OCd p) ≃* (G.baseChange ℚ_[p]).DualTate (PadicAlgCl p) :=
  G.dualTateZpEquiv.trans
    (MulEquiv.subgroupCongr ((G.baseChange ℚ_[p]).tateModule_dualPDiv (PadicAlgCl p)))

theorem dualTateZpEquiv'_val (y : G.DualTate (OCd p)) (v : ℕ) :
    (G.dualTateZpEquiv' y).1 v = (G.dualTateZpEquiv y).1 v := rfl

/-- **Galois equivariance**, with `galDualTate` on the target. -/
theorem dualTateZpEquiv'_gal (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (y : G.DualTate (OCd p)) :
    G.dualTateZpEquiv' (G.galDualZp σ y) =
      (G.baseChange ℚ_[p]).galDualTate σ (G.dualTateZpEquiv' y) :=
  Subtype.ext (funext fun v => G.dualTateZpEquiv_gal_val σ y v)

/-! ### `ℤ_p`-linearity -/

local instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- **`T_p(G^∨)(O_{ℂ_p}) ≃ T_p(G_{ℚ_p}^∨)(ℚ̄_p)` is `ℤ_p`-linear.** -/
def dualTateZpLinearEquiv : Additive (G.DualTate (OCd p)) ≃ₗ[ℤ_[p]]
    Additive ((G.baseChange ℚ_[p]).dualPDiv.TateModule (PadicAlgCl p)) :=
  AddEquiv.toLinearEquiv (MulEquiv.toAdditive G.dualTateZpEquiv) fun a y =>
    (G.baseChange ℚ_[p]).dualPDiv.addTate_ext _ fun v => by
      rw [smul_val]
      change (G.dualTateZpEquiv (Additive.toMul (a • y))).1 v =
        (G.dualTateZpEquiv (Additive.toMul y)).1 v ^ expo a v
      rw [G.dualTateZpEquiv_val_congr (y' := Additive.toMul y ^ expo a v) (v := v)
        (by rw [pi_subgroup_pow_val]; rfl), map_pow, pi_subgroup_pow_val]

theorem dualTateZpLinearEquiv_apply (y : Additive (G.DualTate (OCd p))) :
    Additive.toMul (G.dualTateZpLinearEquiv y) = G.dualTateZpEquiv (Additive.toMul y) := rfl

/-- **`dualTateZpEquiv'` is `ℤ_p`-linear.** -/
def dualTateZpLinearEquiv' : Additive (G.DualTate (OCd p)) ≃ₗ[ℤ_[p]]
    Additive ((G.baseChange ℚ_[p]).DualTate (PadicAlgCl p)) :=
  AddEquiv.toLinearEquiv (MulEquiv.toAdditive G.dualTateZpEquiv') fun a y =>
    (G.baseChange ℚ_[p]).addDualTate_ext _ fun v => by
      rw [dualSmul_val]
      change (G.dualTateZpEquiv (Additive.toMul (a • y))).1 v =
        (G.dualTateZpEquiv (Additive.toMul y)).1 v ^ expo a v
      rw [G.dualTateZpEquiv_val_congr (y' := Additive.toMul y ^ expo a v) (v := v)
        (by rw [pi_subgroup_pow_val]; rfl), map_pow, pi_subgroup_pow_val]

theorem dualTateZpLinearEquiv'_apply (y : Additive (G.DualTate (OCd p))) :
    Additive.toMul (G.dualTateZpLinearEquiv' y) = G.dualTateZpEquiv' (Additive.toMul y) := rfl

end Gal

end PDivGroup

/-! ### `p`-divisible formal group laws over `ℤ_p` -/

namespace PDivFGL

open PDivGroup

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} (P : PDivFGL (ZpD p) d p)

local instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- For `G = F[p^∞]`, the Galois action `galDual` of `AlphaGal.lean` is `galDualZp`. -/
theorem galDual_eq_galDualZp (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hR : ∀ r : ZpD p, autCp σ ((algebraMap (ZpD p) (OC p) r : OC p) : ℂ_[p]) =
      algebraMap (ZpD p) (OC p) r) (y : P.pdivGroup.DualTate (OCd p)) :
    P.galDual σ hR y = P.pdivGroup.galDualZp σ y := rfl

/-- **Galois equivariance of `dualTateZpEquiv` for `G = F[p^∞]`**, with the action `galDual` used
in `alphaZp_gal`. -/
theorem dualTateZpEquiv_galDual (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (y : P.pdivGroup.DualTate (OCd p)) :
    P.pdivGroup.dualTateZpEquiv' (P.galDual σ (ZpD.galFixed σ) y) =
      (P.pdivGroup.baseChange ℚ_[p]).galDualTate σ (P.pdivGroup.dualTateZpEquiv' y) :=
  P.pdivGroup.dualTateZpEquiv'_gal σ y

theorem dU_one (j : Fin d) : P.dU ZpD.p_mem 1 j = 0 := by
  have h := P.dU_mul ZpD.p_mem 1 1 j
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem dU_pow (y : P.pdivGroup.DualTate (OCd p)) (n : ℕ) (j : Fin d) :
    P.dU ZpD.p_mem (y ^ n) j = n • P.dU ZpD.p_mem y j := by
  induction n with
  | zero => rw [pow_zero, dU_one, zero_smul]
  | succ n ih => rw [pow_succ, dU_mul, ih, succ_nsmul]

/-- **`∂U_{a·y}/∂T_j(0) = a ∂U_y/∂T_j(0)`** for `a ∈ ℤ_p`. -/
theorem dU_smul (a : ℤ_[p]) (y : P.pdivGroup.DualTate (OCd p)) (j : Fin d) :
    P.dU ZpD.p_mem (Additive.toMul (a • Additive.ofMul y)) j =
      algebraMap (ZpD p) (OCd p) a * P.dU ZpD.p_mem y j := by
  set 𝔞 := (maximalIdeal (ZpD p)).map (algebraMap (ZpD p) (OCd p))
  have hp𝔞 : (p : OCd p) ∈ 𝔞 := by
    rw [← map_natCast (algebraMap (ZpD p) (OCd p))]
    exact Ideal.mem_map_of_mem _ ZpD.p_mem
  refine (IsHausdorff.eq_iff_smodEq (I := 𝔞)).mpr fun v => ?_
  simp only [smul_eq_mul, Ideal.mul_top]
  rw [SModEq.sub_mem]
  set n := expo a v
  set y' := Additive.toMul (a • Additive.ofMul y)
  -- `a = n + p^v b`
  obtain ⟨b, hb⟩ : ∃ b : ZpD p, b * (p : ZpD p) ^ v = (show ZpD p from a) - (n : ZpD p) := by
    have hk : a - (n : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) v) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow] at hk
    exact Ideal.mem_span_singleton'.mp hk
  have hA : algebraMap (ZpD p) (OCd p) a =
      (n : OCd p) + (p : OCd p) ^ v * algebraMap (ZpD p) (OCd p) b := by
    have := congrArg (algebraMap (ZpD p) (OCd p)) hb
    rw [map_mul, map_pow, map_natCast, map_sub, map_natCast] at this
    linear_combination -this
  -- `y' y^{-n}` is a `p^v`-th power
  set z := y' * (y ^ n)⁻¹
  have hz : z.1 v = 1 := by
    change y.1 v ^ n * ((y ^ n)⁻¹ : P.pdivGroup.DualTate (OCd p)).1 v = 1
    rw [InvMemClass.coe_inv, Pi.inv_apply, pi_subgroup_pow_val, mul_inv_cancel]
  obtain ⟨w, hw⟩ : ∃ w : P.pdivGroup.DualTate (OCd p), w ^ (p ^ v) = z :=
    DualTate.exists_pow_eq_of_val_eq_one_OC P.pdivGroup v z hz
  have hy' : y' = y ^ n * z := by rw [mul_comm, inv_mul_cancel_right]
  have hdU : P.dU ZpD.p_mem y' j =
      (n : OCd p) * P.dU ZpD.p_mem y j + (p : OCd p) ^ v * P.dU ZpD.p_mem w j := by
    rw [hy', dU_mul, dU_pow, ← hw, dU_pow, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_pow]
  have key : P.dU ZpD.p_mem y' j - algebraMap (ZpD p) (OCd p) a * P.dU ZpD.p_mem y j =
      (p : OCd p) ^ v *
        (P.dU ZpD.p_mem w j - algebraMap (ZpD p) (OCd p) b * P.dU ZpD.p_mem y j) := by
    rw [hdU, hA]
    ring
  rw [key]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hp𝔞 v)

/-- **`dα` is `ℤ_p`-linear in `y`**: `dα(z)(a · y) = a · dα(z)(y)` ([Hong, Prop. 3.4.9]:
`dα(z) ∈ Hom_{ℤ_p}(T_p(G^∨), ℂ_p)`). -/
theorem dalpha_zpSmul (z : Fin d → ℂ_[p]) (a : ℤ_[p]) (y : P.pdivGroup.DualTate (OCd p)) :
    P.dalpha ZpD.p_mem z (Additive.toMul (a • Additive.ofMul y)) =
      (a : ℚ_[p]) • P.dalpha ZpD.p_mem z y := by
  rw [dalpha, dalpha, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dU_smul, Algebra.smul_def, map_mul, Subring.coe_mul, mul_assoc]
  rfl

end PDivFGL

end PadicHodge
