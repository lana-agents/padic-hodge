/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TatePerfect
import PadicHodge.GroupScheme.EtaleUnramified
import PadicHodge.HodgeTate.Basic

/-!
# The `ℤ_p`-module `T_p G` and the Galois representation `V_p G`

For a `p`-divisible group `G` over `R` and an `R`-algebra `S`, `T_p G(S) = lim G_v(S)` is a
`ℤ_p`-module: `a · (x_v)_v = (x_v^{a mod p^v})_v` (`instModuleZp`, on `Additive (T_p G(S))`).
For `G` over `ℚ_p`:

* `galLin σ`: the Galois action on `T_p G(ℚ̄_p)` is `ℤ_p`-linear;
* `phiLin`: `ℤ_p^h ≅ T_p G(ℚ̄_p)` as `ℤ_p`-modules (from `TateFree.lean`), so `T_p G(ℚ̄_p)` is
  free of rank `h` (`finrank_tate`);
* `tateRep L`: the representation `V_p G = ℚ_p ⊗_{ℤ_p} T_p G(ℚ̄_p)` of `G_L`, of dimension `h`
  (`finrank_tateRep`);
* `tateRep_baseChange_eq_one_of_isInertia`: for a `p`-divisible group over `ℤ_p` with étale
  layers, inertia acts trivially on `V_p` of the generic fibre (`EtaleUnramified.lean`).
-/

noncomputable section

open WithConv TensorProduct

namespace PadicHodge

universe u

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] {p : ℕ} [hp : Fact p.Prime] (G : PDivGroup R p)
  (S : Type u) [CommRing S] [Algebra R S]

/-- `x ↦ x^a` on the Tate module, for `a ∈ ℤ_p`. -/
def zpPow (a : ℤ_[p]) (x : G.TateModule S) : G.TateModule S :=
  ⟨fun v => x.1 v ^ expo a v, by
    intro v
    have hx : ((x.1 (v + 1)) ^ p) ^ (p ^ v) = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact G.pow_eq_one (v + 1) S _
    rw [map_pow, x.2 v, ← expo_succ a v, pow_mod_eq hx, ← pow_mul, ← pow_mul, mul_comm]⟩

theorem zpPow_val (a : ℤ_[p]) (x : G.TateModule S) (v : ℕ) :
    (G.zpPow S a x).1 v = x.1 v ^ expo a v := rfl

omit hp in
theorem addTate_ext {x y : Additive (G.TateModule S)}
    (h : ∀ v, (Additive.toMul x).1 v = (Additive.toMul y).1 v) : x = y :=
  Additive.toMul.injective (Subtype.ext (funext h))

/-- **`T_p G(S)` is a `ℤ_p`-module.** -/
instance instModuleZp : Module ℤ_[p] (Additive (G.TateModule S)) where
  smul a x := Additive.ofMul (G.zpPow S a (Additive.toMul x))
  one_smul x := G.addTate_ext S fun v => by
    change (Additive.toMul x).1 v ^ expo 1 v = _
    rw [expo, map_one, ZMod.val_one_eq_one_mod, pow_mod_eq (G.pow_eq_one v S _), pow_one]
  mul_smul a b x := G.addTate_ext S fun v => by
    change (Additive.toMul x).1 v ^ expo (a * b) v =
      ((Additive.toMul x).1 v ^ expo b v) ^ expo a v
    rw [expo, map_mul, ZMod.val_mul, pow_mod_eq (G.pow_eq_one v S _), ← pow_mul, mul_comm]
  smul_zero a := G.addTate_ext S fun v => by
    change (1 : (G.G v).points S) ^ expo a v = 1
    rw [one_pow]
  smul_add a x y := G.addTate_ext S fun v => by
    change ((Additive.toMul x).1 v * (Additive.toMul y).1 v) ^ expo a v =
      (Additive.toMul x).1 v ^ expo a v * (Additive.toMul y).1 v ^ expo a v
    rw [mul_pow]
  add_smul a b x := G.addTate_ext S fun v => by
    change (Additive.toMul x).1 v ^ expo (a + b) v =
      (Additive.toMul x).1 v ^ expo a v * (Additive.toMul x).1 v ^ expo b v
    rw [expo, map_add, ZMod.val_add, pow_mod_eq (G.pow_eq_one v S _), pow_add]
  zero_smul x := G.addTate_ext S fun v => by
    change (Additive.toMul x).1 v ^ expo 0 v = 1
    rw [expo, map_zero, ZMod.val_zero, pow_zero]

theorem smul_val (a : ℤ_[p]) (x : Additive (G.TateModule S)) (v : ℕ) :
    (Additive.toMul (a • x)).1 v = (Additive.toMul x).1 v ^ expo a v := rfl

/-- The coordinates `ℤ_p^h → T_p G(S)`, `c ↦ ∑ c_i t_i`, are `ℤ_p`-linear. -/
def phiLin {h : ℕ} (t : Fin h → G.TateModule S) :
    (Fin h → ℤ_[p]) →ₗ[ℤ_[p]] Additive (G.TateModule S) where
  toFun c := Additive.ofMul (G.phi S t (Multiplicative.ofAdd c))
  map_add' c c' := by
    rw [ofAdd_add, map_mul]
    rfl
  map_smul' a c := G.addTate_ext S fun v => by
    rw [RingHom.id_apply, smul_val]
    change G.phiLevel S t v _ = (G.phiLevel S t v _) ^ expo a v
    rw [phiLevel_apply, phiLevel_apply, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [toAdd_ofAdd, Pi.smul_apply, smul_eq_mul]
    rw [← pow_mul, map_mul, ZMod.val_mul, pow_mod_eq (G.pow_eq_one v S _), mul_comm]

end PDivGroup

namespace PDivGroup

open FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] (H : PDivGroup ℚ_[p] p)

theorem galTate_mul (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x : H.TateModule (PadicAlgCl p)) :
    H.galTate (σ * τ) x = H.galTate σ (H.galTate τ x) := rfl

theorem galTate_one (x : H.TateModule (PadicAlgCl p)) : H.galTate 1 x = x := rfl

/-- **The Galois action on `T_p G(ℚ̄_p)` is `ℤ_p`-linear.** -/
def galLin (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Additive (H.TateModule (PadicAlgCl p)) →ₗ[ℤ_[p]] Additive (H.TateModule (PadicAlgCl p)) where
  toFun x := Additive.ofMul (H.galTate σ (Additive.toMul x))
  map_add' x y := by
    change Additive.ofMul (H.galTate σ (Additive.toMul x * Additive.toMul y)) = _
    rw [map_mul]
    rfl
  map_smul' a x := H.addTate_ext _ fun v => by
    change galPoints (H.G v) σ ((Additive.toMul x).1 v ^ expo a v) =
      (galPoints (H.G v) σ ((Additive.toMul x).1 v)) ^ expo a v
    rw [map_pow]

local instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- **`T_p G(ℚ̄_p) ≅ ℤ_p^h` as `ℤ_p`-modules.** -/
theorem nonempty_tateLinearEquiv :
    Nonempty ((Fin H.height → ℤ_[p]) ≃ₗ[ℤ_[p]] Additive (H.TateModule (PadicAlgCl p))) := by
  obtain ⟨t, -, hphi⟩ := H.exists_tateBasis
  refine ⟨LinearEquiv.ofBijective (H.phiLin _ t) ⟨fun c c' h => ?_, fun x => ?_⟩⟩
  · have := hphi.1 (congrArg Additive.toMul h)
    exact Multiplicative.ofAdd.injective this
  · obtain ⟨c, hc⟩ := hphi.2 (Additive.toMul x)
    exact ⟨Multiplicative.toAdd c, congrArg Additive.ofMul hc⟩

instance : Module.Free ℤ_[p] (Additive (H.TateModule (PadicAlgCl p))) :=
  Module.Free.of_equiv H.nonempty_tateLinearEquiv.some

instance : Module.Finite ℤ_[p] (Additive (H.TateModule (PadicAlgCl p))) :=
  Module.Finite.equiv H.nonempty_tateLinearEquiv.some

/-- `T_p G(ℚ̄_p)` is free of rank `h`. -/
theorem finrank_tate :
    Module.finrank ℤ_[p] (Additive (H.TateModule (PadicAlgCl p))) = H.height := by
  rw [← H.nonempty_tateLinearEquiv.some.finrank_eq, Module.finrank_fin_fun]

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- **The Galois representation `V_p G = ℚ_p ⊗_{ℤ_p} T_p G(ℚ̄_p)` of `G_L`.** -/
def tateRep : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (ℚ_[p] ⊗[ℤ_[p]] Additive (H.TateModule (PadicAlgCl p))) where
  toFun σ := (H.galLin (σ.restrictScalars ℚ_[p])).baseChange ℚ_[p]
  map_one' := by
    have : H.galLin ((1 : PadicAlgCl p ≃ₐ[L] PadicAlgCl p).restrictScalars ℚ_[p]) =
        LinearMap.id := LinearMap.ext fun x => rfl
    rw [this, LinearMap.baseChange_id]
    rfl
  map_mul' σ τ := by
    have : H.galLin ((σ * τ).restrictScalars ℚ_[p]) =
        H.galLin (σ.restrictScalars ℚ_[p]) ∘ₗ H.galLin (τ.restrictScalars ℚ_[p]) :=
      LinearMap.ext fun x => rfl
    rw [this, LinearMap.baseChange_comp]
    rfl

/-- `dim_{ℚ_p} V_p G = h`. -/
theorem finrank_tateRep :
    Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (H.TateModule (PadicAlgCl p))) = H.height := by
  rw [Module.finrank_baseChange, finrank_tate]

/-- **`V_p` of (the generic fibre of) a `p`-divisible group over `ℤ_p` with étale layers is
unramified.** -/
theorem tateRep_baseChange_eq_one_of_isInertia (G : PDivGroup ℤ_[p] p)
    (hG : ∀ v, (G.G v).IsEtale) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (hσ : IsInertia (p := p) σ) : (G.baseChange ℚ_[p]).tateRep L σ = 1 := by
  have hσ' : IsInertia (p := p) (σ.restrictScalars ℚ_[p]) := hσ
  have : (G.baseChange ℚ_[p]).galLin (σ.restrictScalars ℚ_[p]) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    change Additive.ofMul ((G.baseChange ℚ_[p]).galTate (σ.restrictScalars ℚ_[p])
      (Additive.toMul x)) = x
    rw [G.galTate_baseChange_eq_of_isInertia hG _ hσ']
    rfl
  change LinearMap.baseChange ℚ_[p] _ = 1
  rw [this, LinearMap.baseChange_id]
  rfl

end PDivGroup

end PadicHodge
