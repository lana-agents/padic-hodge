/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TateMu
import PadicHodge.Cyclotomic.Character

/-!
# `T_p μ_{p^∞} ≅ ℤ_p(1)`

Over `ℚ̄_p` choose a compatible system `ε = (ε_v)` of primitive `p^v`-th roots of unity
(`ε_{v+1}^p = ε_v`, `eps`). Then `a ↦ (ε_v^{a mod p^v})_v` is an isomorphism
`ℤ_p ≅ RootSys p ℚ̄_p` (`rootSysEquiv`), hence (with `tateMuEquiv`)

* `tateMuZpEquiv : T_p μ_{p^∞}(ℚ̄_p) ≃* Multiplicative ℤ_p`,

and `σ ∈ Gal(ℚ̄_p/ℚ_p)` acts on it through the cyclotomic character:
`tateMuZpEquiv (σ • x) = χ(σ) · tateMuZpEquiv x` (`tateMuZpEquiv_gal`), i.e.
`T_p μ_{p^∞} ≅ ℤ_p(1)` as Galois modules ([BC, §2.2] for `ℤ_p(1)`).
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv

namespace PadicHodge

open FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime]

/-- A `p`-th root of a primitive `p^v`-th root of unity can be chosen primitive of order
`p^{v+1}` (for `v ≥ 1` every `p`-th root is). -/
theorem exists_root_step {v : ℕ} {x : PadicAlgCl p} (hx : IsPrimitiveRoot x (p ^ v)) :
    ∃ y : PadicAlgCl p, y ^ p = x ∧ IsPrimitiveRoot y (p ^ (v + 1)) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · obtain ⟨y, hy⟩ := exists_isPrimitiveRoot (p := p) 1
    refine ⟨y, ?_, by simpa using hy⟩
    rw [pow_zero] at hx
    rw [IsPrimitiveRoot.one_right_iff.mp hx]; simpa using hy.pow_eq_one
  · obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq x hp.out.pos
    refine ⟨y, hy, ?_⟩
    have hy1 : y ^ (p ^ (v + 1)) = 1 := by
      rw [pow_succ', pow_mul, hy, hx.pow_eq_one]
    obtain ⟨k, hk, hord⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hy1)
    rcases Nat.lt_or_ge k (v + 1) with hlt | hge
    · exfalso
      have h1 : y ^ (p ^ v) = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hord]; exact pow_dvd_pow p (by omega)
      have h2 : x ^ (p ^ (v - 1)) = 1 := by
        rw [← hy, ← pow_mul, ← pow_succ', show v - 1 + 1 = v by omega, h1]
      have := (hx.pow_eq_one_iff_dvd _).mp h2
      have h3 := Nat.le_of_dvd (pow_pos hp.out.pos _) this
      have h4 : p ^ (v - 1) < p ^ v := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
      omega
    · have hk' : k = v + 1 := le_antisymm hk hge
      rw [← hk', ← hord]
      exact IsPrimitiveRoot.orderOf y

/-- A compatible system of primitive `p^v`-th roots of unity. -/
def epsSub : (v : ℕ) → {x : PadicAlgCl p // IsPrimitiveRoot x (p ^ v)}
  | 0 => ⟨1, by rw [pow_zero]; exact IsPrimitiveRoot.one⟩
  | v + 1 => ⟨Classical.choose (exists_root_step (epsSub v).2),
      (Classical.choose_spec (exists_root_step (epsSub v).2)).2⟩

/-- `ε_v`. -/
def eps (v : ℕ) : PadicAlgCl p := (epsSub (p := p) v).1

theorem eps_prim (v : ℕ) : IsPrimitiveRoot (eps (p := p) v) (p ^ v) := (epsSub v).2

theorem eps_succ_pow (v : ℕ) : eps (p := p) (v + 1) ^ p = eps v :=
  (Classical.choose_spec (exists_root_step (epsSub (p := p) v).2)).1

/-- `a mod p^v ∈ [0, p^v)`. -/
abbrev expo (a : ℤ_[p]) (v : ℕ) : ℕ := (PadicInt.toZModPow v a).val

theorem expo_succ (a : ℤ_[p]) (v : ℕ) : expo a (v + 1) % p ^ v = expo a v := by
  rw [expo, expo, ← PadicInt.cast_toZModPow v (v + 1) (Nat.le_succ v) a, ZMod.cast_eq_val,
    ZMod.val_natCast]

theorem eps_pow_card (v : ℕ) : eps (p := p) v ^ (p ^ v) = 1 := (eps_prim v).pow_eq_one

theorem eps_pow_expo_add (a b : ℤ_[p]) (v : ℕ) :
    eps (p := p) v ^ expo (a + b) v = eps v ^ expo a v * eps v ^ expo b v := by
  rw [expo, map_add, ZMod.val_add, pow_mod_of_pow_eq_one (eps_pow_card v), pow_add]

theorem eps_pow_expo_compat (a : ℤ_[p]) (v : ℕ) :
    (eps (p := p) (v + 1) ^ expo a (v + 1)) ^ p = eps v ^ expo a v := by
  rw [← pow_mul, mul_comm, pow_mul, eps_succ_pow, ← expo_succ a v,
    pow_mod_of_pow_eq_one (eps_pow_card v)]

/-- The root of unity `ε_v^{a mod p^v}`. -/
def epsRoot (a : ℤ_[p]) (v : ℕ) : rootsOfUnity (p ^ v) (PadicAlgCl p) :=
  ⟨Units.ofPowEqOne (eps v ^ expo a v) (p ^ v)
    (by rw [← pow_mul, mul_comm, pow_mul, eps_pow_card, one_pow]) (NeZero.ne _), by
    rw [mem_rootsOfUnity]; ext
    simp only [Units.val_pow_eq_pow_val, Units.val_ofPowEqOne, Units.val_one]
    rw [← pow_mul, mul_comm, pow_mul, eps_pow_card, one_pow]⟩

theorem epsRoot_val (a : ℤ_[p]) (v : ℕ) :
    (((epsRoot a v : rootsOfUnity (p ^ v) (PadicAlgCl p)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      eps v ^ expo a v := rfl

/-- `ℤ_p → RootSys p ℚ̄_p`, `a ↦ (ε_v^{a mod p^v})_v`. -/
def rootSysHom : Multiplicative ℤ_[p] →* RootSys p (PadicAlgCl p) where
  toFun a := ⟨fun v => epsRoot (Multiplicative.toAdd a) v, fun v => by
    ext; rw [Units.val_pow_eq_pow_val, epsRoot_val, epsRoot_val, eps_pow_expo_compat]⟩
  map_one' := by
    apply Subtype.ext; funext v; apply Subtype.ext; apply Units.ext
    change eps v ^ expo 0 v = 1
    rw [expo, map_zero, ZMod.val_zero, pow_zero]
  map_mul' a b := by
    apply Subtype.ext; funext v; apply Subtype.ext; apply Units.ext
    change eps v ^ expo (Multiplicative.toAdd a + Multiplicative.toAdd b) v =
      eps v ^ expo (Multiplicative.toAdd a) v * eps v ^ expo (Multiplicative.toAdd b) v
    rw [eps_pow_expo_add]

theorem rootSysHom_injective : Function.Injective (rootSysHom (p := p)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h : ∀ v, PadicInt.toZModPow v (Multiplicative.toAdd a) = 0 := by
    intro v
    have := congrArg (fun ζ : RootSys p (PadicAlgCl p) =>
      (((ζ : (v : ℕ) → rootsOfUnity (p ^ v) (PadicAlgCl p)) v : (PadicAlgCl p)ˣ) :
        PadicAlgCl p)) ha
    change eps v ^ expo (Multiplicative.toAdd a) v = 1 at this
    rw [(eps_prim v).pow_eq_one_iff_dvd] at this
    rw [← ZMod.val_eq_zero]
    exact Nat.eq_zero_of_dvd_of_lt this (ZMod.val_lt _)
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact PadicInt.ext_of_toZModPow.mp fun v => by rw [h v, map_zero]

theorem rootSysHom_surjective : Function.Surjective (rootSysHom (p := p)) := by
  intro ζ
  have hζ : ∀ v, (((ζ : (v : ℕ) → rootsOfUnity (p ^ v) (PadicAlgCl p)) v : (PadicAlgCl p)ˣ) :
      PadicAlgCl p) ^ (p ^ v) = 1 := fun v => by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp
      ((ζ : (v : ℕ) → rootsOfUnity (p ^ v) (PadicAlgCl p)) v).2, Units.val_one]
  choose k hk hkeq using fun v => (eps_prim (p := p) v).eq_pow_of_pow_eq_one (hζ v)
  -- compatibility of the exponents
  have hcompat : ∀ v, (p : ℤ) ^ v ∣ (k (v + 1) : ℤ) - k v := by
    intro v
    have h1 := ζ.2 v
    have h2 : eps (p := p) v ^ k v = eps v ^ k (v + 1) := by
      rw [hkeq v, ← eps_succ_pow, ← pow_mul, mul_comm, pow_mul, hkeq (v + 1)]
      have := congrArg (fun u : (PadicAlgCl p)ˣ => (u : PadicAlgCl p)) h1
      simpa using this
    rw [pow_eq_pow_iff_of_prim (eps_prim v) (pow_pos hp.out.pos _)] at h2
    have := (Nat.modEq_iff_dvd.mp h2)
    exact_mod_cast this
  set a := PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
    (fun v => (k v : ℤ)) p hcompat)
  refine ⟨Multiplicative.ofAdd a, ?_⟩
  apply Subtype.ext; funext v; apply Subtype.ext; apply Units.ext
  change eps v ^ expo a v = _
  rw [expo, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub, Int.cast_natCast,
    ZMod.val_natCast, Nat.mod_eq_of_lt (hk v), hkeq v]
  exact hcompat

/-- `RootSys p ℚ̄_p ≃* ℤ_p`. -/
def rootSysEquiv : Multiplicative ℤ_[p] ≃* RootSys p (PadicAlgCl p) :=
  MulEquiv.ofBijective rootSysHom ⟨rootSysHom_injective, rootSysHom_surjective⟩

/-- **`T_p μ_{p^∞}(ℚ̄_p) ≅ ℤ_p`.** -/
def tateMuZpEquiv :
    (muPDiv ℚ_[p] p).TateModule (PadicAlgCl p) ≃* Multiplicative ℤ_[p] :=
  (tateMuEquiv p (PadicAlgCl p) ℚ_[p]).trans rootSysEquiv.symm

/-! ### The Galois action -/

/-- `σ ∈ Gal(ℚ̄_p/K)` acting on points: `φ ↦ σ ∘ φ`, for `G` over a field `K ⊆ ℚ̄_p` (e.g.
`ℚ_p`). -/
def galPoints {K : Type} [Field K] [Algebra K (PadicAlgCl p)] (G : FFGroupScheme K)
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :
    G.points (PadicAlgCl p) →* G.points (PadicAlgCl p) where
  toFun φ := toConv ((σ : PadicAlgCl p →ₐ[K] PadicAlgCl p).comp (ofConv φ))
  map_one' := by
    apply WithConv.ofConv_injective
    ext a
    simp [AlgHom.convOne_apply]
  map_mul' φ ψ := by
    apply WithConv.ofConv_injective
    exact AlgHom.comp_convMul_distrib _ _ _

theorem galPoints_val (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (v : ℕ)
    (x : (muP ℚ_[p] p v).points (PadicAlgCl p)) :
    (((muPointsEquiv p (PadicAlgCl p) ℚ_[p] v (galPoints (muP ℚ_[p] p v) σ x) :
      rootsOfUnity (p ^ v) (PadicAlgCl p)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      σ (((muPointsEquiv p (PadicAlgCl p) ℚ_[p] v x : rootsOfUnity (p ^ v) (PadicAlgCl p)) :
        (PadicAlgCl p)ˣ) : PadicAlgCl p) := by
  change (ofConv (galPoints (muP ℚ_[p] p v) σ x)) (MonoidAlgebra.single (genP p v) 1) =
    σ ((ofConv x) (MonoidAlgebra.single (genP p v) 1))
  rfl

/-- The Galois action on `T_p μ_{p^∞}(ℚ̄_p)`. -/
def galTate (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    (muPDiv ℚ_[p] p).TateModule (PadicAlgCl p) →* (muPDiv ℚ_[p] p).TateModule (PadicAlgCl p) where
  toFun x := ⟨fun v => galPoints (muP ℚ_[p] p v) σ (x.1 v), fun v => by
    have h := x.2 v
    change (galPoints (muP ℚ_[p] p (v + 1)) σ) ((muIncl ℚ_[p] p v).mapPoints _ (x.1 v)) =
      (galPoints (muP ℚ_[p] p (v + 1)) σ (x.1 (v + 1))) ^ p
    rw [← map_pow]
    exact congrArg (galPoints (muP ℚ_[p] p (v + 1)) σ) h⟩
  map_one' := by ext1; funext v; exact map_one _
  map_mul' x y := by ext1; funext v; exact map_mul _ _ _

theorem gal_eps_pow (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (a : ℤ_[p]) (v : ℕ) :
    σ (eps v ^ expo a v) = eps v ^ expo (((chi σ : ℤ_[p]ˣ) : ℤ_[p]) * a) v := by
  have ht : (eps (p := p) v ^ expo a v) ^ (p ^ v) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, eps_pow_card, one_pow]
  rw [chi_spec σ ht, ← pow_mul, expo, expo, map_mul, ZMod.val_mul,
    pow_mod_of_pow_eq_one (eps_pow_card v), mul_comm]

theorem tateMuEquiv_eq_rootSysHom (x : (muPDiv ℚ_[p] p).TateModule (PadicAlgCl p)) :
    tateMuEquiv p (PadicAlgCl p) ℚ_[p] x = rootSysHom (tateMuZpEquiv x) := by
  change _ = rootSysEquiv (rootSysEquiv.symm (tateMuEquiv p (PadicAlgCl p) ℚ_[p] x))
  rw [MulEquiv.apply_symm_apply]

/-- **`T_p μ_{p^∞} ≅ ℤ_p(1)`**: `σ` acts on `T_p μ_{p^∞}(ℚ̄_p) ≅ ℤ_p` by multiplication by
`χ(σ)`. -/
theorem tateMuZpEquiv_gal (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x : (muPDiv ℚ_[p] p).TateModule (PadicAlgCl p)) :
    tateMuZpEquiv (galTate σ x) = Multiplicative.ofAdd (((chi σ : ℤ_[p]ˣ) : ℤ_[p]) *
      Multiplicative.toAdd (tateMuZpEquiv x)) := by
  apply rootSysEquiv.injective
  change rootSysEquiv (rootSysEquiv.symm (tateMuEquiv p (PadicAlgCl p) ℚ_[p] (galTate σ x))) = _
  rw [MulEquiv.apply_symm_apply]
  have hx := tateMuEquiv_eq_rootSysHom x
  apply Subtype.ext; funext v; apply Subtype.ext; apply Units.ext
  have hv := congrArg (fun ζ : RootSys p (PadicAlgCl p) =>
    (((ζ : (v : ℕ) → rootsOfUnity (p ^ v) (PadicAlgCl p)) v : (PadicAlgCl p)ˣ) :
      PadicAlgCl p)) hx
  change (((muPointsEquiv p (PadicAlgCl p) ℚ_[p] v (galPoints (muP ℚ_[p] p v) σ (x.1 v)) :
      rootsOfUnity (p ^ v) (PadicAlgCl p)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
    eps v ^ expo (((chi σ : ℤ_[p]ˣ) : ℤ_[p]) * Multiplicative.toAdd (tateMuZpEquiv x)) v
  rw [galPoints_val, ← gal_eps_pow]
  congr 1

end PadicHodge
