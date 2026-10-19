/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cohomology.ContH1
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Kummer maps into continuous `H¹` with coefficients in a Tate module

Let `Γ` be a topological group acting `ℤ`-linearly on an abelian group `M`
(`ρ : Representation ℤ Γ M`; no topology on `M`), and `p` a natural number.

* `Kummer.Tp M p = T_p M = lim_n M[p^n]`: the sequences `(x_n)` with `x_0 = 0` and
  `p · x_{n+1} = x_n`, with the inverse limit topology of the discrete groups `M[p^n]`
  (`IsTopologicalAddGroup`); `Kummer.tpRep ρ p` is the induced action of `Γ`.
* `ContH1.map` (coefficients) and `ContH1.comap` (pull-back along a continuous homomorphism
  `Γ' → Γ`) on continuous `H¹`.
* **`Kummer.kummer`**: if `M` is `p`-divisible and the `p`-th roots of points with open
  stabiliser have open stabilisers (`StabHyp`), the Kummer map
  `M^Γ → H¹_cont(Γ, T_p M)`, `x ↦ [σ ↦ (σ x_n - x_n)_n]` for any compatible system of
  `p`-power roots `(x_n)` of `x` (`IsDivSeq`); it is independent of the system
  (`kummer_eq`) and additive.
* **Functoriality**: `map_kummer` (for `Γ`-equivariant homomorphisms `M → N`) and
  `comap_kummer` (for continuous homomorphisms `Γ' → Γ`, e.g. the inclusion `G_{K''} ⊆ G_{K'}`
  for a finite extension `K''/K'`).
* `stabHyp_of_finite`: `StabHyp` holds if `Γ` is compact, all stabilisers are closed and
  `M[p]` is finite (the case of formal groups over `O_{K'}`, `FormalGroup/Kummer.lean`).
-/

noncomputable section

open Topology

namespace PadicHodge

namespace ContH1

section Map

variable {R G M N : Type*} [CommRing R] [Group G] [TopologicalSpace G]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [ContinuousConstSMul R N]
  {ρ : Representation R G M} {ρ' : Representation R G N}

/-- Cocycles along an equivariant continuous linear map of coefficients. -/
def mapCocycles (φ : M →ₗ[R] N) (hφ : Continuous φ) (h : ∀ g m, φ (ρ g m) = ρ' g (φ m)) :
    cocycles ρ →ₗ[R] cocycles ρ' where
  toFun f := ⟨fun g => φ ((f : G → M) g), hφ.comp f.2.1, fun g g' => by
    dsimp only
    rw [f.2.2 g g', map_add, h]⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add φ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul φ _ _)

theorem mapCocycles_le (φ : M →ₗ[R] N) (hφ : Continuous φ) (h : ∀ g m, φ (ρ g m) = ρ' g (φ m)) :
    coboundaries ρ ≤ (coboundaries ρ').comap (mapCocycles φ hφ h) := by
  rintro f ⟨m, hm⟩
  refine ⟨φ m, fun g => ?_⟩
  change φ ((f : G → M) g) = _
  rw [hm g, map_sub, h]

/-- `H¹(G, M) → H¹(G, N)` for an equivariant continuous linear map `M → N`. -/
def map (φ : M →ₗ[R] N) (hφ : Continuous φ) (h : ∀ g m, φ (ρ g m) = ρ' g (φ m)) :
    H1 ρ →ₗ[R] H1 ρ' :=
  Submodule.mapQ _ _ (mapCocycles φ hφ h) (mapCocycles_le φ hφ h)

theorem map_mk (φ : M →ₗ[R] N) (hφ : Continuous φ) (h : ∀ g m, φ (ρ g m) = ρ' g (φ m))
    (f : cocycles ρ) : map φ hφ h (mk ρ f) = mk ρ' (mapCocycles φ hφ h f) := rfl

end Map

section Comap

variable {R G G' M : Type*} [CommRing R] [Group G] [TopologicalSpace G] [Group G']
  [TopologicalSpace G'] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M)

/-- Pull-back of cocycles along a continuous homomorphism `ψ : G' → G`. -/
def comapCocycles (ψ : G' →* G) (hψ : Continuous ψ) : cocycles ρ →ₗ[R] cocycles (ρ.comp ψ) where
  toFun f := ⟨fun g => (f : G → M) (ψ g), f.2.1.comp hψ, fun g g' => by
    dsimp only
    rw [map_mul, f.2.2]
    rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem comapCocycles_le (ψ : G' →* G) (hψ : Continuous ψ) :
    coboundaries ρ ≤ (coboundaries (ρ.comp ψ)).comap (comapCocycles ρ ψ hψ) := by
  rintro f ⟨m, hm⟩
  exact ⟨m, fun g => hm (ψ g)⟩

/-- `H¹(G, M) → H¹(G', M)` along a continuous homomorphism `ψ : G' → G` (restriction, if `ψ`
is the inclusion of a subgroup). -/
def comap (ψ : G' →* G) (hψ : Continuous ψ) : H1 ρ →ₗ[R] H1 (ρ.comp ψ) :=
  Submodule.mapQ _ _ (comapCocycles ρ ψ hψ) (comapCocycles_le ρ ψ hψ)

theorem comap_mk (ψ : G' →* G) (hψ : Continuous ψ) (f : cocycles ρ) :
    comap ρ ψ hψ (mk ρ f) = mk (ρ.comp ψ) (comapCocycles ρ ψ hψ f) := rfl

end Comap

end ContH1

namespace Kummer

section Tate

variable (M : Type*) [AddCommGroup M] (p : ℕ)

/-- The compatible systems `(x_n)` with `x_0 = 0` and `p · x_{n+1} = x_n`. -/
def tateSub : AddSubgroup (ℕ → M) where
  carrier := {x | x 0 = 0 ∧ ∀ n, p • x (n + 1) = x n}
  add_mem' := fun {x y} hx hy => ⟨by simp [hx.1, hy.1], fun n => by
    simp only [Pi.add_apply, smul_add, hx.2 n, hy.2 n]⟩
  zero_mem' := ⟨rfl, fun n => by simp⟩
  neg_mem' := fun {x} hx => ⟨by simp [hx.1], fun n => by
    simp only [Pi.neg_apply, smul_neg, hx.2 n]⟩

variable {M p} in
theorem mem_tateSub {x : ℕ → M} : x ∈ tateSub M p ↔ x 0 = 0 ∧ ∀ n, p • x (n + 1) = x n :=
  Iff.rfl

/-- **The Tate module** `T_p M = lim_n M[p^n]`, with the inverse limit topology of the discrete
groups `M[p^n]` (a type synonym of `tateSub M p`). -/
def Tp : Type _ := tateSub M p

instance : AddCommGroup (Tp M p) := inferInstanceAs (AddCommGroup (tateSub M p))

/-- The underlying sequence. -/
def val : Tp M p →+ (ℕ → M) := (tateSub M p).subtype

variable {M p}

theorem val_mem (x : Tp M p) : val M p x ∈ tateSub M p := (x : tateSub M p).2

theorem val_zero (x : Tp M p) : val M p x 0 = 0 := (val_mem x).1

theorem val_succ (x : Tp M p) (n : ℕ) : p • val M p x (n + 1) = val M p x n := (val_mem x).2 n

theorem val_injective : Function.Injective (val M p) := Subtype.val_injective

@[ext] theorem ext {x y : Tp M p} (h : ∀ n, val M p x n = val M p y n) : x = y :=
  val_injective (funext h)

/-- The element of `T_p M` given by a compatible system. -/
def mk (x : ℕ → M) (hx : x ∈ tateSub M p) : Tp M p := (⟨x, hx⟩ : tateSub M p)

@[simp] theorem val_mk (x : ℕ → M) (hx : x ∈ tateSub M p) : val M p (mk x hx) = x := rfl

variable (M p)

/-- The inverse limit topology: induced from `∏_n M` with `M` discrete. -/
instance : TopologicalSpace (Tp M p) :=
  TopologicalSpace.induced (val M p) (@Pi.topologicalSpace ℕ (fun _ => M) fun _ => ⊥)

instance : IsTopologicalAddGroup (Tp M p) := by
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  exact topologicalAddGroup_induced (val M p)

instance : ContinuousConstSMul ℤ (Tp M p) :=
  ⟨fun c => (continuous_zsmul c : Continuous fun x : Tp M p => c • x)⟩

variable {M p}

/-- **Continuity into `T_p M`**: it suffices that all fibres of all coordinates are open. -/
theorem continuous_of_isOpen {X : Type*} [TopologicalSpace X] {f : X → Tp M p}
    (hf : ∀ n m, IsOpen {a | val M p (f a) n = m}) : Continuous f := by
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  refine continuous_induced_rng.2 (continuous_pi fun n => ?_)
  refine continuous_discrete_rng.2 fun m => ?_
  exact hf n m

/-- A homomorphism `M → N` induces a continuous homomorphism `T_p M → T_p N`. -/
def map {N : Type*} [AddCommGroup N] (f : M →+ N) : Tp M p →ₗ[ℤ] Tp N p :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => mk (fun n => f (val M p x n))
        ⟨by dsimp only; rw [val_zero, map_zero], fun n => by dsimp only; rw [← map_nsmul, val_succ]⟩
      map_zero' := ext fun n => by simp
      map_add' := fun x y => ext fun n => by simp }

@[simp] theorem val_map {N : Type*} [AddCommGroup N] (f : M →+ N) (x : Tp M p) (n : ℕ) :
    val N p (map f x) n = f (val M p x n) := rfl

theorem isOpen_val_eq {x : Tp M p} {n : ℕ} :
    IsOpen {y : Tp M p | val M p y n = val M p x n} := by
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hc : Continuous fun y : Tp M p => val M p y n :=
    (continuous_apply n).comp continuous_induced_dom
  exact hc.isOpen_preimage {val M p x n} (isOpen_discrete _)

theorem continuous_map {N : Type*} [AddCommGroup N] (f : M →+ N) :
    Continuous (map (p := p) f) := by
  refine continuous_of_isOpen fun n m => ?_
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  exact ⟨_, fun y (hy : val M p y n = val M p x n) => by
    change f (val M p y n) = m
    rw [hy]
    exact hx, isOpen_val_eq, rfl⟩

end Tate

section Rep

variable {Γ M : Type*} [Group Γ] [AddCommGroup M] (ρ : Representation ℤ Γ M) (p : ℕ)

/-- The action of `Γ` on `T_p M`. -/
def tpRep : Representation ℤ Γ (Tp M p) where
  toFun σ := map (ρ σ).toAddMonoidHom
  map_one' := LinearMap.ext fun x => ext fun n => by simp
  map_mul' σ τ := LinearMap.ext fun x => ext fun n => by simp

@[simp] theorem val_tpRep (σ : Γ) (x : Tp M p) (n : ℕ) :
    val M p (tpRep ρ p σ x) n = ρ σ (val M p x n) := rfl

theorem tpRep_comp {Γ' : Type*} [Group Γ'] (ψ : Γ' →* Γ) :
    tpRep (ρ.comp ψ) p = (tpRep ρ p).comp ψ :=
  rfl

/-- The stabiliser of a point. -/
def stab (z : M) : Subgroup Γ where
  carrier := {σ | ρ σ z = z}
  mul_mem' := fun {σ τ} (hσ : ρ σ z = z) (hτ : ρ τ z = z) => by
    change ρ (σ * τ) z = z
    rw [map_mul, Module.End.mul_apply, hτ, hσ]
  one_mem' := by
    change ρ 1 z = z
    rw [map_one, Module.End.one_apply]
  inv_mem' := fun {σ} (hσ : ρ σ z = z) => by
    change ρ σ⁻¹ z = z
    conv_lhs => rw [← hσ]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_stab {z : M} {σ : Γ} : σ ∈ stab ρ z ↔ ρ σ z = z := Iff.rfl

theorem stab_comp {Γ' : Type*} [Group Γ'] (ψ : Γ' →* Γ) (z : M) :
    stab (ρ.comp ψ) z = (stab ρ z).comap ψ := rfl

/-- `x` is invariant iff its stabiliser is everything. -/
theorem stab_eq_top {x : M} (hx : x ∈ ρ.invariants) : stab ρ x = ⊤ :=
  eq_top_iff.mpr fun σ _ => hx σ

/-- A compatible system of `p`-power roots of `x` with open stabilisers. -/
structure IsDivSeq [TopologicalSpace Γ] (x : M) (s : ℕ → M) : Prop where
  zero : s 0 = x
  succ : ∀ n, p • s (n + 1) = s n
  isOpen : ∀ n, IsOpen (stab ρ (s n) : Set Γ)

/-- The hypothesis on stabilisers needed to construct `p`-power roots with open stabilisers. -/
def StabHyp [TopologicalSpace Γ] : Prop :=
  ∀ x z : M, IsOpen (stab ρ x : Set Γ) → p • z = x → IsOpen (stab ρ z : Set Γ)

variable [TopologicalSpace Γ] [IsTopologicalGroup Γ]

variable {ρ p}

/-- The orbit map of a point with open stabiliser has open fibres. -/
theorem isOpen_orbit_fibre {z : M} (hz : IsOpen (stab ρ z : Set Γ)) (m : M) :
    IsOpen {σ : Γ | ρ σ z = m} := by
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ * τ) '' (stab ρ z : Set Γ), ?_, (Homeomorph.mulLeft σ).isOpenMap _ hz,
    ⟨1, (stab ρ z).one_mem, mul_one σ⟩⟩
  rintro _ ⟨τ, hτ, rfl⟩
  change ρ (σ * τ) z = m
  rw [map_mul, Module.End.mul_apply, (mem_stab ρ).mp hτ]
  exact hσ

omit [IsTopologicalGroup Γ] in
theorem exists_isDivSeq (hdiv : ∀ y : M, ∃ z, p • z = y) (hst : StabHyp ρ p) {x : M}
    (hx : x ∈ ρ.invariants) : ∃ s, IsDivSeq ρ p x s := by
  choose r hr using hdiv
  set s : ℕ → M := fun n => Nat.rec x (fun _ y => r y) n with hs
  have hopen : ∀ n, IsOpen (stab ρ (s n) : Set Γ) := by
    intro n
    induction n with
    | zero =>
      change IsOpen (stab ρ x : Set Γ)
      rw [stab_eq_top ρ hx]
      exact isOpen_univ
    | succ n ih => exact hst (s n) (s (n + 1)) ih (hr (s n))
  exact ⟨s, ⟨rfl, fun n => hr (s n), hopen⟩⟩

/-- The Kummer cocycle `σ ↦ (σ x_n - x_n)_n` of a compatible system of roots. -/
def cocycleFun {x : M} (hx : x ∈ ρ.invariants) {s : ℕ → M} (hs : IsDivSeq ρ p x s) (σ : Γ) :
    Tp M p :=
  mk (fun n => ρ σ (s n) - s n) ⟨by dsimp only; rw [hs.zero, hx σ, sub_self], fun n => by
    dsimp only; rw [smul_sub, ← map_nsmul, hs.succ]⟩

omit [IsTopologicalGroup Γ] in
@[simp] theorem val_cocycleFun {x : M} (hx : x ∈ ρ.invariants) {s : ℕ → M}
    (hs : IsDivSeq ρ p x s) (σ : Γ) (n : ℕ) :
    val M p (cocycleFun hx hs σ) n = ρ σ (s n) - s n := rfl

theorem cocycleFun_mem {x : M} (hx : x ∈ ρ.invariants) {s : ℕ → M} (hs : IsDivSeq ρ p x s) :
    cocycleFun hx hs ∈ ContH1.cocycles (tpRep ρ p) := by
  refine ⟨continuous_of_isOpen fun n m => ?_, fun σ τ => ext fun n => ?_⟩
  · have e : {σ | val M p (cocycleFun hx hs σ) n = m} = {σ | ρ σ (s n) = m + s n} :=
      Set.ext fun σ => sub_eq_iff_eq_add
    rw [e]
    exact isOpen_orbit_fibre (hs.isOpen n) (m + s n)
  · change ρ (σ * τ) (s n) - s n = (ρ σ (s n) - s n) + ρ σ (ρ τ (s n) - s n)
    rw [map_sub, map_mul, Module.End.mul_apply]
    abel

/-- The Kummer cocycle as an element of `ContH1.cocycles`. -/
def cocycle {x : M} (hx : x ∈ ρ.invariants) {s : ℕ → M} (hs : IsDivSeq ρ p x s) :
    ContH1.cocycles (tpRep ρ p) :=
  ⟨cocycleFun hx hs, cocycleFun_mem hx hs⟩

/-- **The class is independent of the system of roots.** -/
theorem mk_cocycle_eq {x : M} (hx : x ∈ ρ.invariants) {s s' : ℕ → M} (hs : IsDivSeq ρ p x s)
    (hs' : IsDivSeq ρ p x s') :
    ContH1.mk (tpRep ρ p) (cocycle hx hs) = ContH1.mk (tpRep ρ p) (cocycle hx hs') := by
  refine (Submodule.Quotient.eq _).mpr ⟨mk (fun n => s n - s' n) ⟨?_, fun n => ?_⟩, fun σ => ?_⟩
  · change s 0 - s' 0 = 0
    rw [hs.zero, hs'.zero, sub_self]
  · change p • (s (n + 1) - s' (n + 1)) = s n - s' n
    rw [smul_sub, hs.succ, hs'.succ]
  · refine ext fun n => ?_
    change (ρ σ (s n) - s n) - (ρ σ (s' n) - s' n) = ρ σ (s n - s' n) - (s n - s' n)
    rw [map_sub]
    abel

variable (ρ p) in
/-- **The Kummer map** `M^Γ → H¹_cont(Γ, T_p M)` on a single invariant point. -/
def kummerFun (hdiv : ∀ y : M, ∃ z, p • z = y) (hst : StabHyp ρ p) (x : ρ.invariants) :
    ContH1.H1 (tpRep ρ p) :=
  ContH1.mk (tpRep ρ p) (cocycle x.2 (exists_isDivSeq hdiv hst x.2).choose_spec)

theorem kummerFun_eq (hdiv : ∀ y : M, ∃ z, p • z = y) (hst : StabHyp ρ p) (x : ρ.invariants)
    {s : ℕ → M} (hs : IsDivSeq ρ p x s) :
    kummerFun ρ p hdiv hst x = ContH1.mk (tpRep ρ p) (cocycle x.2 hs) :=
  mk_cocycle_eq x.2 _ hs

theorem isDivSeq_add {x y : M} {s t : ℕ → M} (hs : IsDivSeq ρ p x s) (ht : IsDivSeq ρ p y t) :
    IsDivSeq ρ p (x + y) (s + t) := by
  refine ⟨by simp [hs.zero, ht.zero], fun n => by simp [hs.succ, ht.succ], fun n => ?_⟩
  refine Subgroup.isOpen_mono (H₁ := stab ρ (s n) ⊓ stab ρ (t n)) (fun σ hσ => ?_)
    ((hs.isOpen n).inter (ht.isOpen n))
  change ρ σ (s n + t n) = s n + t n
  rw [map_add, (mem_stab ρ).mp hσ.1, (mem_stab ρ).mp hσ.2]

variable (ρ p) in
/-- **The Kummer map** `κ : M^Γ → H¹_cont(Γ, T_p M)`, `x ↦ [σ ↦ (σ x_n - x_n)_n]`, for a
`p`-divisible `M` satisfying `StabHyp`. -/
def kummer (hdiv : ∀ y : M, ∃ z, p • z = y) (hst : StabHyp ρ p) :
    ρ.invariants →ₗ[ℤ] ContH1.H1 (tpRep ρ p) :=
  AddMonoidHom.toIntLinearMap
    { toFun := kummerFun ρ p hdiv hst
      map_zero' := by
        have hs : IsDivSeq ρ p (0 : M) 0 :=
          ⟨rfl, fun n => by simp, fun n => by
            rw [Pi.zero_apply, stab_eq_top ρ (Submodule.zero_mem _)]; exact isOpen_univ⟩
        rw [kummerFun_eq hdiv hst 0 hs, ContH1.mk_eq_zero_iff]
        exact ⟨0, fun σ => ext fun n => by simp [cocycle]⟩
      map_add' := fun x y => by
        obtain ⟨s, hs⟩ := exists_isDivSeq hdiv hst x.2
        obtain ⟨t, ht⟩ := exists_isDivSeq hdiv hst y.2
        rw [kummerFun_eq hdiv hst x hs, kummerFun_eq hdiv hst y ht,
          kummerFun_eq hdiv hst (x + y) (isDivSeq_add hs ht), ← map_add]
        congr 1
        exact Subtype.ext (funext fun σ => ext fun n => by
          change ρ σ (s n + t n) - (s n + t n) = (ρ σ (s n) - s n) + (ρ σ (t n) - t n)
          rw [map_add]
          abel) }

/-- **Computation of `κ(x)`** from any compatible system of `p`-power roots of `x` with open
stabilisers. -/
theorem kummer_eq (hdiv : ∀ y : M, ∃ z, p • z = y) (hst : StabHyp ρ p) (x : ρ.invariants)
    {s : ℕ → M} (hs : IsDivSeq ρ p x s) :
    kummer ρ p hdiv hst x = ContH1.mk (tpRep ρ p) (cocycle x.2 hs) :=
  kummerFun_eq hdiv hst x hs

/-! ### Functoriality -/

section Functorial

variable {N : Type*} [AddCommGroup N] {ρ' : Representation ℤ Γ N}

theorem isDivSeq_map (f : M →+ N) (hf : ∀ σ m, f (ρ σ m) = ρ' σ (f m)) {x : M} {s : ℕ → M}
    (hs : IsDivSeq ρ p x s) : IsDivSeq ρ' p (f x) (fun n => f (s n)) := by
  refine ⟨by rw [hs.zero], fun n => by rw [← map_nsmul, hs.succ], fun n => ?_⟩
  refine Subgroup.isOpen_mono (H₁ := stab ρ (s n)) (fun σ hσ => ?_) (hs.isOpen n)
  change ρ' σ (f (s n)) = f (s n)
  rw [← hf, (mem_stab ρ).mp hσ]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem map_mem_invariants (f : M →+ N) (hf : ∀ σ m, f (ρ σ m) = ρ' σ (f m)) {x : M}
    (hx : x ∈ ρ.invariants) : f x ∈ ρ'.invariants := fun σ => by
  rw [← hf, hx σ]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
theorem tpMap_equivariant (f : M →+ N) (hf : ∀ σ m, f (ρ σ m) = ρ' σ (f m)) (σ : Γ)
    (x : Tp M p) : map f (tpRep ρ p σ x) = tpRep ρ' p σ (map f x) :=
  ext fun _ => hf σ _

/-- **Naturality of the Kummer map** in `M`: for a `Γ`-equivariant homomorphism `f : M → N`,
`T_p(f)_* κ_M(x) = κ_N(f x)`. -/
theorem map_kummer (hdiv : ∀ y : M, ∃ z, p • z = y) (hst : StabHyp ρ p)
    (hdiv' : ∀ y : N, ∃ z, p • z = y) (hst' : StabHyp ρ' p) (f : M →+ N)
    (hf : ∀ σ m, f (ρ σ m) = ρ' σ (f m)) (x : ρ.invariants) :
    ContH1.map (map f) (continuous_map f) (tpMap_equivariant f hf) (kummer ρ p hdiv hst x) =
      kummer ρ' p hdiv' hst' ⟨f x, map_mem_invariants f hf x.2⟩ := by
  obtain ⟨s, hs⟩ := exists_isDivSeq hdiv hst x.2
  rw [kummer_eq hdiv hst x hs, kummer_eq hdiv' hst' _ (isDivSeq_map f hf hs), ContH1.map_mk]
  congr 1
  exact Subtype.ext (funext fun σ => ext fun n => by
    change f (ρ σ (s n) - s n) = ρ' σ (f (s n)) - f (s n)
    rw [map_sub, hf])

end Functorial

section Comap

variable {Γ' : Type*} [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ']

omit [IsTopologicalGroup Γ] [IsTopologicalGroup Γ'] in
theorem isDivSeq_comap (ψ : Γ' →* Γ) (hψ : Continuous ψ) {x : M} {s : ℕ → M}
    (hs : IsDivSeq ρ p x s) : IsDivSeq (ρ.comp ψ) p x s :=
  ⟨hs.zero, hs.succ, fun n => by
    rw [stab_comp]
    exact (hs.isOpen n).preimage hψ⟩

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] in
theorem comap_mem_invariants (ψ : Γ' →* Γ) {x : M} (hx : x ∈ ρ.invariants) :
    x ∈ Representation.invariants (ρ.comp ψ) := fun σ => hx (ψ σ)

/-- **Compatibility with restriction**: for a continuous homomorphism `ψ : Γ' → Γ` (e.g.
`G_{K''} ⊆ G_{K'}`), `ψ^* κ_Γ(x) = κ_{Γ'}(x)`. -/
theorem comap_kummer (ψ : Γ' →* Γ) (hψ : Continuous ψ) (hdiv : ∀ y : M, ∃ z, p • z = y)
    (hst : StabHyp ρ p) (hst' : StabHyp (ρ.comp ψ) p) (x : ρ.invariants) :
    ContH1.comap (tpRep ρ p) ψ hψ (kummer ρ p hdiv hst x) =
      kummer (ρ.comp ψ) p hdiv hst' ⟨x, comap_mem_invariants ψ x.2⟩ := by
  obtain ⟨s, hs⟩ := exists_isDivSeq hdiv hst x.2
  rw [kummer_eq hdiv hst x hs, kummer_eq hdiv hst' _ (isDivSeq_comap ψ hψ hs), ContH1.comap_mk]
  rfl

end Comap

/-! ### A sufficient condition for `StabHyp` -/

/-- **`StabHyp` for compact `Γ`**: if `Γ` is compact, every stabiliser is closed and `M[p]` is
finite, then `p`-th roots of points with open stabiliser have open stabiliser (the stabiliser of
`z` in the open subgroup `Stab(p z)` has finite index, the orbit lying in `z + M[p]`). -/
theorem stabHyp_of_finite [CompactSpace Γ] (hcl : ∀ z : M, IsClosed (stab ρ z : Set Γ))
    (hfin : Finite {y : M // p • y = 0}) : StabHyp ρ p := by
  intro x z hx hzx
  set H := stab ρ x with hH
  -- the action of `H` on the `p`-th roots of `x`
  set X := {y : M // p • y = x}
  have hXfin : Finite X := by
    refine Finite.of_injective (fun y : X => (⟨y.1 - z, by rw [smul_sub, y.2, hzx, sub_self]⟩ :
      {y : M // p • y = 0})) fun a b hab => ?_
    exact Subtype.ext (sub_left_injective (congrArg Subtype.val hab))
  letI : MulAction H X :=
    { smul := fun h y => ⟨ρ h y.1, by rw [← map_nsmul, y.2]; exact (mem_stab ρ).mp h.2⟩
      one_smul := fun y => Subtype.ext (by
        change ρ ((1 : H) : Γ) y.1 = y.1
        rw [OneMemClass.coe_one, map_one, Module.End.one_apply])
      mul_smul := fun h h' y => Subtype.ext (by
        change ρ ((h * h' : H) : Γ) y.1 = ρ h (ρ h' y.1)
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]) }
  set z' : X := ⟨z, hzx⟩
  have hstab : MulAction.stabilizer H z' = (stab ρ z).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩
  have hfi : ((stab ρ z).subgroupOf H).FiniteIndex := by
    rw [← hstab]
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    exact Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self z') (Set.toFinite _)
  have hcl' : IsClosed (((stab ρ z).subgroupOf H : Subgroup H) : Set H) :=
    (hcl z).preimage continuous_subtype_val
  have hop : IsOpen (((stab ρ z).subgroupOf H : Subgroup H) : Set H) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl'
  have hop' : IsOpen ((Subtype.val : H → Γ) '' (((stab ρ z).subgroupOf H : Subgroup H) : Set H)) :=
    hx.isOpenMap_subtype_val _ hop
  refine Subgroup.isOpen_mono (H₁ := ((stab ρ z).subgroupOf H).map H.subtype) ?_ hop'
  rintro _ ⟨h, hh, rfl⟩
  exact hh

end Rep

end Kummer

end PadicHodge
