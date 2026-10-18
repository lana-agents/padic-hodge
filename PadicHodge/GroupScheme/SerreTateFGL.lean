/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.SerreTateCompact
import PadicHodge.FormalGroup.LayerPDiv

/-!
# Serre–Tate, essential surjectivity: the formal group law of a connected `p`-divisible group

Let `H = (G_v, i_v)` be a `p`-divisible group over `ℤ_p` with layers `G_v = Spec A_v`. Following
[Hong, Thm. 2.2.16, proof, second part], suppose we are given **coordinates** (`Coords H d`):
compatible families `y_v ∈ A_v^d` (`i_v^*(y_{v+1}) = y_v`) of topologically nilpotent elements
with `ε(y_v) = 0`, such that the evaluations `f_v : ℤ_p[[T]] → A_v`, `T ↦ y_v`, are surjective
and `⋂_v ker f_v = 0`. (They are constructed from the special fibre in
`GroupScheme/SerreTateLift.lean`; in [Hong] this is the lift of the isomorphism (2.5).) Then:

* `Coords.exists_ev_eq`: `ℤ_p[[T]] → lim_v A_v` is surjective (compactness), and the kernels go
  to `0` (`Coords.exists_ker_le`);
* `Coords.eq_zero_of_ev2`, `Coords.eq_zero_of_ev3`: power series in `2d` (resp. `3d`) variables
  vanishing in all `A_v ⊗ A_v` (resp. `A_v ⊗ (A_v ⊗ A_v)`) are zero (the argument of
  `PDivFGL.eq_zero_of_evPair`, with the kernels `ker f_v` in place of `[p^v](I)`);
* **the comultiplication** `Φ_i ∈ ℤ_p[[T, U]]` with `Φ_i(t ⊗ 1, 1 ⊗ t) = Δ(y_{v,i})` in every
  `A_v ⊗ A_v` (`Coords.Φ_spec`); `Φ` represents convolution of points
  (`Coords.evF_conv`: `Φ(φ(y), ψ(y)) = (φ * ψ)(y)`);
* **`Coords.fgl`**: `Φ` is a commutative formal group law (the axioms follow from the group
  axioms of `G_v(S)` by uniqueness), [Hong, Thm. 2.2.16, proof] ("The axioms for each
  comultiplication `μ_v` implies that `μ` … is indeed a formal group law").
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval TensorProduct WithConv

namespace PadicHodge

namespace SerreTate

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔪p" => maximalIdeal (ZpD p)

attribute [local instance] PDivFGL.isAdicComplete_free

/-- **Coordinates** on a `p`-divisible group `H` over `ℤ_p`: compatible families `y_v ∈ A_v^d` of
topologically nilpotent elements of the augmentation ideals such that `ℤ_p[[T]] → A_v`,
`T ↦ y_v`, is surjective for every `v` and jointly injective. -/
structure Coords (H : PDivGroup (ZpD p) p) (d : ℕ) where
  /-- the coordinates `y_v ∈ A_v^d` -/
  y : ∀ v, Fin d → (H.G v).A
  tnf : ∀ v, FGL.TNF 𝔪p (y v)
  counit_y : ∀ v j, Coalgebra.counit (R := ZpD p) (y v j) = 0
  incl_y : ∀ v j, H.incl v (y (v + 1) j) = y v j
  surj : ∀ v, Function.Surjective (evalT (y v) (tnf v))
  inj : ∀ g, (∀ v, evalT (y v) (tnf v) g = 0) → g = 0

namespace Coords

variable {H : PDivGroup (ZpD p) p} {d : ℕ} (C : Coords H d)

/-! ### One variable -/

/-- `f_v : ℤ_p[[T]] → A_v`, `T ↦ y_v`. -/
def ev (v : ℕ) : MvPowerSeries (Fin d) (ZpD p) →ₐ[ZpD p] (H.G v).A :=
  evalT (C.y v) (C.tnf v)

theorem ev_X (v : ℕ) (j : Fin d) : C.ev v (X j) = C.y v j := evalT_X _ _ j

theorem ev_eq_evF (v : ℕ) (g : MvPowerSeries (Fin d) (ZpD p)) :
    C.ev v g = FGL.evF 𝔪p (C.y v) g :=
  (FGL.evF_of (C.tnf v) g).symm

theorem ev_surjective (v : ℕ) : Function.Surjective (C.ev v) := C.surj v

theorem tnf_ev (v : ℕ) (j : Fin d) : TopNil 𝔪p (C.ev v (X j)) := by
  rw [ev_X]; exact C.tnf v j

theorem incl_comp_ev (v : ℕ) :
    (H.incl v : (H.G (v + 1)).A →ₐ[ZpD p] (H.G v).A).comp (C.ev (v + 1)) = C.ev v := by
  refine algHom_ext_topNil (𝔪 := 𝔪p) (fun j => ?_) fun j => ?_
  · rw [AlgHom.comp_apply, ev_X]; exact (C.tnf (v + 1) j).map _
  · rw [AlgHom.comp_apply, ev_X, ev_X]; exact C.incl_y v j

theorem incl_ev (v : ℕ) (g : MvPowerSeries (Fin d) (ZpD p)) :
    H.incl v (C.ev (v + 1) g) = C.ev v g := by
  rw [← C.incl_comp_ev v]; rfl

theorem ev_eq_zero_of_le {v w : ℕ} (hvw : v ≤ w) {g : MvPowerSeries (Fin d) (ZpD p)}
    (h : C.ev w g = 0) : C.ev v g = 0 := by
  induction w, hvw using Nat.le_induction with
  | base => exact h
  | succ w _ ih => exact ih (by rw [← C.incl_ev, h, map_zero])

/-- **`ℤ_p[[T]] → lim_v A_v` is surjective** (compactness). -/
theorem exists_ev_eq (a : ∀ v, (H.G v).A) (ha : ∀ v, H.incl v (a (v + 1)) = a v) :
    ∃ g, ∀ v, C.ev v g = a v :=
  exists_forall_eq (B := fun v => (H.G v).A) C.ev C.tnf_ev a (fun v => C.ev_surjective v (a v))
    fun v g h => by rw [← C.incl_ev, h, ha]

/-- **The kernels of `f_v` go to `0`.** -/
theorem exists_ker_le (w : ℕ) :
    ∃ v, ∀ g, C.ev v g = 0 → g ∈ FGL.coeffFilt (σ := Fin d) 𝔪p w :=
  exists_ker_le_coeffFilt (B := fun v => (H.G v).A) C.ev C.tnf_ev
    (fun v _ h => C.ev_eq_zero_of_le (Nat.le_succ v) h) C.inj w

/-! ### Several variables -/

/-- `T ↦ T^{(a)}`, `ℤ_p[[T]] → ℤ_p[[T^{(0)}, …, T^{(n-1)}]]`. -/
def substXn {n : ℕ} (a : Fin n) :
    MvPowerSeries (Fin d) (ZpD p) →ₐ[ZpD p] MvPowerSeries (Fin n × Fin d) (ZpD p) :=
  substAlgHom (FGL.hasSubst_of_noConst (FGL.noConst_Xv (R := ZpD p) (d := d) a))

theorem substXn_X {n : ℕ} (a : Fin n) (j : Fin d) :
    substXn (p := p) a (X j) = X (a, j) := by
  rw [substXn, coe_substAlgHom, subst_X (FGL.hasSubst_of_noConst (FGL.noConst_Xv a))]
  rfl

/-- `K_v^{(n)} = (ker f_v)(T^{(0)}) + ⋯ + (ker f_v)(T^{(n-1)})`. -/
def multiKer (n v : ℕ) : Ideal (MvPowerSeries (Fin n × Fin d) (ZpD p)) :=
  ⨆ a : Fin n, Ideal.map (substXn a) (RingHom.ker (C.ev v))

theorem multiKer_le {n v w : ℕ} (h : ∀ g, C.ev v g = 0 → g ∈ FGL.coeffFilt (σ := Fin d) 𝔪p w) :
    C.multiKer n v ≤ FGL.coeffFilt 𝔪p w :=
  iSup_le fun a => (Ideal.map_mono fun g hg => h g (RingHom.mem_ker.mp hg)).trans
    (map_coeffFilt_le 𝔪p (substXn a) (fun j => by
      rw [substXn_X]; exact Ideal.subset_span ⟨_, rfl⟩) w)

theorem toQ_aux (n v : ℕ) (a : Fin n) : ∀ g ∈ RingHom.ker (C.ev v),
    ((Ideal.Quotient.mkₐ (ZpD p) (C.multiKer n v)).comp (substXn a)) g = 0 := fun g hg => by
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_iSup_of_mem a (Ideal.mem_map_of_mem _ hg)

/-- `A_v ≅ ℤ_p[[T]]/ker f_v → ℤ_p[[T^{(0)}, …]]/K_v^{(n)}`, `t ↦ T^{(a)}`. -/
def toQ (n v : ℕ) (a : Fin n) :
    (H.G v).A →ₐ[ZpD p] MvPowerSeries (Fin n × Fin d) (ZpD p) ⧸ C.multiKer n v :=
  (Ideal.Quotient.liftₐ (RingHom.ker (C.ev v))
    ((Ideal.Quotient.mkₐ (ZpD p) (C.multiKer n v)).comp (substXn a)) (C.toQ_aux n v a)).comp
    (Ideal.quotientKerAlgEquivOfSurjective (C.ev_surjective v)).symm.toAlgHom

theorem toQ_ev (n v : ℕ) (a : Fin n) (g : MvPowerSeries (Fin d) (ZpD p)) :
    C.toQ n v a (C.ev v g) = Ideal.Quotient.mk _ (substXn a g) := by
  have h : (Ideal.quotientKerAlgEquivOfSurjective (C.ev_surjective v)).symm (C.ev v g) =
      Ideal.Quotient.mk _ g := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  change Ideal.Quotient.liftₐ (RingHom.ker (C.ev v))
    ((Ideal.Quotient.mkₐ (ZpD p) (C.multiKer n v)).comp (substXn a)) (C.toQ_aux n v a)
    ((Ideal.quotientKerAlgEquivOfSurjective (C.ev_surjective v)).symm (C.ev v g)) = _
  rw [h, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

theorem toQ_y (n v : ℕ) (a : Fin n) (j : Fin d) :
    C.toQ n v a (C.y v j) = Ideal.Quotient.mk _ (X (a, j)) := by
  rw [← C.ev_X, toQ_ev, substXn_X]

/-- **Injectivity criterion**: if `α_v ∘ ψ_v` agrees with the quotient map on the variables,
a power series killed by all `ψ_v` is zero. -/
theorem eq_zero_of_alpha {n : ℕ} {B : ℕ → Type*} [∀ v, CommRing (B v)]
    [∀ v, Algebra (ZpD p) (B v)]
    (ψ : ∀ v, MvPowerSeries (Fin n × Fin d) (ZpD p) →ₐ[ZpD p] B v)
    (α : ∀ v, B v →ₐ[ZpD p] MvPowerSeries (Fin n × Fin d) (ZpD p) ⧸ C.multiKer n v)
    (hα : ∀ v x, α v (ψ v (X x)) = Ideal.Quotient.mk _ (X x))
    {g : MvPowerSeries (Fin n × Fin d) (ZpD p)} (hg : ∀ v, ψ v g = 0) : g = 0 := by
  refine FGL.eq_zero_of_mem_coeffFilt (𝔪 := 𝔪p) fun w => ?_
  obtain ⟨v, hv⟩ := C.exists_ker_le w
  have := MvPowerSeries.mem_sup_pow_of_comp_eq_mk ((α v).comp (ψ v)) (fun x => hα v x)
    (g := g) (by rw [AlgHom.comp_apply, hg v, map_zero]) w
  exact sup_le (C.multiKer_le hv) (FGL.pow_span_X_le_coeffFilt w) this

/-! ### Two variables -/

/-- `t ↦ t ⊗ 1`. -/
abbrev inL (v : ℕ) : (H.G v).A →ₐ[ZpD p] (H.G v).A ⊗[ZpD p] (H.G v).A :=
  Algebra.TensorProduct.includeLeft

/-- `t ↦ 1 ⊗ t`. -/
abbrev inR (v : ℕ) : (H.G v).A →ₐ[ZpD p] (H.G v).A ⊗[ZpD p] (H.G v).A :=
  Algebra.TensorProduct.includeRight

theorem tnf_map {S : Type*} [CommRing S] [Algebra (ZpD p) S] (v : ℕ)
    (φ : (H.G v).A →ₐ[ZpD p] S) : FGL.TNF 𝔪p fun j => φ (C.y v j) :=
  fun j => (C.tnf v j).map φ

/-- `R[[T, U]] → A_v ⊗ A_v`, `(T, U) ↦ (t ⊗ 1, 1 ⊗ t)`. -/
def ev2 (v : ℕ) : MvPowerSeries (Fin 2 × Fin d) (ZpD p) →ₐ[ZpD p]
    (H.G v).A ⊗[ZpD p] (H.G v).A :=
  evalT (FGL.pairS (fun j => inL v (C.y v j)) fun j => inR v (C.y v j))
    (FGL.tnf_pairS (C.tnf_map v _) (C.tnf_map v _))

theorem ev2_X (v : ℕ) (x : Fin 2 × Fin d) :
    C.ev2 v (X x) = FGL.pairS (fun j => inL v (C.y v j)) (fun j => inR v (C.y v j)) x :=
  evalT_X _ _ x

theorem ev2_eq_evF (v : ℕ) (g : MvPowerSeries (Fin 2 × Fin d) (ZpD p)) :
    C.ev2 v g = FGL.evF 𝔪p (FGL.pairS (fun j => inL v (C.y v j)) fun j => inR v (C.y v j)) g :=
  (FGL.evF_of _ g).symm

theorem tnf_ev2 (v : ℕ) (x : Fin 2 × Fin d) : TopNil 𝔪p (C.ev2 v (X x)) := by
  rw [ev2_X]; exact FGL.tnf_pairS (C.tnf_map v _) (C.tnf_map v _) x

theorem ev2_comp_substXn_zero (v : ℕ) : (C.ev2 v).comp (substXn 0) = (inL v).comp (C.ev v) := by
  refine algHom_ext_topNil (𝔪 := 𝔪p) (fun j => ?_) fun j => ?_
  · rw [AlgHom.comp_apply, substXn_X]; exact C.tnf_ev2 v _
  · rw [AlgHom.comp_apply, substXn_X, ev2_X, AlgHom.comp_apply, ev_X]
    simp [FGL.pairS]

theorem ev2_comp_substXn_one (v : ℕ) : (C.ev2 v).comp (substXn 1) = (inR v).comp (C.ev v) := by
  refine algHom_ext_topNil (𝔪 := 𝔪p) (fun j => ?_) fun j => ?_
  · rw [AlgHom.comp_apply, substXn_X]; exact C.tnf_ev2 v _
  · rw [AlgHom.comp_apply, substXn_X, ev2_X, AlgHom.comp_apply, ev_X]
    simp [FGL.pairS]

theorem ev2_surjective (v : ℕ) : Function.Surjective (C.ev2 v) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
    obtain ⟨g, rfl⟩ := C.ev_surjective v a
    obtain ⟨h, rfl⟩ := C.ev_surjective v b
    refine ⟨substXn 0 g * substXn 1 h, ?_⟩
    have h0 := congrArg (fun φ => φ g) (C.ev2_comp_substXn_zero v)
    have h1 := congrArg (fun φ => φ h) (C.ev2_comp_substXn_one v)
    simp only [AlgHom.comp_apply] at h0 h1
    rw [map_mul, h0, h1, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
  | add x x' hx hx' =>
    obtain ⟨g, rfl⟩ := hx
    obtain ⟨g', rfl⟩ := hx'
    exact ⟨g + g', map_add _ _ _⟩

theorem map_incl_comp_ev2 (v : ℕ) :
    (Algebra.TensorProduct.map (H.incl v : (H.G (v + 1)).A →ₐ[ZpD p] (H.G v).A)
      (H.incl v : (H.G (v + 1)).A →ₐ[ZpD p] (H.G v).A)).comp (C.ev2 (v + 1)) = C.ev2 v := by
  refine algHom_ext_topNil (𝔪 := 𝔪p) (fun x => ?_) fun x => ?_
  · exact (C.tnf_ev2 (v + 1) x).map (Algebra.TensorProduct.map
      (H.incl v : (H.G (v + 1)).A →ₐ[ZpD p] (H.G v).A)
      (H.incl v : (H.G (v + 1)).A →ₐ[ZpD p] (H.G v).A))
  · simp only [AlgHom.comp_apply, ev2_X]
    obtain ⟨a, j⟩ := x
    simp only [FGL.pairS]
    split_ifs <;> simp [incl_y]

/-- `α_v : A_v ⊗ A_v → ℤ_p[[T, U]]/K_v^{(2)}`. -/
def alpha2 (v : ℕ) :
    (H.G v).A ⊗[ZpD p] (H.G v).A →ₐ[ZpD p] MvPowerSeries (Fin 2 × Fin d) (ZpD p) ⧸ C.multiKer 2 v :=
  Algebra.TensorProduct.lift (C.toQ 2 v 0) (C.toQ 2 v 1) fun _ _ => Commute.all _ _

theorem alpha2_ev2_X (v : ℕ) (x : Fin 2 × Fin d) :
    C.alpha2 v (C.ev2 v (X x)) = Ideal.Quotient.mk _ (X x) := by
  obtain ⟨a, j⟩ := x
  rw [ev2_X]
  simp only [FGL.pairS]
  fin_cases a
  · simp [alpha2, toQ_y]
  · simp [alpha2, toQ_y]

/-- **A power series in `(T, U)` vanishing in every `A_v ⊗ A_v` is zero.** -/
theorem eq_zero_of_ev2 {g : MvPowerSeries (Fin 2 × Fin d) (ZpD p)} (hg : ∀ v, C.ev2 v g = 0) :
    g = 0 :=
  C.eq_zero_of_alpha C.ev2 C.alpha2 C.alpha2_ev2_X hg

/-! ### Three variables -/

variable (H) in
/-- The three inclusions `A_v → A_v ⊗ (A_v ⊗ A_v)`. -/
def e3 (v : ℕ) (a : Fin 3) :
    (H.G v).A →ₐ[ZpD p] (H.G v).A ⊗[ZpD p] ((H.G v).A ⊗[ZpD p] (H.G v).A) :=
  if a = 0 then Algebra.TensorProduct.includeLeft
  else if a = 1 then (Algebra.TensorProduct.includeRight).comp (inL v)
  else (Algebra.TensorProduct.includeRight).comp (inR v)

/-- `R[[T, U, V]] → A_v ⊗ (A_v ⊗ A_v)`. -/
def ev3 (v : ℕ) : MvPowerSeries (Fin 3 × Fin d) (ZpD p) →ₐ[ZpD p]
    (H.G v).A ⊗[ZpD p] ((H.G v).A ⊗[ZpD p] (H.G v).A) :=
  evalT (fun x => e3 H v x.1 (C.y v x.2)) fun x => (C.tnf v x.2).map _

theorem ev3_X (v : ℕ) (x : Fin 3 × Fin d) : C.ev3 v (X x) = e3 H v x.1 (C.y v x.2) :=
  evalT_X _ _ x

/-- `α_v : A_v ⊗ (A_v ⊗ A_v) → ℤ_p[[T, U, V]]/K_v^{(3)}`. -/
def alpha3 (v : ℕ) : (H.G v).A ⊗[ZpD p] ((H.G v).A ⊗[ZpD p] (H.G v).A) →ₐ[ZpD p]
    MvPowerSeries (Fin 3 × Fin d) (ZpD p) ⧸ C.multiKer 3 v :=
  Algebra.TensorProduct.lift (C.toQ 3 v 0)
    (Algebra.TensorProduct.lift (C.toQ 3 v 1) (C.toQ 3 v 2) fun _ _ => Commute.all _ _)
    fun _ _ => Commute.all _ _

theorem alpha3_ev3_X (v : ℕ) (x : Fin 3 × Fin d) :
    C.alpha3 v (C.ev3 v (X x)) = Ideal.Quotient.mk _ (X x) := by
  obtain ⟨a, j⟩ := x
  rw [ev3_X]
  fin_cases a
  · simp [alpha3, e3, toQ_y]
  · simp [alpha3, e3, toQ_y]
  · simp [alpha3, e3, toQ_y]

/-- **A power series in `(T, U, V)` vanishing in every `A_v ⊗ (A_v ⊗ A_v)` is zero.** -/
theorem eq_zero_of_ev3 {g : MvPowerSeries (Fin 3 × Fin d) (ZpD p)} (hg : ∀ v, C.ev3 v g = 0) :
    g = 0 :=
  C.eq_zero_of_alpha C.ev3 C.alpha3 C.alpha3_ev3_X hg

/-! ### The comultiplication -/

theorem incl_comul (v : ℕ) (a : (H.G (v + 1)).A) :
    Algebra.TensorProduct.map (H.incl v : (H.G (v + 1)).A →ₐ[ZpD p] (H.G v).A)
      (H.incl v : (H.G (v + 1)).A →ₐ[ZpD p] (H.G v).A)
      (Bialgebra.comulAlgHom (ZpD p) (H.G (v + 1)).A a) =
    Bialgebra.comulAlgHom (ZpD p) (H.G v).A (H.incl v a) := by
  rw [Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply]
  exact CoalgHomClass.map_comp_comul_apply (H.incl v) a

theorem exists_Φ (i : Fin d) :
    ∃ g, ∀ v, C.ev2 v g = Bialgebra.comulAlgHom (ZpD p) (H.G v).A (C.y v i) :=
  exists_forall_eq (B := fun v => (H.G v).A ⊗[ZpD p] (H.G v).A) C.ev2 C.tnf_ev2
    (fun v => Bialgebra.comulAlgHom (ZpD p) (H.G v).A (C.y v i))
    (fun v => C.ev2_surjective v _) fun v g h => by
      rw [← C.map_incl_comp_ev2 v, AlgHom.comp_apply, h, incl_comul, incl_y]

/-- **The power series `Φ_i(T, U)`** with `Φ_i(t ⊗ 1, 1 ⊗ t) = Δ(y_i)` in every `A_v ⊗ A_v`. -/
def Φ (i : Fin d) : MvPowerSeries (Fin 2 × Fin d) (ZpD p) := (C.exists_Φ i).choose

theorem Φ_spec (i : Fin d) (v : ℕ) :
    C.ev2 v (C.Φ i) = Bialgebra.comulAlgHom (ZpD p) (H.G v).A (C.y v i) :=
  (C.exists_Φ i).choose_spec v

/-- **`Φ` represents convolution**: `Φ(φ(y), ψ(y)) = (φ * ψ)(y)` for points `φ, ψ` of `G_v`
with values in a finite free algebra. -/
theorem evF_conv {S : Type} [CommRing S] [Algebra (ZpD p) S] [Module.Free (ZpD p) S]
    [Module.Finite (ZpD p) S] (v : ℕ) (φ ψ : (H.G v).points S) (i : Fin d) :
    FGL.evF 𝔪p (FGL.pairS (fun j => ofConv φ (C.y v j)) fun j => ofConv ψ (C.y v j)) (C.Φ i) =
      ofConv (φ * ψ) (C.y v i) := by
  set χ := (Algebra.TensorProduct.lmul' (ZpD p) (S := S)).comp
    (Algebra.TensorProduct.map (ofConv φ) (ofConv ψ))
  have h1 : ofConv (φ * ψ) (C.y v i) = χ (C.ev2 v (C.Φ i)) := by
    rw [Φ_spec]
    rfl
  rw [h1, ev2_eq_evF, FGL.evF_comp χ (FGL.tnf_pairS (C.tnf_map v _) (C.tnf_map v _))]
  congr 1
  funext x
  obtain ⟨a, j⟩ := x
  simp only [FGL.pairS]
  split_ifs <;> simp [χ]

/-! ### The axioms -/

/-- Evaluation of `h(f, g)`. -/
theorem evF_subst_pairFam {S : Type} [CommRing S] [Algebra (ZpD p) S]
    [IsAdicComplete ((𝔪p).map (algebraMap (ZpD p) S)) S] {τ : Type*} [Finite τ] {x : τ → S}
    (hx : FGL.TNF 𝔪p x) {f g : Fin d → MvPowerSeries τ (ZpD p)} (hf : FGL.NoConst f)
    (hg : FGL.NoConst g) (h : MvPowerSeries (Fin 2 × Fin d) (ZpD p)) :
    FGL.evF 𝔪p x (h.subst (pairFam f g)) =
      FGL.evF 𝔪p (FGL.pairS (fun j => FGL.evF 𝔪p x (f j)) fun j => FGL.evF 𝔪p x (g j)) h := by
  rw [FGL.evF_subst hx (fun v => by unfold pairFam; split_ifs; exacts [hf _, hg _])]
  congr 1
  funext v
  unfold pairFam FGL.pairS
  split_ifs <;> rfl

/-- `Φ(y, 0) = y`. -/
theorem evF_pairS_y_zero (v : ℕ) (i : Fin d) :
    FGL.evF 𝔪p (FGL.pairS (C.y v) 0) (C.Φ i) = C.y v i := by
  have h := C.evF_conv v (H.G v).univPt 1 i
  rw [mul_one] at h
  have h0 : (fun j => ofConv (1 : (H.G v).points (H.G v).A) (C.y v j)) = 0 := by
    funext j
    rw [AlgHom.convOne_apply, C.counit_y, map_zero]
    rfl
  rw [h0] at h
  exact h

/-- `Φ(0, y) = y`. -/
theorem evF_pairS_zero_y (v : ℕ) (i : Fin d) :
    FGL.evF 𝔪p (FGL.pairS 0 (C.y v)) (C.Φ i) = C.y v i := by
  have h := C.evF_conv v 1 (H.G v).univPt i
  rw [one_mul] at h
  have h0 : (fun j => ofConv (1 : (H.G v).points (H.G v).A) (C.y v j)) = 0 := by
    funext j
    rw [AlgHom.convOne_apply, C.counit_y, map_zero]
    rfl
  rw [h0] at h
  exact h

theorem constantCoeff_Φ (i : Fin d) : constantCoeff (C.Φ i) = 0 := by
  set χ := (Algebra.ofId (ZpD p) (H.G 0).A).comp (Bialgebra.counitAlgHom (ZpD p) (H.G 0).A)
  have h := congrArg χ (C.evF_pairS_y_zero 0 i)
  have hy : ∀ j, χ (C.y 0 j) = 0 := fun j => by
    simp [χ, Bialgebra.counitAlgHom_apply, C.counit_y]
  rw [FGL.evF_comp χ (FGL.tnf_pairS (C.tnf 0) FGL.tnf_zero), hy] at h
  have e : (fun s => χ (FGL.pairS (C.y 0) 0 s)) = 0 := by
    funext x
    obtain ⟨a, j⟩ := x
    simp only [FGL.pairS]
    split_ifs
    · exact hy j
    · simp
  rw [e, FGL.evF_zero_fam] at h
  have h' := congrArg (Coalgebra.counit (R := ZpD p) (A := (H.G 0).A)) h
  rwa [map_zero, Algebra.algebraMap_eq_smul_one, map_smul, Bialgebra.counit_one, smul_eq_mul,
    mul_one] at h'

theorem noConst_Φ : FGL.NoConst C.Φ := C.constantCoeff_Φ

theorem unit_right (i : Fin d) :
    (C.Φ i).subst (pairFam (fun j => (X j : MvPowerSeries (Fin d) (ZpD p))) 0) = X i := by
  refine sub_eq_zero.mp (C.inj _ fun v => ?_)
  change C.ev v _ = 0
  rw [map_sub, sub_eq_zero, ev_eq_evF, ev_eq_evF,
    evF_subst_pairFam (C.tnf v) FGL.noConst_X FGL.noConst_zero, FGL.evF_X (C.tnf v)]
  have e1 : (fun j => FGL.evF 𝔪p (C.y v) (X j : MvPowerSeries (Fin d) (ZpD p))) = C.y v :=
    funext fun j => FGL.evF_X (C.tnf v) j
  have e2 : (fun j => FGL.evF 𝔪p (C.y v) ((0 : Fin d → MvPowerSeries (Fin d) (ZpD p)) j)) = 0 :=
    funext fun j => FGL.evF_zero _
  rw [e1, e2, evF_pairS_y_zero]

theorem unit_left (i : Fin d) :
    (C.Φ i).subst (pairFam 0 (fun j => (X j : MvPowerSeries (Fin d) (ZpD p)))) = X i := by
  refine sub_eq_zero.mp (C.inj _ fun v => ?_)
  change C.ev v _ = 0
  rw [map_sub, sub_eq_zero, ev_eq_evF, ev_eq_evF,
    evF_subst_pairFam (C.tnf v) FGL.noConst_zero FGL.noConst_X, FGL.evF_X (C.tnf v)]
  have e1 : (fun j => FGL.evF 𝔪p (C.y v) (X j : MvPowerSeries (Fin d) (ZpD p))) = C.y v :=
    funext fun j => FGL.evF_X (C.tnf v) j
  have e2 : (fun j => FGL.evF 𝔪p (C.y v) ((0 : Fin d → MvPowerSeries (Fin d) (ZpD p)) j)) = 0 :=
    funext fun j => FGL.evF_zero _
  rw [e1, e2, evF_pairS_zero_y]

theorem comm (i : Fin d) :
    (C.Φ i).subst (pairFam (Xv (R := ZpD p) (n := 2) 1) (Xv 0)) = C.Φ i := by
  refine sub_eq_zero.mp (C.eq_zero_of_ev2 fun v => ?_)
  have hx := FGL.tnf_pairS (C.tnf_map v (inL v)) (C.tnf_map v (inR v))
  rw [map_sub, sub_eq_zero, ev2_eq_evF, evF_subst_pairFam hx (FGL.noConst_Xv 1)
    (FGL.noConst_Xv 0), C.Φ_spec]
  simp only [FGL.evF_pairS_Xv (C.tnf_map v (inL v)) (C.tnf_map v (inR v)),
    show (1 : Fin 2) ≠ 0 from by decide, if_true, if_false]
  have h := C.evF_conv v (toConv (inR v)) (toConv (inL v)) i
  rw [h, mul_comm, FFGroupScheme.inl_mul_inr]

theorem evF3_Φ (v : ℕ) (a b : Fin 3) (i : Fin d) :
    FGL.evF 𝔪p (fun x => e3 H v x.1 (C.y v x.2)) ((C.Φ i).subst (pairFam (Xv a) (Xv b))) =
      ofConv (toConv (e3 H v a) * toConv (e3 H v b)) (C.y v i) := by
  have hx : FGL.TNF 𝔪p (fun x : Fin 3 × Fin d => e3 H v x.1 (C.y v x.2)) :=
    fun x => (C.tnf v x.2).map _
  rw [evF_subst_pairFam hx (FGL.noConst_Xv a) (FGL.noConst_Xv b), ← C.evF_conv v]
  congr 1
  funext x
  obtain ⟨c, j⟩ := x
  simp only [FGL.pairS]
  split_ifs <;> rw [Xv, FGL.evF_X hx]

theorem assoc (i : Fin d) :
    (C.Φ i).subst (pairFam (fun j => (C.Φ j).subst (pairFam (Xv (R := ZpD p) (n := 3) 0) (Xv 1)))
      (Xv 2)) =
    (C.Φ i).subst (pairFam (Xv (R := ZpD p) (n := 3) 0)
      (fun j => (C.Φ j).subst (pairFam (Xv (R := ZpD p) (n := 3) 1) (Xv 2)))) := by
  refine sub_eq_zero.mp (C.eq_zero_of_ev3 fun v => ?_)
  have hx : FGL.TNF 𝔪p (fun x : Fin 3 × Fin d => e3 H v x.1 (C.y v x.2)) :=
    fun x => (C.tnf v x.2).map _
  have hc : ∀ a b : Fin 3, FGL.NoConst fun j =>
      (C.Φ j).subst (pairFam (Xv (R := ZpD p) (d := d) (n := 3) a) (Xv b)) := fun a b j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (FGL.noConst_pairFam
      (FGL.noConst_Xv a) (FGL.noConst_Xv b))) (FGL.noConst_pairFam (FGL.noConst_Xv a)
      (FGL.noConst_Xv b)) (C.constantCoeff_Φ j)
  have hX : ∀ a : Fin 3,
      (fun j => FGL.evF 𝔪p (fun x : Fin 3 × Fin d => e3 H v x.1 (C.y v x.2))
        (Xv (R := ZpD p) a j)) = fun j => ofConv (toConv (e3 H v a)) (C.y v j) := fun a => by
    funext j
    rw [Xv, FGL.evF_X hx]
  rw [map_sub, sub_eq_zero]
  unfold ev3
  rw [← FGL.evF_of hx, ← FGL.evF_of hx, evF_subst_pairFam hx (hc 0 1) (FGL.noConst_Xv 2),
    evF_subst_pairFam hx (FGL.noConst_Xv 0) (hc 1 2), hX, hX]
  simp only [evF3_Φ]
  rw [C.evF_conv, C.evF_conv, mul_assoc]

/-- **The formal group law of `H`** ([Hong, Thm. 2.2.16, proof]). -/
def fgl : FGL (ZpD p) d where
  Φ := C.Φ
  constantCoeff_Φ := C.constantCoeff_Φ
  assoc := C.assoc
  unit_right := C.unit_right
  unit_left := C.unit_left
  comm := C.comm

end Coords

end SerreTate

end PadicHodge
