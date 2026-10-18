/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.AdicEval
import PadicHodge.FormalGroup.Formal

/-!
# Points of a formal group law with topologically nilpotent coordinates

Let `R` be a ring with an ideal `𝔪` and `S` an `R`-algebra which is `𝔪S`-adically complete. For a
formal group law `F` of dimension `d` over `R`, the families `x : Fin d → S` of topologically
nilpotent elements (`TNF 𝔪 x`) form a commutative group under `x +_F y = Φ(x, y)`
(`addE`): evaluation (`evF`, from `AdicEval.evalT`) commutes with substitution (`evF_subst`) and
with algebra maps (`evF_comp`), so the axioms of `F` give the group laws
(`addE_assoc`, `addE_comm`, `addE_zero`, `zero_addE`). Also `n · x = [n]_F(x)` (`mulE`,
`mulE_succ`). These are used, with `S` the tensor powers of the layers `A_v`, to construct the
Hopf algebra structure on `A_v` ([Hong, Prop. 2.2.10]).
-/

noncomputable section

open MvPowerSeries PadicHodge.AdicEval

namespace PadicHodge

namespace FGL

variable {R : Type*} [CommRing R] (𝔪 : Ideal R)

section Ev

variable {S : Type*} [CommRing S] [Algebra R S]

/-- A family of topologically nilpotent elements. -/
abbrev TNF {σ : Type*} (x : σ → S) : Prop := ∀ i, TopNil 𝔪 (x i)

variable [IsAdicComplete (𝔪.map (algebraMap R S)) S]

open Classical in
/-- Evaluation `f ↦ f(x)` at a topologically nilpotent family (`0` otherwise). -/
def evF {σ : Type*} [Finite σ] (x : σ → S) (f : MvPowerSeries σ R) : S :=
  if h : TNF 𝔪 x then evalT x h f else 0

variable {𝔪}

theorem evF_of {σ : Type*} [Finite σ] {x : σ → S} (hx : TNF 𝔪 x) (f : MvPowerSeries σ R) :
    evF 𝔪 x f = evalT x hx f := by
  classical
  rw [evF, dif_pos hx]

theorem evF_X {σ : Type*} [Finite σ] {x : σ → S} (hx : TNF 𝔪 x) (i : σ) :
    evF 𝔪 x (X i) = x i := by
  rw [evF_of hx, evalT_X]

theorem evF_add {σ : Type*} [Finite σ] {x : σ → S} (hx : TNF 𝔪 x) (f g : MvPowerSeries σ R) :
    evF 𝔪 x (f + g) = evF 𝔪 x f + evF 𝔪 x g := by
  rw [evF_of hx, evF_of hx, evF_of hx, map_add]

theorem evF_mul {σ : Type*} [Finite σ] {x : σ → S} (hx : TNF 𝔪 x) (f g : MvPowerSeries σ R) :
    evF 𝔪 x (f * g) = evF 𝔪 x f * evF 𝔪 x g := by
  rw [evF_of hx, evF_of hx, evF_of hx, map_mul]

theorem evF_zero {σ : Type*} [Finite σ] (x : σ → S) : evF 𝔪 x (0 : MvPowerSeries σ R) = 0 := by
  classical
  unfold evF; split_ifs <;> simp

theorem topNil_evF {σ : Type*} [Finite σ] {x : σ → S} (hx : TNF 𝔪 x) {f : MvPowerSeries σ R}
    (hf : constantCoeff f = 0) : TopNil 𝔪 (evF 𝔪 x f) := by
  rw [evF_of hx]
  exact topNil_evalT hx hf

/-- **Evaluation commutes with substitution.** -/
theorem evF_subst {σ τ : Type*} [Finite σ] [Finite τ] {x : τ → S} (hx : TNF 𝔪 x)
    {a : σ → MvPowerSeries τ R} (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    evF 𝔪 x (f.subst a) = evF 𝔪 (fun s => evF 𝔪 x (a s)) f := by
  have hy : TNF 𝔪 fun s => evF 𝔪 x (a s) := fun s => topNil_evF hx (ha s)
  have hA : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have key : (evalT x hx).comp (substAlgHom hA) = evalT _ hy := by
    refine algHom_ext_topNil (𝔪 := 𝔪) (fun s => ?_) fun s => ?_
    · rw [AlgHom.comp_apply, coe_substAlgHom, subst_X hA, ← evF_of hx]
      exact topNil_evF hx (ha s)
    · rw [AlgHom.comp_apply, coe_substAlgHom, subst_X hA, evalT_X, evF_of hx]
  rw [evF_of hx, evF_of hy, ← key, AlgHom.comp_apply, coe_substAlgHom]

/-- **Algebra maps commute with evaluation.** -/
theorem evF_comp {S' : Type*} [CommRing S'] [Algebra R S']
    [IsAdicComplete (𝔪.map (algebraMap R S')) S'] (g : S →ₐ[R] S') {σ : Type*} [Finite σ]
    {x : σ → S} (hx : TNF 𝔪 x) (f : MvPowerSeries σ R) :
    g (evF 𝔪 x f) = evF 𝔪 (fun s => g (x s)) f := by
  have hy : TNF 𝔪 fun s => g (x s) := fun s => (hx s).map g
  have key : g.comp (evalT x hx) = evalT _ hy := by
    refine algHom_ext_topNil (𝔪 := 𝔪) (fun s => ?_) fun s => ?_
    · rw [AlgHom.comp_apply, evalT_X]; exact hy s
    · rw [AlgHom.comp_apply, evalT_X, evalT_X]
  rw [evF_of hx, evF_of hy, ← key, AlgHom.comp_apply]

/-- The `R`-algebra map `R[[X_σ]] → R`, `f ↦ f(0)`. -/
def constAlgHom (σ : Type*) : MvPowerSeries σ R →ₐ[R] R :=
  { constantCoeff with
    commutes' := fun r => by
      change constantCoeff (algebraMap R (MvPowerSeries σ R) r) = r
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        constantCoeff_C] }

/-- **Evaluation at `0`.** -/
theorem evF_zero_fam {σ : Type*} [Finite σ] (f : MvPowerSeries σ R) :
    evF 𝔪 (0 : σ → S) f = algebraMap R S (constantCoeff f) := by
  have h0 : TNF 𝔪 (0 : σ → S) := fun _ => topNil_zero
  have key : evalT (0 : σ → S) h0 = (Algebra.ofId R S).comp (constAlgHom σ) := by
    refine algHom_ext_topNil (𝔪 := 𝔪) (fun s => ?_) fun s => ?_
    · rw [evalT_X]; exact topNil_zero
    · rw [evalT_X, AlgHom.comp_apply]
      simp [constAlgHom]
  rw [evF_of h0, key]
  rfl

end Ev

/-! ### The group law on topologically nilpotent families -/

section Group

variable {S : Type*} [CommRing S] [Algebra R S] [IsAdicComplete (𝔪.map (algebraMap R S)) S]
  {d : ℕ} (F : FGL R d)

/-- `(t_j ↦ x_j, u_j ↦ y_j)`. -/
def pairS (x y : Fin d → S) : Fin 2 × Fin d → S :=
  fun v => if v.1 = 0 then x v.2 else y v.2

/-- `(t_j ↦ x_j, u_j ↦ y_j, v_j ↦ z_j)`. -/
def tripleS (x y z : Fin d → S) : Fin 3 × Fin d → S :=
  fun v => if v.1 = 0 then x v.2 else if v.1 = 1 then y v.2 else z v.2

variable {𝔪}

omit [IsAdicComplete (𝔪.map (algebraMap R S)) S] in
theorem tnf_pairS {x y : Fin d → S} (hx : TNF 𝔪 x) (hy : TNF 𝔪 y) : TNF 𝔪 (pairS x y) :=
  fun v => by unfold pairS; split_ifs; exacts [hx _, hy _]

omit [IsAdicComplete (𝔪.map (algebraMap R S)) S] in
theorem tnf_tripleS {x y z : Fin d → S} (hx : TNF 𝔪 x) (hy : TNF 𝔪 y) (hz : TNF 𝔪 z) :
    TNF 𝔪 (tripleS x y z) :=
  fun v => by unfold tripleS; split_ifs; exacts [hx _, hy _, hz _]

omit [IsAdicComplete (𝔪.map (algebraMap R S)) S] in
theorem tnf_zero : TNF 𝔪 (0 : Fin d → S) := fun _ => topNil_zero

variable (𝔪) in
/-- **The group law** `x +_F y = Φ(x, y)`. -/
def addE (x y : Fin d → S) : Fin d → S := fun i => evF 𝔪 (pairS x y) (F.Φ i)

theorem tnf_addE {x y : Fin d → S} (hx : TNF 𝔪 x) (hy : TNF 𝔪 y) : TNF 𝔪 (F.addE 𝔪 x y) :=
  fun i => topNil_evF (tnf_pairS hx hy) (F.constantCoeff_Φ i)

/-- `f(x) +_F g(x) = (f +_F g)(x)`. -/
theorem evF_addPS {σ : Type*} [Finite σ] {x : σ → S} (hx : TNF 𝔪 x)
    {f g : Fin d → MvPowerSeries σ R} (hf : NoConst f) (hg : NoConst g) (i : Fin d) :
    evF 𝔪 x (F.addPS f g i) =
      F.addE 𝔪 (fun j => evF 𝔪 x (f j)) (fun j => evF 𝔪 x (g j)) i := by
  rw [addPS, evF_subst hx (fun v => by unfold pairFam; split_ifs; exacts [hf _, hg _])]
  congr 1
  funext v
  unfold pairFam pairS
  split_ifs <;> rfl

theorem evF_pairS_Xv {x y : Fin d → S} (hx : TNF 𝔪 x) (hy : TNF 𝔪 y) (a : Fin 2) (j : Fin d) :
    evF 𝔪 (pairS x y) (Xv (R := R) a j) = if a = 0 then x j else y j := by
  rw [Xv, evF_X (tnf_pairS hx hy)]
  rfl

theorem evF_tripleS_Xv {x y z : Fin d → S} (hx : TNF 𝔪 x) (hy : TNF 𝔪 y) (hz : TNF 𝔪 z)
    (a : Fin 3) (j : Fin d) :
    evF 𝔪 (tripleS x y z) (Xv (R := R) a j) =
      if a = 0 then x j else if a = 1 then y j else z j := by
  rw [Xv, evF_X (tnf_tripleS hx hy hz)]
  rfl

/-- **Associativity.** -/
theorem addE_assoc {x y z : Fin d → S} (hx : TNF 𝔪 x) (hy : TNF 𝔪 y) (hz : TNF 𝔪 z) :
    F.addE 𝔪 (F.addE 𝔪 x y) z = F.addE 𝔪 x (F.addE 𝔪 y z) := by
  have hT := tnf_tripleS hx hy hz
  have h0 := noConst_Xv (R := R) (d := d) (0 : Fin 3)
  have h1 := noConst_Xv (R := R) (d := d) (1 : Fin 3)
  have h2 := noConst_Xv (R := R) (d := d) (2 : Fin 3)
  funext i
  have e' : evF 𝔪 (tripleS x y z) (F.addPS (F.addPS (Xv 0) (Xv 1)) (Xv 2) i) =
      evF 𝔪 (tripleS x y z) (F.addPS (Xv 0) (F.addPS (Xv 1) (Xv 2)) i) := by
    rw [F.addPS_assoc h0 h1 h2]
  rw [F.evF_addPS hT (F.noConst_addPS h0 h1) h2, F.evF_addPS hT h0 (F.noConst_addPS h1 h2)] at e'
  have hxyz : ∀ j, evF 𝔪 (tripleS x y z) (Xv (R := R) 0 j) = x j ∧
      evF 𝔪 (tripleS x y z) (Xv (R := R) 1 j) = y j ∧
      evF 𝔪 (tripleS x y z) (Xv (R := R) 2 j) = z j := fun j => by
    simp only [evF_tripleS_Xv hx hy hz]
    exact ⟨rfl, rfl, rfl⟩
  have eL : (fun j => evF 𝔪 (tripleS x y z) (F.addPS (Xv (R := R) 0) (Xv 1) j)) =
      F.addE 𝔪 x y := by
    funext j
    rw [F.evF_addPS hT h0 h1]
    simp only [fun j => (hxyz j).1, fun j => (hxyz j).2.1]
  have eR : (fun j => evF 𝔪 (tripleS x y z) (F.addPS (Xv (R := R) 1) (Xv 2) j)) =
      F.addE 𝔪 y z := by
    funext j
    rw [F.evF_addPS hT h1 h2]
    simp only [fun j => (hxyz j).2.1, fun j => (hxyz j).2.2]
  rw [eL, eR] at e'
  simpa only [fun j => (hxyz j).1, fun j => (hxyz j).2.2] using e'

/-- **Commutativity.** -/
theorem addE_comm {x y : Fin d → S} (hx : TNF 𝔪 x) (hy : TNF 𝔪 y) :
    F.addE 𝔪 x y = F.addE 𝔪 y x := by
  have hP := tnf_pairS hx hy
  have h0 := noConst_Xv (R := R) (d := d) (0 : Fin 2)
  have h1 := noConst_Xv (R := R) (d := d) (1 : Fin 2)
  funext i
  have e : evF 𝔪 (pairS x y) (F.addPS (Xv 0) (Xv 1) i) =
      evF 𝔪 (pairS x y) (F.addPS (Xv 1) (Xv 0) i) := by
    rw [F.addPS_comm h0 h1]
  rw [F.evF_addPS hP h0 h1, F.evF_addPS hP h1 h0] at e
  simp only [evF_pairS_Xv hx hy] at e
  exact e

/-- **Unit.** -/
theorem addE_zero {x : Fin d → S} (hx : TNF 𝔪 x) : F.addE 𝔪 x 0 = x := by
  funext i
  have e : evF 𝔪 x (F.addPS (fun j => X j) 0 i) = evF 𝔪 x (X i) := by
    rw [F.addPS_zero (noConst_X (R := R) (d := d))]
  rw [F.evF_addPS hx noConst_X noConst_zero, evF_X hx] at e
  have h1 : (fun j => evF 𝔪 x (X j : MvPowerSeries (Fin d) R)) = x := funext (evF_X hx)
  have h2 : (fun j => evF 𝔪 x ((0 : Fin d → MvPowerSeries (Fin d) R) j)) = 0 :=
    funext fun j => evF_zero x
  rw [h1, h2] at e
  exact e

theorem zero_addE {x : Fin d → S} (hx : TNF 𝔪 x) : F.addE 𝔪 0 x = x := by
  rw [F.addE_comm tnf_zero hx, F.addE_zero hx]

/-- **Algebra maps are homomorphisms.** -/
theorem addE_comp {S' : Type*} [CommRing S'] [Algebra R S']
    [IsAdicComplete (𝔪.map (algebraMap R S')) S'] (g : S →ₐ[R] S') {x y : Fin d → S}
    (hx : TNF 𝔪 x) (hy : TNF 𝔪 y) (i : Fin d) :
    g (F.addE 𝔪 x y i) = F.addE 𝔪 (fun j => g (x j)) (fun j => g (y j)) i := by
  rw [addE, evF_comp g (tnf_pairS hx hy)]
  congr 1
  funext v
  unfold pairS
  split_ifs <;> rfl

variable (𝔪) in
/-- `n · x = [n]_F(x)`. -/
def mulE (n : ℕ) (x : Fin d → S) : Fin d → S := fun j => evF 𝔪 x (F.mulPS n j)

theorem tnf_mulE (n : ℕ) {x : Fin d → S} (hx : TNF 𝔪 x) : TNF 𝔪 (F.mulE 𝔪 n x) :=
  fun j => topNil_evF hx (F.constantCoeff_mulPS n j)

theorem mulE_zero (x : Fin d → S) : F.mulE 𝔪 0 x = 0 := by
  funext j
  simp [mulE, mulPS_zero, evF_zero]

theorem mulE_succ (n : ℕ) {x : Fin d → S} (hx : TNF 𝔪 x) :
    F.mulE 𝔪 (n + 1) x = F.addE 𝔪 (F.mulE 𝔪 n x) x := by
  funext j
  rw [mulE, mulPS_succ, F.evF_addPS hx (F.noConst_mulPS n) noConst_X]
  simp only [evF_X hx]
  rfl

theorem mulE_comp {S' : Type*} [CommRing S'] [Algebra R S']
    [IsAdicComplete (𝔪.map (algebraMap R S')) S'] (g : S →ₐ[R] S') (n : ℕ) {x : Fin d → S}
    (hx : TNF 𝔪 x) (j : Fin d) :
    g (F.mulE 𝔪 n x j) = F.mulE 𝔪 n (fun j => g (x j)) j := by
  rw [mulE, evF_comp g hx]
  rfl

theorem addE_addE_comm {a b x y : Fin d → S} (ha : TNF 𝔪 a) (hb : TNF 𝔪 b) (hx : TNF 𝔪 x)
    (hy : TNF 𝔪 y) :
    F.addE 𝔪 (F.addE 𝔪 a b) (F.addE 𝔪 x y) = F.addE 𝔪 (F.addE 𝔪 a x) (F.addE 𝔪 b y) := by
  rw [F.addE_assoc ha hb (F.tnf_addE hx hy), ← F.addE_assoc hb hx hy, F.addE_comm hb hx,
    F.addE_assoc hx hb hy, ← F.addE_assoc ha hx (F.tnf_addE hb hy)]

/-- `[n]` is a homomorphism. -/
theorem mulE_addE (n : ℕ) {x y : Fin d → S} (hx : TNF 𝔪 x) (hy : TNF 𝔪 y) :
    F.mulE 𝔪 n (F.addE 𝔪 x y) = F.addE 𝔪 (F.mulE 𝔪 n x) (F.mulE 𝔪 n y) := by
  induction n with
  | zero => rw [mulE_zero, mulE_zero, mulE_zero, F.addE_zero tnf_zero]
  | succ n ih =>
    rw [F.mulE_succ n (F.tnf_addE hx hy), ih, F.mulE_succ n hx, F.mulE_succ n hy,
      F.addE_addE_comm (F.tnf_mulE n hx) (F.tnf_mulE n hy) hx hy]

/-- `[m]([n] x) = [mn] x`. -/
theorem mulE_mulE (m n : ℕ) {x : Fin d → S} (hx : TNF 𝔪 x) :
    F.mulE 𝔪 m (F.mulE 𝔪 n x) = F.mulE 𝔪 (m * n) x := by
  funext j
  rw [mulE, mulE, ← subst_mulPS, evF_subst hx (F.constantCoeff_mulPS n)]
  rfl

theorem mulE_zero_fam (n : ℕ) : F.mulE 𝔪 n (0 : Fin d → S) = 0 := by
  funext j
  rw [mulE, evF_zero_fam, F.constantCoeff_mulPS, map_zero, Pi.zero_apply]

end Group

end FGL

end PadicHodge
