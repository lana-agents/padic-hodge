/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Law
import PadicHodge.FormalGroup.OC

/-!
# Points of a formal group law on the open unit polydisc of `ℂ_p`

For a formal group law `F` of dimension `d` over a ring `R` (with the discrete topology) and an
algebra map `R → O_{ℂ_p}`, the open polydisc `{x ∈ O_{ℂ_p}^d | |x_j| < 1}` is a commutative monoid
under `x +_F y = Φ(x, y)` (`FGL.Pt`, `instAddCommMonoidPt`): the axioms of `F` are identities of
power series, and evaluation at topologically nilpotent points commutes with substitution
(Mathlib's `MvPowerSeries.eval₂_subst`). This is the group of `O_{ℂ_p}`-valued formal points
`F(m_{ℂ_p})` of [Hong, Cor. 3.2.4], [Stix, Ex. 81 (3)] (inverses are not needed below).
-/

noncomputable section

open MvPowerSeries Topology Filter

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

theorem hasEval_of_norm_lt_one {σ : Type*} [Finite σ] {a : σ → OC p}
    (ha : ∀ s, ‖(a s : ℂ_[p])‖ < 1) : HasEval a :=
  ⟨fun s => isTopologicallyNilpotent_of_norm_lt_one (ha s), by
    rw [Filter.cofinite_eq_bot]; exact tendsto_bot⟩

namespace FGL

variable {R : Type*} [CommRing R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ}

variable (p) in
/-- Evaluation of a power series over `R` at a point of `O_{ℂ_p}^σ`. -/
def ev {σ : Type*} (f : MvPowerSeries σ R) (a : σ → OC p) : OC p :=
  eval₂ (algebraMap R (OC p)) a f

theorem continuous_algebraMap_OC : Continuous (algebraMap R (OC p)) :=
  continuous_of_discreteTopology

omit [DiscreteUniformity R] in
theorem ev_X {σ : Type*} (a : σ → OC p) (s : σ) : ev p (X s : MvPowerSeries σ R) a = a s :=
  eval₂_X _ _ s

theorem ev_zero {σ : Type*} [Finite σ] {a : σ → OC p} (ha : ∀ s, ‖(a s : ℂ_[p])‖ < 1) :
    ev p (0 : MvPowerSeries σ R) a = 0 := by
  rw [ev, ← coe_eval₂Hom continuous_algebraMap_OC (hasEval_of_norm_lt_one ha), map_zero]

/-- Evaluation commutes with substitution. -/
theorem ev_subst {σ τ : Type*} [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) {b : τ → OC p} (hb : ∀ t, ‖(b t : ℂ_[p])‖ < 1)
    (f : MvPowerSeries σ R) :
    ev p (f.subst a) b = ev p f (fun s => ev p (a s) b) :=
  eval₂_subst (hasSubst_of_constantCoeff_zero ha) (hasEval_of_norm_lt_one hb) f

/-- `(t_j ↦ x_j, u_j ↦ y_j)`. -/
def pairPt (x y : Fin d → OC p) : Fin 2 × Fin d → OC p :=
  fun v => if v.1 = 0 then x v.2 else y v.2

theorem norm_pairPt_lt {x y : Fin d → OC p} (hx : ∀ j, ‖(x j : ℂ_[p])‖ < 1)
    (hy : ∀ j, ‖(y j : ℂ_[p])‖ < 1) (v : Fin 2 × Fin d) : ‖(pairPt x y v : ℂ_[p])‖ < 1 := by
  unfold pairPt; split_ifs
  · exact hx _
  · exact hy _

theorem ev_pairFam {τ : Type*} [Finite τ] {f g : Fin d → MvPowerSeries τ R}
    (hf : ∀ j, constantCoeff (f j) = 0) (hg : ∀ j, constantCoeff (g j) = 0)
    {b : τ → OC p} (hb : ∀ t, ‖(b t : ℂ_[p])‖ < 1) (h : MvPowerSeries (Fin 2 × Fin d) R) :
    ev p (h.subst (pairFam f g)) b =
      ev p h (pairPt (fun j => ev p (f j) b) (fun j => ev p (g j) b)) := by
  rw [ev_subst (fun v => by unfold pairFam; split_ifs; exacts [hf _, hg _]) hb]
  congr 1
  funext v
  unfold pairFam pairPt
  split_ifs <;> rfl

omit [UniformSpace R] [DiscreteUniformity R] in
theorem constantCoeff_Xv {n : ℕ} (a : Fin n) (j : Fin d) :
    constantCoeff (Xv (R := R) a j) = 0 := constantCoeff_X _

variable (F : FGL R d)

omit [UniformSpace R] [DiscreteUniformity R] in
theorem constantCoeff_subst_Φ {n : ℕ} (a b : Fin n) (j : Fin d) :
    constantCoeff ((F.Φ j).subst (pairFam (Xv (R := R) a) (Xv b))) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun v => by
      unfold pairFam; split_ifs <;> exact constantCoeff_Xv _ _)
    (fun v => by unfold pairFam; split_ifs <;> exact constantCoeff_Xv _ _) (F.constantCoeff_Φ j)

variable (p) in
/-- The points `F(m_{ℂ_p}) = {x ∈ O_{ℂ_p}^d | |x_j| < 1}`. -/
structure Pt (_F : FGL R d) where
  /-- the coordinates -/
  val : Fin d → OC p
  norm_lt : ∀ j, ‖(val j : ℂ_[p])‖ < 1

/-- A family of reals `< 1` indexed by a finite type has a common bound `r < 1`. -/
theorem exists_bound {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, f i < 1) :
    ∃ r, 0 ≤ r ∧ r < 1 ∧ ∀ i, f i ≤ r := by
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨0, le_rfl, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    exact ⟨max 0 (f i0), le_max_left _ _, max_lt one_pos (hf i0),
      fun i => (hi0 i (Finset.mem_univ _)).trans (le_max_right _ _)⟩

/-- A power series without constant term maps the open polydisc to the open disc. -/
theorem norm_ev_lt {σ : Type*} [Finite σ] {f : MvPowerSeries σ R} (hf : constantCoeff f = 0)
    {a : σ → OC p} (ha : ∀ s, ‖(a s : ℂ_[p])‖ < 1) : ‖(ev p f a : ℂ_[p])‖ < 1 := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_bound (fun s => ‖(a s : ℂ_[p])‖) ha
  refine lt_of_le_of_lt ?_ hr1
  have := norm_eval₂_le continuous_algebraMap_OC (hasEval_of_norm_lt_one ha) f (k := 1) hr0
    hr1.le hr fun m hm => by
      by_contra h0
      have hm0 : m = 0 := by
        rw [not_le, Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at h0
        exact h0
      rw [hm0, coeff_zero_eq_constantCoeff_apply, hf] at hm
      exact hm rfl
  rwa [pow_one] at this

/-- The group law `x +_F y = Φ(x, y)`. -/
def add (x y : F.Pt p) : F.Pt p :=
  ⟨fun i => ev p (F.Φ i) (pairPt x.1 y.1), fun i =>
    norm_ev_lt (F.constantCoeff_Φ i) (norm_pairPt_lt x.2 y.2)⟩

instance : Add (F.Pt p) := ⟨F.add⟩

instance : Zero (F.Pt p) := ⟨⟨0, fun j => by simp⟩⟩

theorem add_val (x y : F.Pt p) (i : Fin d) :
    (x + y).1 i = ev p (F.Φ i) (pairPt x.1 y.1) := rfl

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
@[simp] theorem zero_val (j : Fin d) : (0 : F.Pt p).1 j = 0 := rfl

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
theorem pt_ext {x y : F.Pt p} (h : ∀ j, x.1 j = y.1 j) : x = y := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  obtain rfl : x = y := funext h
  rfl

theorem add_assoc' (x y z : F.Pt p) : x + y + z = x + (y + z) := by
  refine F.pt_ext fun i => ?_
  -- the point `(x, y, z)`
  let b : Fin 3 × Fin d → OC p := fun v =>
    if v.1 = 0 then x.1 v.2 else if v.1 = 1 then y.1 v.2 else z.1 v.2
  have hb : ∀ v, ‖(b v : ℂ_[p])‖ < 1 := fun v => by
    simp only [b]; split_ifs
    exacts [x.2 _, y.2 _, z.2 _]
  have hb0 : ∀ j, ev p (Xv (R := R) (n := 3) 0 j) b = x.1 j := fun j => ev_X b _
  have hb1 : ∀ j, ev p (Xv (R := R) (n := 3) 1 j) b = y.1 j := fun j => ev_X b _
  have hb2 : ∀ j, ev p (Xv (R := R) (n := 3) 2 j) b = z.1 j := fun j => ev_X b _
  have hL : (x + y + z).1 i = ev p ((F.Φ i).subst (pairFam
      (fun j => (F.Φ j).subst (pairFam (Xv (R := R) (n := 3) 0) (Xv 1))) (Xv 2))) b := by
    rw [ev_pairFam (F.constantCoeff_subst_Φ 0 1) (constantCoeff_Xv 2) hb]
    rw [add_val]
    congr 2
    · funext j
      rw [ev_pairFam (constantCoeff_Xv 0) (constantCoeff_Xv 1) hb]
      simp only [hb0, hb1]
      rfl
    · funext j; rw [hb2]
  have hR : (x + (y + z)).1 i = ev p ((F.Φ i).subst (pairFam (Xv (R := R) (n := 3) 0)
      (fun j => (F.Φ j).subst (pairFam (Xv (R := R) (n := 3) 1) (Xv 2))))) b := by
    rw [ev_pairFam (constantCoeff_Xv 0) (F.constantCoeff_subst_Φ 1 2) hb]
    rw [add_val]
    congr 2
    · funext j; rw [hb0]
    · funext j
      rw [ev_pairFam (constantCoeff_Xv 1) (constantCoeff_Xv 2) hb]
      simp only [hb1, hb2]
      rfl
  rw [hL, hR, F.assoc i]

theorem add_zero' (x : F.Pt p) : x + 0 = x := by
  refine F.pt_ext fun i => ?_
  have h : ev p ((F.Φ i).subst (pairFam (fun j => (X j : MvPowerSeries (Fin d) R)) 0)) x.1 =
      ev p (X i : MvPowerSeries (Fin d) R) x.1 := by rw [F.unit_right i]
  rw [ev_pairFam (fun j => constantCoeff_X j) (fun j => by simp) x.2, ev_X] at h
  rw [add_val, ← h]
  congr 2
  · funext j; rw [ev_X]
  · funext j; rw [Pi.zero_apply, ev_zero x.2]; rfl

theorem add_comm' (x y : F.Pt p) : x + y = y + x := by
  refine F.pt_ext fun i => ?_
  have h : ev p ((F.Φ i).subst (pairFam (Xv (R := R) (n := 2) 1) (Xv 0))) (pairPt x.1 y.1) =
      ev p (F.Φ i) (pairPt x.1 y.1) := by rw [F.comm i]
  rw [ev_pairFam (constantCoeff_Xv 1) (constantCoeff_Xv 0) (norm_pairPt_lt x.2 y.2)] at h
  rw [add_val, add_val, ← h]
  congr 2
  · funext j; exact ev_X _ _
  · funext j; exact ev_X _ _

instance instAddCommMonoidPt : AddCommMonoid (F.Pt p) where
  add_assoc := F.add_assoc'
  zero_add x := by rw [F.add_comm', F.add_zero']
  add_zero := F.add_zero'
  add_comm := F.add_comm'
  nsmul := nsmulRec

end FGL

end PadicHodge
