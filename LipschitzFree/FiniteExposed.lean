import Mathlib

/-!
# Exposed points of the unit ball of a finite Lipschitz-free space

Personal formalization test around
C. Petitjean, A. Procházka, "On exposed points of Lipschitz free spaces" (2018).
The authors are not associated with this test.

Model (M finite): an element of F(M) is represented by `μ : M → ℝ`;
the unit ball is the set of `μ` such that `∑ μ(z) f(z) ≤ 1` for every
1-Lipschitz function `f`. (Taking `f` constant shows that these `μ`
have total mass zero, like the elements of F(M).)

Main result: for `x ≠ y`, the molecule `m_xy = (δ_x - δ_y)/d(x,y)` is an
exposed point of the unit ball if and only if no point `z ∉ {x,y}`
satisfies `d(x,z) + d(z,y) = d(x,y)`.
-/

open Classical

noncomputable section

namespace FreeSpaceTest

set_option linter.unusedSectionVars false

variable {M : Type*} [MetricSpace M] [Fintype M]

/-! ## Definitions -/

/-- 1-Lipschitz functions. -/
def Lip1 : Set (M → ℝ) := {f | LipschitzWith 1 f}

/-- Duality between `μ` (element of F(M)) and `f` (Lipschitz function). -/
def pair (μ f : M → ℝ) : ℝ := ∑ z, μ z * f z

/-- Norm of F(M) (Kantorovich–Rubinstein norm). -/
def fnorm (μ : M → ℝ) : ℝ := sSup ((fun f => pair μ f) '' Lip1)

/-- Closed unit ball of F(M). -/
def ball1 : Set (M → ℝ) := {μ | ∀ f : M → ℝ, LipschitzWith 1 f → pair μ f ≤ 1}

lemma mem_ball1 {μ : M → ℝ} : μ ∈ (ball1 : Set (M → ℝ)) ↔
    ∀ f : M → ℝ, LipschitzWith 1 f → pair μ f ≤ 1 := Iff.rfl

/-- The molecule `m_xy = (δ_x - δ_y) / d(x,y)`. -/
def mol (x y : M) : M → ℝ :=
  fun z => ((if z = x then 1 else 0) - (if z = y then 1 else 0)) / dist x y

/-! ## Basic lemmas -/

lemma pair_mol (x y : M) (f : M → ℝ) : pair (mol x y) f = (f x - f y) / dist x y := by
  have h : ∀ z, mol x y z * f z
      = ((if z = x then f z else 0) - (if z = y then f z else 0)) / dist x y := by
    intro z
    simp only [mol]
    split_ifs <;> ring
  simp only [pair, h, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma pair_add_smul (μ f h : M → ℝ) (s : ℝ) :
    pair μ (fun w => f w + s * h w) = pair μ f + s * pair μ h := by
  simp only [pair, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun w _ => by ring

lemma abs_sub_le_of_lip {f : M → ℝ} (hf : LipschitzWith 1 f) (a b : M) :
    |f a - f b| ≤ dist a b := by
  have h := hf.dist_le_mul a b
  rwa [Real.dist_eq, NNReal.coe_one, one_mul] at h

lemma sub_le_dist_of_lip {f : M → ℝ} (hf : LipschitzWith 1 f) (a b : M) :
    f a - f b ≤ dist a b :=
  (le_abs_self _).trans (abs_sub_le_of_lip hf a b)

lemma mol_mem {x y : M} (hxy : x ≠ y) : mol x y ∈ (ball1 : Set (M → ℝ)) :=
  mem_ball1.2 fun f hf => by
    rw [pair_mol, div_le_one (dist_pos.2 hxy)]
    exact sub_le_dist_of_lip hf x y

/-- **Every molecule has norm 1.** -/
theorem fnorm_mol {x y : M} (hxy : x ≠ y) : fnorm (mol x y) = 1 := by
  have hd : 0 < dist x y := dist_pos.2 hxy
  have hub : ∀ v ∈ (fun f => pair (mol x y) f) '' (Lip1 : Set (M → ℝ)), v ≤ 1 := by
    rintro _ ⟨f, hf, rfl⟩
    exact (mem_ball1.1 (mol_mem hxy)) f hf
  apply le_antisymm
  · exact csSup_le ⟨_, _, (LipschitzWith.const (0 : ℝ)).weaken zero_le_one, rfl⟩ hub
  · apply le_csSup ⟨1, hub⟩
    refine ⟨fun z => dist z y, LipschitzWith.dist_left y, ?_⟩
    simp only [pair_mol, dist_self, sub_zero]
    exact div_self hd.ne'

/-! ## Easy direction: a point between `x` and `y` prevents `m_xy` from being extreme -/

lemma mol_eq_comb {x y z : M} (hxz : x ≠ z) (hzy : z ≠ y)
    (hz : dist x z + dist z y = dist x y) :
    mol x y = (dist x z / dist x y) • mol x z + (dist z y / dist x y) • mol z y := by
  have h1 : 0 < dist x z := dist_pos.2 hxz
  have h2 : 0 < dist z y := dist_pos.2 hzy
  have h3 : 0 < dist x y := by linarith
  funext w
  simp only [mol, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem mol_not_extreme {x y z : M} (hxz : x ≠ z) (hzy : z ≠ y)
    (hz : dist x z + dist z y = dist x y) :
    mol x y ∉ (ball1 : Set (M → ℝ)).extremePoints ℝ := by
  have h1 : 0 < dist x z := dist_pos.2 hxz
  have h2 : 0 < dist z y := dist_pos.2 hzy
  have h3 : 0 < dist x y := by linarith
  have hxy : x ≠ y := fun h => by subst h; rw [dist_self] at hz; linarith
  intro hext
  rw [mem_extremePoints] at hext
  obtain ⟨-, hext⟩ := hext
  have hseg : mol x y ∈ openSegment ℝ (mol x z) (mol z y) := by
    refine ⟨dist x z / dist x y, dist z y / dist x y, div_pos h1 h3, div_pos h2 h3, ?_, ?_⟩
    · rw [← add_div, hz, div_self h3.ne']
    · exact (mol_eq_comb hxz hzy hz).symm
  obtain ⟨heq, -⟩ := hext (mol x z) (mol_mem hxz) (mol z y) (mol_mem hzy) hseg
  have := congrFun heq z
  simp only [mol, if_neg hxz.symm, if_neg hzy] at this
  have h1' := h1.ne'
  field_simp at this
  norm_num at this
  exact hxy this

/-! ## Hard direction: construction of a function exposing `m_xy` -/

/-- On a finite set, positive quantities have a common positive lower bound. -/
lemma exists_pos_le {ι : Type*} [Fintype ι] (g : ι → ℝ) (P : ι → Prop)
    (hg : ∀ i, P i → 0 < g i) : ∃ ε > 0, ∀ i, P i → ε ≤ g i := by
  by_cases hS : (Finset.univ.filter P).Nonempty
  · refine ⟨(Finset.univ.filter P).inf' hS g, ?_, fun i hi => ?_⟩
    · exact (Finset.lt_inf'_iff hS).2 fun i hi => hg i (Finset.mem_filter.1 hi).2
    · exact Finset.inf'_le g (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  · refine ⟨1, one_pos, fun i hi => absurd ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩ hS⟩

lemma dist_sub_bound (x y z : M) : |dist z y - dist z x| ≤ dist x y := by
  have := abs_dist_sub_le y x z
  rwa [dist_comm y z, dist_comm x z, dist_comm y x] at this

/-- The candidate function: `d/2` at `x`, `-d/2` at `y`, and elsewhere
`(1 - η) (d(z,y) - d(z,x)) / 2`. -/
def expo (η : ℝ) (x y : M) : M → ℝ := fun z =>
  if z = x then dist x y / 2 else if z = y then -(dist x y / 2)
  else (1 - η) * ((dist z y - dist z x) / 2)

section Expo

variable {η : ℝ} {x y : M}

lemma expo_x : expo η x y x = dist x y / 2 := by simp [expo]

lemma expo_y (hxy : x ≠ y) : expo η x y y = -(dist x y / 2) := by
  simp only [expo, if_neg (Ne.symm hxy), ite_true]

lemma expo_z {z : M} (hzx : z ≠ x) (hzy : z ≠ y) :
    expo η x y z = (1 - η) * ((dist z y - dist z x) / 2) := by
  simp only [expo, if_neg hzx, if_neg hzy]

variable (hη0 : 0 < η) (hη1 : η ≤ 1)
  (hS : ∀ z, z ≠ x → z ≠ y → η * dist x y < dist x z + dist z y - dist x y)
include hη0 hη1 hS

lemma case_x {z : M} (hzx : z ≠ x) (hzy : z ≠ y) :
    |dist x y / 2 - (1 - η) * ((dist z y - dist z x) / 2)| < dist x z := by
  have hT := abs_le.1 (dist_sub_bound x y z)
  have hSz := hS z hzx hzy
  have hxz : 0 < dist x z := dist_pos.2 (Ne.symm hzx)
  have hc : dist z x = dist x z := dist_comm z x
  have h1 : η * (dist z y - dist z x) ≤ η * dist x y := mul_le_mul_of_nonneg_left hT.2 hη0.le
  have h2 : (1 - η) * (dist z y - dist z x) ≤ (1 - η) * dist x y :=
    mul_le_mul_of_nonneg_left hT.2 (by linarith)
  have h3 : 0 ≤ η * dist x y := mul_nonneg hη0.le dist_nonneg
  rw [abs_lt]; constructor <;> nlinarith

lemma case_y {z : M} (hzx : z ≠ x) (hzy : z ≠ y) :
    |-(dist x y / 2) - (1 - η) * ((dist z y - dist z x) / 2)| < dist y z := by
  have hT := abs_le.1 (dist_sub_bound x y z)
  have hSz := hS z hzx hzy
  have hyz : 0 < dist y z := dist_pos.2 (Ne.symm hzy)
  have hc : dist z x = dist x z := dist_comm z x
  have hc' : dist y z = dist z y := dist_comm y z
  have h1 : η * (-dist x y) ≤ η * (dist z y - dist z x) := mul_le_mul_of_nonneg_left hT.1 hη0.le
  have h2 : (1 - η) * (-dist x y) ≤ (1 - η) * (dist z y - dist z x) :=
    mul_le_mul_of_nonneg_left hT.1 (by linarith)
  have h3 : 0 ≤ η * dist x y := mul_nonneg hη0.le dist_nonneg
  rw [abs_lt]; constructor <;> nlinarith

lemma case_out {a b : M} (hab : a ≠ b) :
    |(1 - η) * ((dist a y - dist a x) / 2) - (1 - η) * ((dist b y - dist b x) / 2)|
      < dist a b := by
  have h1 := abs_le.1 (abs_dist_sub_le a b y)
  have h2 := abs_le.1 (abs_dist_sub_le a b x)
  have hd : 0 < dist a b := dist_pos.2 hab
  have hq : |(dist a y - dist a x) / 2 - (dist b y - dist b x) / 2| ≤ dist a b := by
    rw [abs_le]; constructor <;> linarith
  rw [show (1 - η) * ((dist a y - dist a x) / 2) - (1 - η) * ((dist b y - dist b x) / 2)
      = (1 - η) * ((dist a y - dist a x) / 2 - (dist b y - dist b x) / 2) by ring,
    abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - η)]
  calc _ ≤ (1 - η) * dist a b := mul_le_mul_of_nonneg_left hq (by linarith)
    _ < dist a b := by nlinarith

/-- The function `expo` is strictly contracting on every pair other than `{x,y}`. -/
lemma expo_strict (hxy : x ≠ y) {a b : M} (hab : a ≠ b)
    (hp : ¬(a = x ∧ b = y)) (hp' : ¬(a = y ∧ b = x)) :
    |expo η x y a - expo η x y b| < dist a b := by
  have ex : expo η x y x = dist x y / 2 := expo_x
  have ey : expo η x y y = -(dist x y / 2) := expo_y hxy
  by_cases hax : a = x
  · have hbx : b ≠ x := fun h => hab (hax.trans h.symm)
    have hby : b ≠ y := fun h => hp ⟨hax, h⟩
    have ea : expo η x y a = dist x y / 2 := by rw [hax]; exact ex
    have da : dist a b = dist x b := by rw [hax]
    rw [ea, expo_z hbx hby, da]
    exact case_x hη0 hη1 hS hbx hby
  by_cases hay : a = y
  · have hbx : b ≠ x := fun h => hp' ⟨hay, h⟩
    have hby : b ≠ y := fun h => hab (hay.trans h.symm)
    have ea : expo η x y a = -(dist x y / 2) := by rw [hay]; exact ey
    have da : dist a b = dist y b := by rw [hay]
    rw [ea, expo_z hbx hby, da]
    exact case_y hη0 hη1 hS hbx hby
  have eza := expo_z (η := η) hax hay
  by_cases hbx : b = x
  · have eb : expo η x y b = dist x y / 2 := by rw [hbx]; exact ex
    have db : dist a b = dist x a := by rw [hbx, dist_comm]
    rw [eza, eb, abs_sub_comm, db]
    exact case_x hη0 hη1 hS hax hay
  by_cases hby : b = y
  · have eb : expo η x y b = -(dist x y / 2) := by rw [hby]; exact ey
    have db : dist a b = dist y a := by rw [hby, dist_comm]
    rw [eza, eb, abs_sub_comm, db]
    exact case_y hη0 hη1 hS hax hay
  rw [eza, expo_z hbx hby]
  exact case_out hη0 hη1 hS hab

lemma expo_lip (hxy : x ≠ y) : LipschitzWith 1 (expo η x y) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, NNReal.coe_one, one_mul]
  by_cases hab : a = b
  · rw [hab]; simp
  by_cases p1 : a = x ∧ b = y
  · rw [p1.1, p1.2, expo_x, expo_y hxy,
      show dist x y / 2 - -(dist x y / 2) = dist x y by ring, abs_of_nonneg dist_nonneg]
  by_cases p2 : a = y ∧ b = x
  · rw [p2.1, p2.2, expo_x, expo_y hxy,
      show -(dist x y / 2) - dist x y / 2 = -dist x y by ring, abs_neg,
      abs_of_nonneg dist_nonneg, dist_comm]
  exact (expo_strict hη0 hη1 hS hxy hab p1 p2).le

end Expo

/-- Choice of the parameter `η` when no point lies between `x` and `y`. -/
lemma exists_eta {x y : M} (hxy : x ≠ y)
    (hnb : ∀ z, z ≠ x → z ≠ y → dist x z + dist z y ≠ dist x y) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∀ z, z ≠ x → z ≠ y → η * dist x y < dist x z + dist z y - dist x y := by
  obtain ⟨ε, hε, hle⟩ := exists_pos_le (fun z => dist x z + dist z y - dist x y)
    (fun z => z ≠ x ∧ z ≠ y) fun z hz =>
      sub_pos.2 (lt_of_le_of_ne (dist_triangle x z y) fun h => hnb z hz.1 hz.2 h.symm)
  have hD : 0 < dist x y := dist_pos.2 hxy
  refine ⟨min 1 (ε / (2 * dist x y)), lt_min one_pos (div_pos hε (by positivity)),
    min_le_left _ _, fun z hzx hzy => ?_⟩
  calc min 1 (ε / (2 * dist x y)) * dist x y ≤ ε / (2 * dist x y) * dist x y :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le
    _ = ε / 2 := by field_simp
    _ < ε := by linarith
    _ ≤ dist x z + dist z y - dist x y := hle z ⟨hzx, hzy⟩

/-- If `f` is 1-Lipschitz, strictly contracting outside `{x,y}`, and
`⟨μ, f⟩ ≥ 1` for some `μ` in the ball, then `μ` kills every `h` with `h x = h y`. -/
lemma pair_eq_zero_of_perturb {x y : M} {μ f : M → ℝ} (hμ : μ ∈ (ball1 : Set (M → ℝ)))
    (hf : LipschitzWith 1 f)
    (hstrict : ∀ a b : M, a ≠ b → ¬(a = x ∧ b = y) → ¬(a = y ∧ b = x) →
      |f a - f b| < dist a b)
    (h1 : 1 ≤ pair μ f) (h : M → ℝ) (hh : h x = h y) : pair μ h = 0 := by
  obtain ⟨ε, hε, hle⟩ := exists_pos_le
    (fun p : M × M => (dist p.1 p.2 - |f p.1 - f p.2|) / (|h p.1 - h p.2| + 1))
    (fun p => p.1 ≠ p.2 ∧ ¬(p.1 = x ∧ p.2 = y) ∧ ¬(p.1 = y ∧ p.2 = x))
    fun p hp => div_pos (sub_pos.2 (hstrict _ _ hp.1 hp.2.1 hp.2.2)) (by positivity)
  have key : ∀ s : ℝ, |s| ≤ ε → LipschitzWith 1 (fun w => f w + s * h w) := by
    intro s hs
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    by_cases hab : a = b
    · rw [hab]; simp
    by_cases p1 : a = x ∧ b = y
    · have : f a + s * h a - (f b + s * h b) = f a - f b := by
        rw [p1.1, p1.2, hh]; ring
      rw [this]; exact abs_sub_le_of_lip hf a b
    by_cases p2 : a = y ∧ b = x
    · have : f a + s * h a - (f b + s * h b) = f a - f b := by
        rw [p2.1, p2.2, hh]; ring
      rw [this]; exact abs_sub_le_of_lip hf a b
    have hg := hle (a, b) ⟨hab, p1, p2⟩
    have hpos : 0 < |h a - h b| + 1 := by positivity
    have hg' : ε * (|h a - h b| + 1) ≤ dist a b - |f a - f b| := by
      have := mul_le_mul_of_nonneg_right hg hpos.le
      rwa [div_mul_cancel₀ _ hpos.ne'] at this
    have hsh : |s| * |h a - h b| ≤ ε * (|h a - h b| + 1) := by
      nlinarith [abs_nonneg (h a - h b), abs_nonneg s]
    calc |f a + s * h a - (f b + s * h b)| = |(f a - f b) + s * (h a - h b)| := by
          congr 1; ring
      _ ≤ |f a - f b| + |s * (h a - h b)| := abs_add_le _ _
      _ = |f a - f b| + |s| * |h a - h b| := by rw [abs_mul]
      _ ≤ dist a b := by linarith
  have A := (mem_ball1.1 hμ) _ (key ε (by rw [abs_of_pos hε]))
  have B := (mem_ball1.1 hμ) _ (key (-ε) (by rw [abs_neg, abs_of_pos hε]))
  rw [pair_add_smul] at A B
  have hz : ε * pair μ h = 0 := by linarith
  rcases mul_eq_zero.1 hz with h0 | h0
  · linarith
  · exact h0

/-- A `μ` that kills every `h` with `h x = h y` and satisfies `⟨μ, f⟩ = 1`
is the molecule `m_xy`. -/
lemma eq_mol_of {x y : M} (hxy : x ≠ y) {μ f : M → ℝ} (hμ : μ ∈ (ball1 : Set (M → ℝ)))
    (hf : LipschitzWith 1 f) (hfxy : f x - f y = dist x y) (h1 : 1 ≤ pair μ f)
    (h0 : ∀ h : M → ℝ, h x = h y → pair μ h = 0) : μ = mol x y := by
  have hz : ∀ z, z ≠ x → z ≠ y → μ z = 0 := fun z hzx hzy => by
    have := h0 (fun w => if w = z then 1 else 0)
      (by simp only [if_neg (Ne.symm hzx), if_neg (Ne.symm hzy)])
    simpa [pair] using this
  have hsum : μ x + μ y = 0 := by
    have := h0 (fun w => (if w = x then 1 else 0) + (if w = y then 1 else 0))
      (by simp only [ite_true, if_neg hxy, if_neg (Ne.symm hxy)]; ring)
    simpa [pair, mul_add, Finset.sum_add_distrib] using this
  have hmy : μ y = -μ x := by linarith
  have hpf : pair μ f = μ x * (f x - f y) := by
    rw [pair, Fintype.sum_eq_add x y hxy (fun w hw => by rw [hz w hw.1 hw.2, zero_mul]), hmy]
    ring
  have hle : pair μ f ≤ 1 := (mem_ball1.1 hμ) f hf
  have hD : 0 < dist x y := dist_pos.2 hxy
  rw [hpf, hfxy] at h1 hle
  have hmx : μ x = 1 / dist x y := by
    field_simp
    linarith
  funext w
  by_cases hwx : w = x
  · rw [hwx, hmx]; simp [mol, hxy]
  by_cases hwy : w = y
  · rw [hwy, hmy, hmx]; simp [mol, Ne.symm hxy]; ring
  · rw [hz w hwx hwy]; simp [mol, hwx, hwy]

/-- **Hard direction**: if no point lies between `x` and `y`, the molecule
`m_xy` is an exposed point of the unit ball. -/
theorem mol_exposed {x y : M} (hxy : x ≠ y)
    (hnb : ∀ z, z ≠ x → z ≠ y → dist x z + dist z y ≠ dist x y) :
    mol x y ∈ (ball1 : Set (M → ℝ)).exposedPoints ℝ := by
  obtain ⟨η, hη0, hη1, hS⟩ := exists_eta hxy hnb
  set f := expo η x y with hfdef
  have hf : LipschitzWith 1 f := expo_lip hη0 hη1 hS hxy
  have hstrict : ∀ a b : M, a ≠ b → ¬(a = x ∧ b = y) → ¬(a = y ∧ b = x) →
      |f a - f b| < dist a b := fun a b hab hp hp' =>
    expo_strict hη0 hη1 hS hxy hab hp hp'
  have hfxy : f x - f y = dist x y := by
    rw [hfdef, expo_x, expo_y hxy]; ring
  let l : (M → ℝ) →L[ℝ] ℝ := ∑ z, f z • ContinuousLinearMap.proj z
  have hl : ∀ ν, l ν = pair ν f := fun ν => by
    simp only [l, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, pair]
    exact Finset.sum_congr rfl fun z _ => mul_comm _ _
  have hlm : pair (mol x y) f = 1 := by
    rw [pair_mol, hfxy, div_self (dist_pos.2 hxy).ne']
  refine ⟨mol_mem hxy, l, fun ν hν => ⟨?_, ?_⟩⟩
  · rw [hl, hl, hlm]; exact (mem_ball1.1 hν) f hf
  · intro hle
    rw [hl, hl, hlm] at hle
    exact eq_mol_of hxy hν hf hfxy hle
      (pair_eq_zero_of_perturb hν hf hstrict hle)

/-- **Theorem (finite case of Petitjean–Procházka 2018).** For `x ≠ y`, the molecule
`m_xy` is an exposed point of the unit ball of F(M) if and only if
no point `z ≠ x, y` lies on a metric segment between `x` and `y`. -/
theorem mol_exposed_iff {x y : M} (hxy : x ≠ y) :
    mol x y ∈ (ball1 : Set (M → ℝ)).exposedPoints ℝ ↔
      ∀ z, z ≠ x → z ≠ y → dist x z + dist z y ≠ dist x y := by
  constructor
  · intro hexp z hzx hzy heq
    exact mol_not_extreme (Ne.symm hzx) hzy heq (exposedPoints_subset_extremePoints hexp)
  · exact mol_exposed hxy

end FreeSpaceTest

-- Checked on 12 Nov 2026 on live.lean-lang.org (Lean v4.36.0-rc2, Mathlib): no errors;
-- both theorems depend only on propext, choice, Quot.sound (no sorry).
#print axioms FreeSpaceTest.fnorm_mol
#print axioms FreeSpaceTest.mol_exposed_iff
