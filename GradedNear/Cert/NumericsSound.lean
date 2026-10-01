module

public import LeafCheckCore
public import GradedNear.Cert.NumericsSpec
public import GradedNear.Cert.FastEq
public import GradedNear.LeafNumSound

/-!
# Soundness of the numeric checker `LeafCheckCore.checkNum`

`checkNum_sound`: if the compiled checker accepts the metadata `m` of a leaf `L`
(`LeafCheckCore.checkNum m L = true`), then the leaf's data are valid for its metadata,
`MetaValid m (Leaf.ofCore L)` (`GradedNear/Cert/NumericsSpec.lean`). The checker also certifies
the side conditions that the leaf composition needs: the far profile is one of the two corpus
profiles (`checkNum_profile`), every column's `φ` is nonnegative (`checkNum_phi`),
`L ≥ 3.99` (`checkNum_L`), `η > 0` (`checkNum_eta`), and where the first-family charge uses
`J_new`, the charged family is the far budget's inside family `(n, b)` with `b ≤ p`
(`checkNum_jnew`), the condition under which `J_new` applies.

The proof reads each comparison of rationals as a comparison of reals and uses the soundness of
the enclosures (`GradedNear/LeafNumSound.lean`):
* the memoized tables give the enclosures themselves (`look_memo`: a table entry is the value of
  the function at its key);
* a column's objective is enclosed by `gphi_sound`, or `mem_expI` and `benv_sound` for a hidden
  column (`objAt_sound`); `g/w = g·w⁻¹` and `winv_sound` give the tail; `w_lo_le` the far costs;
* `V_le_vUpper` and `w_lo_le` give the far budget, `jold_sound` and `jnew_sound` the first-family
  charge, `gphi_sound` a reserved family's charge.

The positivity checks of `checkNum` are the side conditions of these lemmas (`λ ≠ 0`, `a ≠ 0`,
`p ≠ 0`, `c₁, c₂ > 0`), and `η > 0` makes `(1 + η/2)·V ≤ (1 + η/2)·vUpper`.
-/

@[expose] public section

namespace GradedNear.Cert

open IntervalCore LeafMetaCore LeafCheckCore Kernel

/-! ## Memoization -/

section Memo

variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α]

/-- Every entry of `memo f ks` is the value of `f` at its key. -/
theorem memo_inv (f : α → Ival) (ks : List α) :
    ∀ k v, (memo f ks)[k]? = some v → v = f k := by
  unfold memo
  suffices h : ∀ (t : Std.HashMap α Ival), (∀ k v, t[k]? = some v → v = f k) →
      ∀ k v, (ks.foldl (fun t k => if t.contains k then t else t.insert k (f k)) t)[k]? =
        some v → v = f k from
    h _ (fun k v hk => by simp at hk)
  induction ks with
  | nil => exact fun t ht => ht
  | cons a ks ih =>
    intro t ht
    simp only [List.foldl_cons]
    apply ih
    split
    · exact ht
    · intro k v hk
      rw [Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i hak
        rw [eq_of_beq hak] at hk
        exact (Option.some.inj hk).symm
      · exact ht k v hk

/-- **A memoized lookup is the value of the function.** -/
theorem look_memo (f : α → Ival) (ks : List α) (k : α) : look f (memo f ks) k = f k := by
  unfold look
  split
  · rename_i v hv
    exact memo_inv f ks k v hv
  · rfl

end Memo

/-! ## Casts -/

theorem cast_Sq : ((Sq : ℚ) : ℝ) = (S : ℝ) := by
  rw [Sq, Rat.cast_intCast]
  rfl

theorem S_nonneg : (0 : ℝ) ≤ (S : ℝ) := by norm_num [S]

/-- `a ≤ b` in `ℚ` read in `ℝ`. -/
theorem cast_le_of_decide {a b : ℚ} (h : decide (a ≤ b) = true) : (a : ℝ) ≤ (b : ℝ) :=
  Rat.cast_le.mpr (of_decide_eq_true h)

/-! ## The tables of a leaf -/

section Tables

variable (m : LeafMeta)

theorem gAt_eq (φ lam : ℚ) : (mkCtx m).gAt φ lam = LeafNumCore.gphi m.L φ lam prec :=
  look_memo _ _ _

theorem bAt_eq (φ p : ℚ) : (mkCtx m).bAt φ p = LeafNumCore.benv φ p prec :=
  look_memo _ _ _

theorem winvL_eq (lam : ℚ) :
    (mkCtx m).winvL lam = LeafNumCore.winv m.prof.c₁ m.prof.c₂ m.prof.θ lam prec :=
  look_memo _ _ _

theorem wLoOf_winv (c₁ c₂ θ lam : ℚ) :
    wLoOf (LeafNumCore.winv c₁ c₂ θ lam prec) = (LeafNumCore.w c₁ c₂ θ lam prec).lo := by
  unfold wLoOf LeafNumCore.w
  dsimp only
  by_cases h : 0 < (LeafNumCore.winv c₁ c₂ θ lam prec).lo
  · simp [h]
  · simp [h]

/-- The table's lower bound for `w(λ)`. -/
theorem wLo_le (hc₁ : 0 < m.prof.c₁) (hc₂ : 0 < m.prof.c₂) (lam : ℚ) :
    ((mkCtx m).wLo lam : ℝ) ≤ (profileFar m.prof).w lam := by
  unfold Ctx.wLo
  rw [winvL_eq, wLoOf_winv]
  exact LeafNumCore.w_lo_le (profileFar m.prof) hc₁ hc₂ lam prec

/-- The table's enclosure of `w(λ)⁻¹`. -/
theorem winv_mem (hc₁ : 0 < m.prof.c₁) (hc₂ : 0 < m.prof.c₂) (lam : ℚ) :
    (profileFar m.prof).winv lam ∈ₗ (mkCtx m).winvL lam := by
  rw [winvL_eq]
  exact LeafNumCore.winv_sound (profileFar m.prof) hc₁ hc₂ lam prec

/-- **A column's objective** is enclosed by `objAt`, for `φ ≥ 0`, `p > 0` and `λ > 0`. -/
theorem objAt_sound (o : Obj) (ho : objOk o = true) {lam : ℚ} (hlam : 0 < lam) :
    objFun m.L o lam ∈ₗ (mkCtx m).objAt o lam := by
  cases o with
  | G φ =>
    show Gphi m.L φ lam ∈ₗ (mkCtx m).gAt φ lam
    rw [gAt_eq]
    exact LeafNumCore.gphi_sound m.L φ lam prec hlam.ne'
  | hidden φ p =>
    simp only [objOk, Bool.and_eq_true, decide_eq_true_eq] at ho
    show Real.exp (-(((m.L : ℝ) - 2 * (T : ℝ)) * lam)) * Benv φ p ∈ₗ
      (LeafNumCore.expI (-((m.L - 2 * LeafNumCore.T) * lam)) prec).mul ((mkCtx m).bAt φ p) prec
    rw [bAt_eq]
    have h := Ival.mem_mul prec (LeafNumCore.mem_expI (-((m.L - 2 * LeafNumCore.T) * lam)) prec)
      (LeafNumCore.benv_sound φ p prec ho.2.ne')
    convert h using 3
    push_cast
    rfl

/-- **One column.** -/
theorem colOk_sound (hc₁ : 0 < m.prof.c₁) (hc₂ : 0 < m.prof.c₂) (c : ColMeta)
    (col : CertCore.Col) (ho : objOk c.obj = true) (h : (mkCtx m).colOk c col = true) :
    (colSem m.L c).Valid (profileFar m.prof).w (Col.ofCore col) := by
  obtain ⟨span, o⟩ := c
  cases span with
  | bin lo hi =>
    simp only [Ctx.colOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hlo, -⟩, hG⟩, hW⟩ := h
    have hmem := objAt_sound m o ho hlo
    have hG' := Rat.cast_le (K := ℝ) |>.mpr hG
    have hW' := Rat.cast_le (K := ℝ) |>.mpr hW
    push_cast [cast_Sq] at hG' hW'
    refine ⟨?_, ?_⟩
    · show (S : ℝ) * objFun m.L o lo ≤ (col.G : ℝ)
      calc (S : ℝ) * objFun m.L o lo ≤ S * (((mkCtx m).objAt o lo).hi : ℝ) :=
            mul_le_mul_of_nonneg_left hmem.2 S_nonneg
        _ ≤ col.G := hG'
    · show (col.W : ℝ) ≤ (S : ℝ) * (profileFar m.prof).w hi
      calc (col.W : ℝ) ≤ S * ((mkCtx m).wLo hi : ℝ) := hW'
        _ ≤ S * (profileFar m.prof).w hi :=
            mul_le_mul_of_nonneg_left (wLo_le m hc₁ hc₂ hi) S_nonneg
  | tail R =>
    simp only [Ctx.colOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hR, hG⟩, hW⟩ := h
    have hmem := Ival.mem_mul prec (objAt_sound m o ho hR) (winv_mem m hc₁ hc₂ R)
    have hG' := Rat.cast_le (K := ℝ) |>.mpr hG
    push_cast [cast_Sq] at hG'
    refine ⟨?_, ?_⟩
    · show (S : ℝ) * (objFun m.L o R / (profileFar m.prof).w R) ≤ (col.G : ℝ)
      rw [FarProfile.w, div_inv_eq_mul]
      calc (S : ℝ) * (objFun m.L o R * (profileFar m.prof).winv R)
          ≤ S * ((((mkCtx m).objAt o R).mul ((mkCtx m).winvL R) prec).hi : ℝ) :=
            mul_le_mul_of_nonneg_left hmem.2 S_nonneg
        _ ≤ col.G := hG'
    · show (col.W : ℝ) ≤ (S : ℝ)
      exact_mod_cast hW

/-- The far weights subtracted from the budget are at least the table's lower bounds. -/
theorem farLower_le (hc₁ : 0 < m.prof.c₁) (hc₂ : 0 < m.prof.c₂) :
    (((mkCtx m).farLower m : ℚ) : ℝ) ≤ farReserved m := by
  unfold Ctx.farLower farReserved
  rw [Rat.cast_add]
  apply add_le_add
  · rcases m.farInside with _ | ⟨n, b⟩
    · simp
    · push_cast
      exact mul_le_mul_of_nonneg_left (wLo_le m hc₁ hc₂ b) (Nat.cast_nonneg n)
  · rcases m.reserved with _ | r
    · simp
    · push_cast
      exact mul_le_mul_of_nonneg_left (wLo_le m hc₁ hc₂ r.hi₂) (Nat.cast_nonneg _)

/-- `List.ofFn` of the ten weights read with `getD` is the list itself. -/
theorem ofFn_getD (l : List ℚ) (h : l.length = 10) :
    List.ofFn (fun i : Fin 10 => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ h2

/-- `V ≤ vUpper` for the metadata's profile. -/
theorem V_le (hc₁ : 0 < m.prof.c₁) (hc₂ : 0 < m.prof.c₂) (hα : m.prof.α.length = 10) :
    (profileFar m.prof).V ≤
      (LeafNumCore.vUpper m.prof.c₁ m.prof.c₂ m.prof.θ m.prof.α prec : ℝ) := by
  have h := LeafNumCore.V_le_vUpper (profileFar m.prof) hc₁ hc₂ prec
  have e : List.ofFn (profileFar m.prof).α = m.prof.α := ofFn_getD _ hα
  rw [e] at h
  exact h

/-- The first-family charge is at most the table's upper bound. -/
theorem firstCharge_le (hpar : firstParamsOk m = true) :
    firstCharge m ≤ (((mkCtx m).firstUpper m : ℚ) : ℝ) := by
  unfold firstCharge Ctx.firstUpper
  unfold firstParamsOk at hpar
  rw [Rat.cast_add]
  rw [Bool.and_eq_true] at hpar
  obtain ⟨hpf, hpr⟩ := hpar
  apply add_le_add
  · cases hf : m.firstInside with
    | none => simp
    | some f =>
      rw [hf] at hpf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpf
      obtain ⟨ha, hp⟩ := hpf
      have hJo := (LeafNumCore.jold_sound m.L f.n f.α f.φ f.a f.p prec ha.ne').2
      unfold firstInsideCharge
      by_cases hu : f.useJnew = true
      · have hJn := (LeafNumCore.jnew_sound m.L f.n f.α f.φ f.a f.p prec ha.ne' hp.ne').2
        simp only [hu, ↓reduceIte, cast_rmin]
        exact min_le_min hJo hJn
      · simp only [hu, ↓reduceIte, Bool.false_eq_true]
        exact hJo
  · cases hr : m.reserved with
    | none => simp
    | some r =>
      rw [hr] at hpr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpr
      push_cast
      rw [gAt_eq]
      exact mul_le_mul_of_nonneg_left (LeafNumCore.gphi_sound m.L r.φ₂ r.lo₂ prec hpr.1.ne').2
        (Nat.cast_nonneg _)

end Tables

/-! ## The checker -/

/-- What `metaOk` checks. -/
theorem metaOk_spec {m : LeafMeta} (h : metaOk m = true) :
    399 / 100 ≤ m.L ∧ 0 < m.eta ∧ m.prof.α.length = 10 ∧ 0 < m.prof.c₁ ∧ 0 < m.prof.c₂ ∧
      (sameProfile m.prof LeafNumCore.inherited || sameProfile m.prof LeafNumCore.retuned) = true ∧
      firstParamsOk m = true ∧ ∀ c ∈ m.cols, objOk c.obj = true := by
  simp only [metaOk, profileOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hL, hη⟩, ⟨⟨⟨hα, hc₁⟩, hc₂⟩, hsame⟩⟩, hpar⟩, hobj⟩, -⟩ := h
  exact ⟨hL, hη, hα, hc₁, hc₂, hsame, hpar, hobj⟩

/-- `metaOk` includes the applicability condition of `J_new` (`jnewOk`). -/
theorem metaOk_jnewOk {m : LeafMeta} (h : metaOk m = true) : jnewOk m = true := by
  simp only [metaOk, Bool.and_eq_true] at h
  exact h.2

/-- What `checkNum` checks, before the columns, the far budget and the first-family charge. -/
theorem checkNum_spec {m : LeafMeta} {L : CertCore.Leaf} (h : checkNum m L = true) :
    m.cols.length = L.cols.length ∧ metaOk m = true ∧ colsOk (mkCtx m) m L = true ∧
      farOk (mkCtx m) m L.F = true ∧ firstOk (mkCtx m) m L.first = true := by
  simp only [checkNum, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hmeta⟩, ⟨hcols, hfar⟩, hfirst⟩ := h
  exact ⟨hlen, hmeta, hcols, hfar, hfirst⟩

/-- **Soundness of the numeric checker**: if `checkNum` accepts the metadata `m` of the leaf `L`,
the leaf's data are valid for its metadata. -/
theorem checkNum_sound (m : LeafMeta) (L : CertCore.Leaf)
    (h : LeafCheckCore.checkNum m L = true) : MetaValid m (Leaf.ofCore L) := by
  obtain ⟨hlen, hmeta, hcols, hfar, hfirst⟩ := checkNum_spec h
  obtain ⟨-, hη, hα, hc₁, hc₂, -, hpar, hobj⟩ := metaOk_spec hmeta
  have hlen' : m.cols.length = (Leaf.ofCore L).cols.length := by
    simp [Leaf.ofCore, hlen]
  refine ⟨hlen', ?_, ?_, ?_⟩
  · -- every column
    intro c
    have hcL : (c : ℕ) < L.cols.length := by
      have := c.isLt
      simpa [Leaf.ofCore] using this
    have hcm : (c : ℕ) < m.cols.length := hlen ▸ hcL
    have hget : (Leaf.ofCore L).cols.get c = Col.ofCore L.cols[(c : ℕ)] := by
      rw [List.get_eq_getElem]
      simp only [Leaf.ofCore, List.getElem_map]
    rw [List.getD_eq_getElem _ _ hcm, hget]
    have hz : (m.cols[(c : ℕ)], L.cols[(c : ℕ)]) ∈ m.cols.zip L.cols := by
      have hlt : (c : ℕ) < (m.cols.zip L.cols).length := by simp [hcm, hcL]
      have hm := List.getElem_mem hlt
      rwa [List.getElem_zip] at hm
    unfold colsOk at hcols
    rw [List.all_eq_true] at hcols
    exact colOk_sound m hc₁ hc₂ _ _ (hobj _ (List.getElem_mem hcm)) (hcols _ hz)
  · -- the far budget
    have hF := cast_le_of_decide hfar
    push_cast [cast_Sq] at hF
    have hV := V_le m hc₁ hc₂ hα
    have hres := farLower_le m hc₁ hc₂
    have hη' : (0 : ℝ) ≤ 1 + (m.eta : ℝ) / 2 := by
      have : (0 : ℝ) < m.eta := by exact_mod_cast hη
      linarith
    show (S : ℝ) * ((1 + (m.eta : ℝ) / 2) * (profileFar m.prof).V - farReserved m) ≤ (L.F : ℝ)
    calc (S : ℝ) * ((1 + (m.eta : ℝ) / 2) * (profileFar m.prof).V - farReserved m)
        ≤ S * ((1 + (m.eta : ℝ) / 2) *
            (LeafNumCore.vUpper m.prof.c₁ m.prof.c₂ m.prof.θ m.prof.α prec : ℝ) -
            ((mkCtx m).farLower m : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ S_nonneg
          have := mul_le_mul_of_nonneg_left hV hη'
          linarith
      _ ≤ L.F := hF
  · -- the first-family charge
    have hJ := cast_le_of_decide hfirst
    push_cast [cast_Sq] at hJ
    show (S : ℝ) * firstCharge m ≤ (L.first : ℝ)
    calc (S : ℝ) * firstCharge m ≤ S * (((mkCtx m).firstUpper m : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left (firstCharge_le m hpar) S_nonneg
      _ ≤ L.first := hJ

/-! ## The side conditions certified by the checker -/

/-- The metadata's profile has the constants of a corpus profile. -/
theorem profileFar_eq_of_same {P : LeafMetaCore.Profile} {Q : LeafNumCore.Profile}
    {R : FarProfile} (hQ : Q.c₁ = R.c₁ ∧ Q.c₂ = R.c₂ ∧ Q.θ = R.θ ∧ Q.α = List.ofFn R.α)
    (h : sameProfile P Q = true) : profileFar P = R := by
  simp only [sameProfile, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨c₁, c₂, θ, α⟩ := R
  obtain ⟨e1, e2, e3, e4⟩ := hQ
  simp only at e1 e2 e3 e4
  unfold profileFar
  rw [h1, h2, h3, e1, e2, e3]
  congr 1
  funext i
  rw [h4, e4, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

/-- **The far profile is a corpus profile.** -/
theorem checkNum_profile (m : LeafMeta) (L : CertCore.Leaf) (h : checkNum m L = true) :
    profileFar m.prof = inherited ∨ profileFar m.prof = retuned := by
  obtain ⟨-, hmeta, -⟩ := checkNum_spec h
  obtain ⟨-, -, -, -, -, hsame, -⟩ := metaOk_spec hmeta
  rw [Bool.or_eq_true] at hsame
  rcases hsame with hs | hs
  · exact Or.inl (profileFar_eq_of_same LeafNumCore.inherited_eq hs)
  · exact Or.inr (profileFar_eq_of_same LeafNumCore.retuned_eq hs)

/-- **Every column's `φ` is nonnegative.** -/
theorem checkNum_phi (m : LeafMeta) (L : CertCore.Leaf) (h : checkNum m L = true) :
    ∀ c ∈ m.cols, 0 ≤ (c.obj.phi : ℝ) := by
  obtain ⟨-, hmeta, -⟩ := checkNum_spec h
  obtain ⟨-, -, -, -, -, -, -, hobj⟩ := metaOk_spec hmeta
  intro c hc
  have ho := hobj c hc
  cases hco : c.obj with
  | G φ =>
    rw [hco] at ho
    simp only [objOk, decide_eq_true_eq] at ho
    simpa [Obj.phi] using ho
  | hidden φ p =>
    rw [hco] at ho
    simp only [objOk, Bool.and_eq_true, decide_eq_true_eq] at ho
    simpa [Obj.phi] using ho.1

/-- **`L ≥ 3.99`.** -/
theorem checkNum_L (m : LeafMeta) (L : CertCore.Leaf) (h : checkNum m L = true) :
    (399 / 100 : ℝ) ≤ (m.L : ℝ) := by
  obtain ⟨-, hmeta, -⟩ := checkNum_spec h
  obtain ⟨hL, -⟩ := metaOk_spec hmeta
  have : ((399 / 100 : ℚ) : ℝ) ≤ (m.L : ℝ) := by exact_mod_cast hL
  simpa using this

/-- **`η > 0`.** -/
theorem checkNum_eta (m : LeafMeta) (L : CertCore.Leaf) (h : checkNum m L = true) :
    0 < (m.eta : ℝ) := by
  obtain ⟨-, hmeta, -⟩ := checkNum_spec h
  obtain ⟨-, hη, -⟩ := metaOk_spec hmeta
  exact_mod_cast hη

/-- **Where `J_new` applies, the charged family is the far budget's inside family, with
`b ≤ p`**: if the first-family charge `f` uses `J_new`, then `farInside = some (f.n, b)` with
`b ≤ p`. -/
theorem checkNum_jnew (m : LeafMeta) (L : CertCore.Leaf) (h : checkNum m L = true) :
    ∀ f, m.firstInside = some f → f.useJnew = true →
      ∃ b : ℚ, m.farInside = some (f.n, b) ∧ (b : ℝ) ≤ (f.p : ℝ) := by
  obtain ⟨-, hmeta, -⟩ := checkNum_spec h
  intro f hf hu
  have hj := metaOk_jnewOk hmeta
  simp only [jnewOk, hf, hu, ↓reduceIte] at hj
  rcases hfar : m.farInside with _ | ⟨n', b⟩
  · simp [hfar] at hj
  · simp only [hfar, Bool.and_eq_true, decide_eq_true_eq] at hj
    exact ⟨b, by rw [hj.1], by exact_mod_cast hj.2⟩

end GradedNear.Cert
