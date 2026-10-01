module

public import GradedNear.Cert.Relaxation

/-!
# The meaning of a leaf's columns (paper §§5–6, 10)

Every column of a leaf LP has one of two meanings (`research/notes/leaf-data-semantics-2026-09-29.md` in the research repository
§2):
* **a bin** `[lo, hi]` with an objective function `g` (ordinary bins `G`, hidden columns
  `t ↦ e^{−At} B_φ(p_h)`, second-family sub-bins `G_{φ₂}`). A character whose parameter lies in the
  bin has mass `1`; its objective is charged at the left end, `G_c ≥ S·g(lo)`, and its far weight
  at the right end, `W_c ≤ S·w(hi)`;
* **a tail** `[R, ∞)` with objective `g`. A character with parameter `λ ≥ R` has mass `w(λ)`;
  the objective is charged per unit mass, `G_c ≥ S·g(R)/w(R)`, and the far cost is `W_c ≤ S`.

`column_bounds`: if `w` decreases and `g` decreases (bins) or `g/w` decreases (tails), a character
with parameter `λ` in its column and cost at most `g(λ) + err` satisfies the per-character
hypotheses of `leaf_relaxation`. `leaf_interpretation` then bounds the total cost of such a
configuration below `1` for a certified leaf.
-/

@[expose] public section

namespace GradedNear.Cert

open Finset

/-- The meaning of a column: a bin `[lo, hi]` or a tail `[R, ∞)`, with its objective function. -/
inductive ColSem
  | bin (lo hi : ℝ) (g : ℝ → ℝ)
  | tail (R : ℝ) (g : ℝ → ℝ)

namespace ColSem

/-- The objective function of a column. -/
def g : ColSem → ℝ → ℝ
  | bin _ _ g => g
  | tail _ g => g

/-- The parameter range of a column. -/
def Contains : ColSem → ℝ → Prop
  | bin lo hi _, lam => lo ≤ lam ∧ lam ≤ hi
  | tail R _, lam => R ≤ lam

/-- The mass of a character with parameter `λ` in the column: `1` in a bin, `w(λ)` in a tail. -/
def mass (w : ℝ → ℝ) : ColSem → ℝ → ℝ
  | bin _ _ _, _ => 1
  | tail _ _, lam => w lam

/-- The column's integer data are valid for its meaning (scaled by `S`): the objective at the left
end (bin) or per unit far weight at `R` (tail), rounded up; the far cost at the right end (bin) or
`1` (tail), rounded down. -/
def Valid (w : ℝ → ℝ) (c : Col) : ColSem → Prop
  | bin lo hi g => (S : ℝ) * g lo ≤ c.G ∧ (c.W : ℝ) ≤ S * w hi
  | tail R g => (S : ℝ) * (g R / w R) ≤ c.G ∧ (c.W : ℝ) ≤ S

/-- The monotonicity a column's meaning needs: `g` decreases on `[lo, ∞)` (bin), `g/w` decreases
on `[R, ∞)` (tail). -/
def Mono (w : ℝ → ℝ) : ColSem → Prop
  | bin lo _ g => ∀ a b, lo ≤ a → a ≤ b → g b ≤ g a
  | tail R g => ∀ a b, R ≤ a → a ≤ b → g b / w b ≤ g a / w a

lemma mass_nonneg {w : ℝ → ℝ} (hwpos : ∀ x, 0 < w x) (s : ColSem) (lam : ℝ) :
    0 ≤ s.mass w lam := by
  cases s with
  | bin => exact zero_le_one
  | tail => exact (hwpos lam).le

end ColSem

/-- **Per-character column bounds.** A character with parameter `λ` in its column and cost at
most `g(λ) + err` is charged at most its column's objective times its mass, and its far weight
`w(λ)` covers its column's far cost times its mass (all scaled by `S`). -/
lemma column_bounds {w : ℝ → ℝ} (hw : Antitone w) (hwpos : ∀ x, 0 < w x) (s : ColSem) (c : Col)
    (hv : s.Valid w c) (hm : s.Mono w) {lam cost err : ℝ} (hin : s.Contains lam)
    (hcost : cost ≤ s.g lam + err) :
    (cost - err) * S ≤ (c.G : ℝ) * s.mass w lam ∧ (c.W : ℝ) * s.mass w lam ≤ w lam * S := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  cases s with
  | bin lo hi g =>
    obtain ⟨hG, hW⟩ := hv
    obtain ⟨hlo, hhi⟩ := hin
    simp only [ColSem.mass, mul_one]
    simp only [ColSem.g] at hcost
    have h1 : g lam ≤ g lo := hm lo lam le_rfl hlo
    have h2 : w hi ≤ w lam := hw hhi
    constructor <;> nlinarith
  | tail R g =>
    obtain ⟨hG, hW⟩ := hv
    simp only [ColSem.Contains] at hin
    simp only [ColSem.mass]
    simp only [ColSem.g] at hcost
    have hwl := hwpos lam
    have hwR := hwpos R
    have h1 : g lam / w lam ≤ g R / w R := hm R lam le_rfl hin
    constructor
    · have h2 : g lam = g lam / w lam * w lam := by field_simp
      calc (cost - err) * S ≤ g lam * S := by nlinarith
        _ = g lam / w lam * w lam * S := by rw [← h2]
        _ ≤ g R / w R * w lam * S := by gcongr
        _ = S * (g R / w R) * w lam := by ring
        _ ≤ (c.G : ℝ) * w lam := mul_le_mul_of_nonneg_right hG hwl.le
    · nlinarith

/-- **A certified leaf bounds the cost of any configuration it describes** (paper §10). Each
character `j` lies in a column `col j` whose integer data are valid for its meaning (`hvalid`,
`hmono`), has parameter `λ_j` in that column, and has cost at most the column's objective at
`λ_j` plus an error `err_j`. Suppose:
* the remaining costs plus the errors fit in `first + final`;
* the far weights `w(λ_j)` sum to at most `F`;
* the count, hidden-count and second-family constraints and every near row hold at the
  masses.

Then the total cost is below `1`. -/
theorem leaf_interpretation {L : Leaf} {T : Tree} {v : ℤ} (hcert : checkLeaf L T = some v)
    (w : ℝ → ℝ) (hw : Antitone w) (hwpos : ∀ x, 0 < w x)
    (sem : Fin L.cols.length → ColSem)
    (hvalid : ∀ c, (sem c).Valid w (L.cols.get c)) (hmono : ∀ c, (sem c).Mono w)
    {ι : Type*} [Fintype ι] (col : ι → Fin L.cols.length) (lam cost err : ι → ℝ)
    (hin : ∀ j, (sem (col j)).Contains (lam j))
    (hcost : ∀ j, cost j ≤ (sem (col j)).g (lam j) + err j)
    (restCost : ℝ)
    (hrest : (restCost + ∑ j, err j) * S ≤ ((L.first + L.final : ℤ) : ℝ))
    (hfar : (∑ j, w (lam j)) * S ≤ L.F)
    (hcount : ∑ j, ((L.cols.get (col j)).C : ℝ) * (sem (col j)).mass w (lam j) ≤ 2 * S)
    (hhidden : ∑ j, ((L.cols.get (col j)).NH : ℝ) * (sem (col j)).mass w (lam j) ≤ L.ng * S)
    (hsecond : ∑ j, ((L.cols.get (col j)).E : ℝ) * (sem (col j)).mass w (lam j) = L.n2 * S)
    (τ : ℕ → ℝ)
    (hrows : ∀ k < L.rows.length, 0 ≤ τ k ∧ τ k ^ 2 ≤ ((L.rows.getD k ⟨1, []⟩).d : ℝ) / S ∧
      rowLHS L (massVec L (fun j => some (col j)) (fun j => (sem (col j)).mass w (lam j))) k
          (τ k) ≤ 1 - τ k ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) :
    restCost + ∑ j, cost j < 1 := by
  have hcoef : ∀ (f : Col → ℤ) j, (colCoef L (fun j => some (col j)) f j : ℝ) =
      (f (L.cols.get (col j)) : ℝ) := fun f j => rfl
  have hb := fun j => column_bounds hw hwpos (sem (col j)) (L.cols.get (col j)) (hvalid (col j))
    (hmono (col j)) (hin j) (hcost j)
  have h := leaf_relaxation hcert (fun j => some (col j))
    (fun j => (sem (col j)).mass w (lam j)) (fun j => cost j - err j) (fun j => w (lam j))
    (restCost + ∑ j, err j)
    (fun j => ColSem.mass_nonneg hwpos _ _)
    (fun j => by rw [hcoef]; exact (hb j).1) hrest
    (fun j => by rw [hcoef]; exact (hb j).2) hfar
    (by simpa only [hcoef] using hcount) (by simpa only [hcoef] using hhidden)
    (by simpa only [hcoef] using hsecond) τ hrows
  have : ∑ j, (cost j - err j) = ∑ j, cost j - ∑ j, err j := Finset.sum_sub_distrib ..
  linarith

end GradedNear.Cert
