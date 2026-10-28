import Mathlib

-- Based on Chp 2 of Thesis
namespace dy

inductive nameterm where
| mk : ℕ → nameterm
deriving Repr, DecidableEq

inductive keyterm where
| mk : ℕ → keyterm
deriving Repr, DecidableEq

inductive pkterm where
| mk : keyterm → pkterm
deriving Repr, DecidableEq

inductive dyterm where
| name : nameterm → dyterm
| key : keyterm → dyterm
| pk : pkterm → dyterm
| pair : dyterm → dyterm → dyterm
| senc : dyterm → dyterm → dyterm
| aenc : dyterm → pkterm → dyterm

deriving Repr, DecidableEq

open dyterm

def inv : pkterm → keyterm
| .mk k => k

def sz : dyterm → ℕ
| name _ => 1
| key _ => 1
| pk _ => 2
| pair t u => 1 + sz t + sz u
| senc m k => 1 + sz m + sz k
| aenc m _ => 1 + sz m + 2

lemma sz_gt_0 : ∀ t : dyterm, sz t > 0 := by
  intro t ; cases t <;> simp[sz]

def st : dyterm → Set dyterm
| name n => {name n}
| key k => {key k}
| pk k => {pk k}
| pair t u => {pair t u} ∪ (st t) ∪ (st u)
| senc t k => {senc t k} ∪ (st t) ∪ (st k)
| aenc t p => {aenc t p} ∪ st t ∪ {pk p}

def ST (X : Set dyterm) : Set dyterm := {t | ∃ u ∈ X, t ∈ st u}

lemma self_st : ∀ t : dyterm, t ∈ st t := by
  intro t; cases t <;> simp[st]

lemma st_trans : ∀ t u v : dyterm, t ∈ st u → u ∈ st v → t ∈ st v := by
  intro t u v
  induction v generalizing u
  · simp[st]; intro f g; subst_vars; rfl
  · simp[st]; intro f g; subst_vars; rfl
  · simp[st]; intro f g; subst_vars; rfl
  · rename_i a b iha ihb
    simp[st]
    rintro f ((g|g) | g)
    · rw[g] at f; apply f
    · have h : t ∈ st a := by exact iha u f g
      simp[h]
    · have h : t ∈ st b := by exact ihb u f g
      simp[h]
  · rename_i a b iha ihb
    simp[st]
    rintro f ((g|g) | g)
    · rw[g] at f; apply f
    · have h : t ∈ st a := by exact iha u f g
      simp[h]
    · have h : t ∈ st b := by exact ihb u f g
      simp[h]
  · rename_i a p iha
    simp[st]
    rintro f (g | (g|g))
    · rw[g] at f
      simp[st] at f; simp[f]
    · rw[g] at f
      simp[st] at f; simp[f]
    · have h : t ∈ st a := by exact iha u f g
      simp[h]

lemma ST_cong: ∀ X Y : Set dyterm, X ⊆ Y → ST X ⊆ ST Y := by
  intro X Y hXY
  simp[ST]; grind

-- Proof System

inductive dyprf : dyterm → Type
| ax : ∀ t : dyterm, dyprf t
| pubKey : ∀ k : keyterm, dyprf (key k) → dyprf (pk (pkterm.mk k))
| pairTerms : ∀ t u : dyterm, dyprf t → dyprf u → dyprf (pair t u)
-- pairTerms2 : ∀ {t u : dyterm}, dyprf t → dyprf u → dyprf (pair t u)
| fst : ∀ t u : dyterm, dyprf (pair t u) → dyprf t
| snd : ∀ t u : dyterm, dyprf (pair t u) → dyprf u
| sencd : ∀ t u : dyterm, dyprf t → dyprf u → dyprf (senc t u)
| sdecd : ∀ t u : dyterm, dyprf (senc t u) → dyprf u → dyprf t
| aencd : ∀ t : dyterm, ∀ p : pkterm, dyprf t → dyprf (pk p) → dyprf (aenc t p)
| adecd : ∀ t : dyterm, ∀ p : pkterm, dyprf (aenc t p) → dyprf (key (inv p)) → dyprf t
deriving Repr, DecidableEq


def hypos {t : dyterm} : dyprf t → Set dyterm
| .ax t => {t}
| .pubKey _ μ => hypos μ
| .pairTerms _ _ μ ν => hypos μ ∪ hypos ν
| .fst _ _ μ => hypos μ
| .snd _ _ μ => hypos μ
| .sencd _ _ μ ν => hypos μ ∪ hypos ν
| .sdecd _ _ μ ν => hypos μ ∪ hypos ν
| .aencd _ _ μ ν => hypos μ ∪ hypos ν
| .adecd _ _ μ ν => hypos μ ∪ hypos ν

def conc {t : dyterm}: dyprf t → dyterm
| _ => t

def DYPrf := Σ (t : dyterm), dyprf t

def Conc (prf: DYPrf) : dyterm := prf.1

def Hypos (prf: DYPrf) : Set dyterm := hypos prf.2

inductive proofrule where
| prax
| prpubKey
| prpairTerms
| prfst
| prsnd
| prsencd
| prsdecd
| praencd
| pradecd
deriving Repr, DecidableEq

open dyprf
open proofrule

def lrof {t : dyterm} : dyprf t → proofrule
| ax _ => prax
| pubKey _ _ => prpubKey
| pairTerms _ _ _ _ => prpairTerms
| fst _ _ _ => prfst
| snd _ _ _ => prsnd
| sencd _ _ _ _ => prsencd
| sdecd _ _ _ _ => prsdecd
| aencd _ _ _ _ => praencd
| adecd _ _ _ _ => pradecd

def termsin {t} (π : dyprf t) : Set dyterm :=
  match π with
  | ax t => {t}
  | pubKey k μ => {pk (pkterm.mk k)} ∪ termsin μ
  | pairTerms t u μ ν => {pair t u} ∪ termsin μ ∪ termsin ν
  | fst t _ μ => {t} ∪ termsin μ
  | snd _ u μ => {u} ∪ termsin μ
  | sencd t k μ ν  => {senc t k} ∪ termsin μ ∪ termsin ν
  | sdecd t _ μ ν  => {t} ∪ termsin μ ∪ termsin ν
  | aencd t p μ ν  => {aenc t p} ∪ termsin μ ∪ termsin ν
  | adecd t _ μ ν  => {t} ∪ termsin μ ∪ termsin ν

def Termsin (prf : DYPrf) : Set dyterm :=
  match prf with
  | ⟨_, π⟩ => termsin π

lemma conc_in_terms : ∀ t (π : dyprf t), t ∈ termsin π := by
  intro t π ; induction π <;> simp[termsin]

def prfsize {t} (π : dyprf t) : ℕ :=
  match π with
  | ax _ => 1
  | pubKey _ μ => 1 + prfsize μ
  | pairTerms _ _ μ ν => 1 + prfsize μ + prfsize ν
  | fst _ _ μ => 1 + prfsize μ
  | snd _ _ μ => 1 + prfsize μ
  | sencd _ _ μ ν => 1 + prfsize μ + prfsize ν
  | sdecd _ _ μ ν => 1 +  prfsize μ + prfsize ν
  | aencd _ _ μ ν => 1 +  prfsize μ + prfsize ν
  | adecd _ _ μ ν => 1 +  prfsize μ + prfsize ν

def PrfSize (prf : DYPrf) : ℕ :=
  match prf with
  | ⟨_ , π⟩ => prfsize π

lemma prfsize_gt_0 : ∀ t (π : dyprf t), prfsize π > 0 := by
  intro t π; induction π <;> simp[prfsize]


def subproofs {t} (π : dyprf t) : Set DYPrf :=
  match π with
  | ax _ => {⟨_, π⟩}
  | pubKey _ μ => {⟨_, π⟩} ∪ subproofs μ
  | pairTerms _ _ μ ν => {⟨_, π⟩} ∪ subproofs μ ∪ subproofs ν
  | fst _ _ μ => {⟨_, π⟩} ∪ subproofs μ
  | snd _ _ μ => {⟨_, π⟩} ∪ subproofs μ
  | sencd _ _ μ ν => {⟨_, π⟩} ∪ subproofs μ ∪ subproofs ν
  | sdecd _ _ μ ν => {⟨_, π⟩} ∪ subproofs μ ∪ subproofs ν
  | aencd _ _ μ ν => {⟨_, π⟩} ∪ subproofs μ ∪ subproofs ν
  | adecd _ _ μ ν => {⟨_, π⟩} ∪ subproofs μ ∪ subproofs ν

def Subproofs (prf : DYPrf) : Set DYPrf :=
  match prf with
  | ⟨_ , π⟩ => subproofs π

def prop_subproofs {t} (π : dyprf t) : Set DYPrf :=
  match π with
  | ax _ => {}
  | pubKey _ μ =>  subproofs μ
  | pairTerms _ _ μ ν =>  subproofs μ ∪ subproofs ν
  | fst _ _ μ => subproofs μ
  | snd _ _ μ => subproofs μ
  | sencd _ _ μ ν => subproofs μ ∪ subproofs ν
  | sdecd _ _ μ ν => subproofs μ ∪ subproofs ν
  | aencd _ _ μ ν => subproofs μ ∪ subproofs ν
  | adecd _ _ μ ν => subproofs μ ∪ subproofs ν


lemma sp_size : ∀ (prf prf' : DYPrf),
  prf' ∈ Subproofs prf → PrfSize prf' ≤ PrfSize prf := by
    rintro ⟨t, π⟩ ⟨u, μ⟩ -- we know it's a Σ type so we directy introduce the components
    simp[PrfSize, Subproofs]
    intro hSP
    induction π
    --ax
    · rename_i a; simp[subproofs] at *; cases hSP; rfl
    --pubKey
    · rename_i k ν ih; simp[prfsize]; simp[subproofs] at hSP;
      rcases hSP with (hSP | hSP)
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; rw[h3]; simp[prfsize]
      · have hLEQ := ih hSP; omega
    --pairTerms
    · rename_i a b α β ihα ihβ; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; rw[h3]; simp[prfsize]
      · have hLEQ := ihα hSP; omega
      · have hLEQ := ihβ hSP; omega
    --fst
    · rename_i a b ν ih; simp[prfsize]; simp[subproofs] at hSP;
      rcases hSP with (hSP | hSP)
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; rw[h3]; simp[prfsize]
      · have hLEQ := ih hSP; omega
    --snd
    · rename_i a b ν ih; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP)
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; rw[h3]; simp[prfsize]
      · have hLEQ := ih hSP; omega
    --sencd
    · rename_i a b α β ihα ihβ; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; rw[h3]; simp[prfsize]
      · have hLEQ := ihα hSP; omega
      · have hLEQ := ihβ hSP; omega
    --sdecd
    · rename_i a b α β ihα ihβ; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; rw[h3]; simp[prfsize]
      · have hLEQ := ihα hSP; omega
      · have hLEQ := ihβ hSP; omega
    --aencd
    · rename_i a b α β ihα ihβ; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; rw[h3]; simp[prfsize]
      · have hLEQ := ihα hSP; omega
      · have hLEQ := ihβ hSP; omega
    --adecd
    · rename_i a b α β ihα ihβ; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; rw[h3]; simp[prfsize]
      · have hLEQ := ihα hSP; omega
      · have hLEQ := ihβ hSP; omega

lemma prop_sp_size : ∀ (prf prf' : DYPrf),
  prf' ∈ Subproofs prf → prf' ≠ prf → PrfSize prf' < PrfSize prf := by
    rintro ⟨t, π⟩ ⟨u, μ⟩
    simp[PrfSize, Subproofs]
    intro hSP hNE
    induction π
    --ax
    · rename_i a; simp[subproofs] at hSP; contradiction
    --pubKey
    · rename_i k ν ih; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP)
      · contradiction
      · have hObv := sp_size ⟨key k, ν⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize ν := by simp[PrfSize] at hObv; assumption
        omega
    --pairTerms
    · rename_i a b α β ihα ihβ; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · contradiction
      · have hObv := sp_size ⟨a, α⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize α := by simp[PrfSize] at hObv; assumption
        omega
      · have hObv := sp_size ⟨b, β⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize β := by simp[PrfSize] at hObv; assumption
        omega
    --fst
    · rename_i a b ν ih; simp[prfsize]; simp[subproofs] at hSP;
      rcases hSP with (hSP | hSP)
      · contradiction
      · have hObv := sp_size ⟨pair a b, ν⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize ν := by simp[PrfSize] at hObv; assumption
        omega
    --snd
    · rename_i a b ν ih; simp[prfsize]; simp[subproofs] at hSP;
      rcases hSP with (hSP | hSP)
      · contradiction
      · have hObv := sp_size ⟨pair a b, ν⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize ν := by simp[PrfSize] at hObv; assumption
        omega
    --sencd
    · rename_i a b α β ihα ihβ; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · contradiction
      · have hObv := sp_size ⟨a, α⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize α := by simp[PrfSize] at hObv; assumption
        omega
      · have hObv := sp_size ⟨b, β⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize β := by simp[PrfSize] at hObv; assumption
        omega
    --sdecd
    · rename_i a b α β ihα ihβ; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · contradiction
      · have hObv := sp_size ⟨senc a b, α⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize α := by simp[PrfSize] at hObv; assumption
        omega
      · have hObv := sp_size ⟨b, β⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize β := by simp[PrfSize] at hObv; assumption
        omega
    --aencd
    · rename_i a b α β ihα ihβ; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · contradiction
      · have hObv := sp_size ⟨a, α⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize α := by simp[PrfSize] at hObv; assumption
        omega
      · have hObv := sp_size ⟨pk b, β⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize β := by simp[PrfSize] at hObv; assumption
        omega
    --adecd
    · rename_i a b α β ihα ihβ; simp[prfsize]; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · contradiction
      · have hObv := sp_size ⟨aenc a b, α⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize α := by simp[PrfSize] at hObv; assumption
        omega
      · have hObv := sp_size ⟨key (inv b), β⟩ ⟨u, μ⟩ hSP
        have hObv2 : prfsize μ ≤ prfsize β := by simp[PrfSize] at hObv; assumption
        omega


@[simp]
lemma self_sp : ∀ t (π : dyprf t), ⟨_ , π⟩ ∈ subproofs π := by
  intro t π ; induction π <;> simp[subproofs]

lemma sp_trans : ∀ t u v (π : dyprf t) (ϖ : dyprf u) (υ : dyprf v),
  ⟨u, ϖ⟩ ∈ subproofs π → ⟨v, υ⟩ ∈ subproofs ϖ →
  ⟨v, υ⟩ ∈ subproofs π := by
    intro t u v π ϖ υ
    induction π generalizing u ϖ <;>
       intro fsp gsp <;> simp [subproofs] at *
    · cases fsp; simp [subproofs] at *; assumption
    · rename_i α μ ihμ
      rcases fsp with (fsp | fsp)
      · cases fsp ; simp[subproofs] at *; assumption
      · have h : ⟨v, υ⟩ ∈ subproofs μ := by exact ihμ u ϖ fsp gsp
        simp[h]
    · rename_i t' u' α β ihα ihβ
      rcases fsp with ((fsp | fsp) | fsp)
      · cases fsp ; simp[subproofs] at *; assumption
      · have h : ⟨v, υ⟩ ∈ subproofs α := by exact ihα u ϖ fsp gsp
        simp[h]
      · have h : ⟨v, υ⟩ ∈ subproofs β := by exact ihβ u ϖ fsp gsp
        simp[h]
    · rename_i t' u' prf ihp
      rcases fsp with (fsp | fsp)
      · cases fsp ; simp[subproofs] at *; assumption
      · have h : ⟨v, υ⟩ ∈ subproofs prf := by exact ihp u ϖ fsp gsp
        simp[h]
    · rename_i t' u' prf ihp
      rcases fsp with (fsp | fsp)
      · cases fsp ; simp[subproofs] at *; assumption
      · have h : ⟨v, υ⟩ ∈ subproofs prf := by exact ihp u ϖ fsp gsp
        simp[h]
    · rename_i t' u' α β ihα ihβ
      rcases fsp with ((fsp | fsp) | fsp)
      · cases fsp ; simp[subproofs] at *; assumption
      · have h : ⟨v, υ⟩ ∈ subproofs α := by exact ihα u ϖ fsp gsp
        simp[h]
      · have h : ⟨v, υ⟩ ∈ subproofs β := by exact ihβ u ϖ fsp gsp
        simp[h]
    · rename_i t' u' α β ihα ihβ
      rcases fsp with ((fsp | fsp) | fsp)
      · cases fsp ; simp[subproofs] at *; assumption
      · have h : ⟨v, υ⟩ ∈ subproofs α := by exact ihα u ϖ fsp gsp
        simp[h]
      · have h : ⟨v, υ⟩ ∈ subproofs β := by exact ihβ u ϖ fsp gsp
        simp[h]
    · rename_i t' u' α β ihα ihβ
      rcases fsp with ((fsp | fsp) | fsp)
      · cases fsp ; simp[subproofs] at *; assumption
      · have h : ⟨v, υ⟩ ∈ subproofs α := by exact ihα u ϖ fsp gsp
        simp[h]
      · have h : ⟨v, υ⟩ ∈ subproofs β := by exact ihβ u ϖ fsp gsp
        simp[h]
    · rename_i t' u' α β ihα ihβ
      rcases fsp with ((fsp | fsp) | fsp)
      · cases fsp ; simp[subproofs] at *; assumption
      · have h : ⟨v, υ⟩ ∈ subproofs α := by exact ihα u ϖ fsp gsp
        simp[h]
      · have h : ⟨v, υ⟩ ∈ subproofs β := by exact ihβ u ϖ fsp gsp
        simp[h]

def Deducible (X : Set dyterm) (t : dyterm) : Prop :=
  ∃ (π : dyprf t), hypos π ⊆ X

-- We don't need provable because nothing can come from a vacuum

def t : dyterm := name (nameterm.mk 1)
def k : dyterm := key (keyterm.mk 1)
def X : Set dyterm := {senc t k, k}

theorem ex1 : Deducible X t := by
  unfold Deducible
  unfold X
  use sdecd t k (ax (senc t k)) (ax k)
  simp[hypos]; grind

end dy
