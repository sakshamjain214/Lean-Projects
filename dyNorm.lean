import Mathlib.Tactic
import NkSystemProject.dy

namespace dyNorm

open dy
open dy.dyterm
open dy.dyprf
open dy.proofrule

theorem monotonicity: ∀ X Y : Set dyterm, ∀ t : dyterm,
  Deducible X t → X ⊆ Y → Deducible Y t := by
    intro X Y t hXt hXY
    unfold Deducible at *;
    obtain ⟨π, hπ⟩ := hXt
    use π
    exact subset_trans hπ hXY

/-
Defining cuts in the prof system:
  A proof is a cut iff there is constructor followed by its destructor
-/

inductive isCut : {t : dyterm} → dyprf t → Prop where
| fstPair : ∀ u v μ ν, isCut (fst u v (pairTerms u v μ ν))
| sndPair : ∀ u v μ ν, isCut (snd u v (pairTerms u v μ ν))
| sEncDec : ∀ t k μ ν, isCut (sdecd t k (sencd t k μ ν) ν)
| aEncDec : ∀ t k μ ν ρ, isCut (adecd t k (aencd t k μ ν) ρ)

def IsCut (prf : DYPrf) : Prop :=
  match prf with
  | ⟨_, π⟩ => isCut π

-- The following four lemmas are useful in proving normalization
-- They state what the structure of the major premise of a cut looks like

lemma fst_not_cut : ∀ a b μ,
  isCut (fst a b μ) → (∃ α β, (μ = pairTerms a b α β)) := by
    intro a b μ hCut
    cases hCut
    · rename_i π1 π2
      use π1; use π2

lemma snd_not_cut : ∀ a b μ,
  isCut (snd a b μ) → (∃ α β, (μ = pairTerms a b α β)) := by
    intro a b μ hCut
    cases hCut
    · rename_i π2 π1; use π1;use π2

lemma sdecd_not_cut : ∀ a b μ ν,
  isCut (sdecd a b μ ν) → (∃ α β, (μ = sencd a b α β)) := by
    intro a b μ ν hCut
    cases hCut
    · rename_i π1; use π1; use ν

lemma adecd_not_cut : ∀ a b μ ν,
  isCut (adecd a b μ ν) → (∃ α β, (μ = aencd a b α β)) := by
    intro a b μ ν hCut
    cases hCut
    · rename_i π1 π2; use π1; use π2

/-
Defining Normal Proofs:
  A proof is normal if its premises are normal and it is itself not a cut
-/

inductive isNormal : {t : dyterm} → dyprf t → Prop where
| axNorm : ∀ t π, π = ax t → isNormal π
| pubKeyNorm : ∀ k μ π, π = pubKey k μ → isNormal μ → isNormal π
| pairTermsNorm : ∀ t u μ ν π, π = pairTerms t u μ ν → isNormal μ → isNormal ν → isNormal π
| fstNorm : ∀ t u μ π, π = fst t u μ → isNormal μ → ¬isCut π → isNormal π
| sndNorm : ∀ t u μ π , π = snd t u μ → isNormal μ → ¬isCut π → isNormal π
| sencdNorm : ∀ t u μ ν π, π = sencd t u μ ν → isNormal μ → isNormal ν → isNormal π
| sdecdNorm : ∀ t u μ ν π, π = sdecd t u μ ν → isNormal μ → isNormal ν → ¬isCut π → isNormal π
| aencdNorm : ∀ t u μ ν π, π = aencd t u μ ν → isNormal μ → isNormal ν → isNormal π
| adecdNorm : ∀ t u μ ν π, π = adecd t u μ ν → isNormal μ → isNormal ν → ¬isCut π → isNormal π

def IsNormal (prf : DYPrf) : Prop :=
  match prf with
  | ⟨_, π⟩ => isNormal π

-- IMP LEMMA : The subproof of any normal proof is normal

lemma sp_of_norm : ∀ t u (π : dyprf t) (μ : dyprf u),
  isNormal π → (⟨u, μ⟩ ∈ subproofs π) → isNormal μ := by
    intro t u π μ hπ hSP
    induction hπ
    -- ax
    · rename_i v π heq
      subst π; simp[subproofs] at hSP;
      injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; subst μ
      have h4 : ax v = ax v := by rfl
      exact isNormal.axNorm v (ax v) h4
    --pubKey
    · rename_i k ν π heq hN ih
      subst π; simp[subproofs] at hSP;
      rcases hSP with (hSP | hSP)
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; subst μ
        have h4 : pubKey k ν = pubKey k ν := by rfl
        exact isNormal.pubKeyNorm k ν (pubKey k ν) h4 hN
      · exact ih hSP
    --pairTerms
    · rename_i a b α β π hEq hN1 hN2 ih1 ih2
      subst π; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; subst μ
        have h4 : pairTerms a b α β = pairTerms a b α β := by rfl
        exact isNormal.pairTermsNorm a b α β (pairTerms a b α β) h4 hN1 hN2
      · exact ih1 hSP
      · exact ih2 hSP
    --fst
    · rename_i a b ν π heq hN hC ih
      subst π; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP)
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; subst μ
        have h4 : fst a b ν = fst a b ν := by rfl
        exact isNormal.fstNorm a b ν (fst a b ν) h4 hN hC
      · exact ih hSP
    --snd
    · rename_i a b ν π heq hN hC ih
      subst π; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP)
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; subst μ
        have h4 : snd a b ν = snd a b ν := by rfl
        exact isNormal.sndNorm a b ν (snd a b ν) h4 hN hC
      · exact ih hSP
    --sencd
    · rename_i a b α β π hEq hN1 hN2 ih1 ih2
      subst π; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; subst μ
        have h4 : sencd a b α β = sencd a b α β := by rfl
        exact isNormal.sencdNorm a b α β (sencd a b α β) h4 hN1 hN2
      · exact ih1 hSP
      · exact ih2 hSP
    --sdecd
    · rename_i a b α β π heq hN1 hN2 hC ih1 ih2
      subst π; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; subst μ
        have h4 : sdecd a b α β = sdecd a b α β := by rfl
        exact isNormal.sdecdNorm a b α β (sdecd a b α β) h4 hN1 hN2 hC
      · exact ih1 hSP
      · exact ih2 hSP
    --aencd
    · rename_i a b α β π hEq hN1 hN2 ih1 ih2
      subst π; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; subst μ
        have h4 : aencd a b α β = aencd a b α β := by rfl
        exact isNormal.aencdNorm a b α β (aencd a b α β) h4 hN1 hN2
      · exact ih1 hSP
      · exact ih2 hSP
    --adecd
    · rename_i a b α β π heq hN1 hN2 hC ih1 ih2
      subst π; simp[subproofs] at hSP
      rcases hSP with (hSP | hSP) | hSP
      · injection hSP with h1 h2; subst u; have h3 := eq_of_heq h2; subst μ
        have h4 : adecd a b α β = adecd a b α β := by rfl
        exact isNormal.adecdNorm a b α β (adecd a b α β) h4 hN1 hN2 hC
      · exact ih1 hSP
      · exact ih2 hSP

-- Propositional form of a contractum, unused in this file

inductive contract_prop : {t : dyterm} → dyprf t → dyprf t → Prop
| fstPairContract : ∀ u v μ ν, contract_prop (fst u v (pairTerms u v μ ν)) μ
| sndPairContract : ∀ u v μ ν, contract_prop (snd u v (pairTerms u v μ ν)) ν
| sEncDecContract : ∀ t k μ ν ρ, contract_prop (sdecd t k (sencd t k μ ν) ρ) μ
| aEncDecContract : ∀ t k μ ν ρ, contract_prop (adecd t k (aencd t k μ ν) ρ) μ
| notCut : ∀ π, ¬ isCut π → contract_prop π π

-- Contract function: takes in a dy proof and spits out a normal dy proof

def contract {t : dyterm} (π : dyprf t) : dyprf t :=
  match π with
  | ax u => ax u
  | pubKey k μ => pubKey k (contract μ)
  | pairTerms a b α β => pairTerms a b (contract α) (contract β)
  | fst _ _ ν =>
    match contract ν with
    | pairTerms _ _ α _ => α
    | ν' => fst _ _ ν'
  | snd _ _ ν =>
    match contract ν with
    | pairTerms _ _ _ β => β
    | ν' => snd _ _ ν'
  | sencd _ _ α β => sencd _ _ (contract α) (contract β)
  | sdecd _ _ α β =>
    match contract α with
    | sencd _ _ γ _ => γ
    | α' => sdecd _ _ α' (contract β)
  | aencd _ _ α β => aencd _ _ (contract α) (contract β)
  | adecd _ _ α β =>
    match contract α with
    | aencd _ _ γ _ => γ
    | α' => adecd _ _ α' (contract β)
termination_by structural π

-- On contracting, the proof size either decreases or stays the same

lemma contract_size_red : ∀ t (π μ: dyprf t),
  μ = contract π → prfsize μ ≤ prfsize π := by
    intro t π μ hCon
    induction π
    --ax
    · rename_i u; unfold contract at hCon; rw[hCon]
    --pubKey
    · rename_i k ρ ih; unfold contract at hCon; rw[hCon]; simp[prfsize];
      have hPleaseKillMe : contract ρ = contract ρ := by rfl
      exact ih (contract ρ) hPleaseKillMe
    --pairTerms
    · rename_i c d γ δ ihγ ihδ; unfold contract at hCon; rw[hCon]; simp[prfsize]
      have hKillMe1 : contract γ = contract γ := by ac_rfl
      have hConγ := ihγ (contract γ) hKillMe1
      have hKillMe2 : contract δ = contract δ := by ac_rfl
      have hConδ := ihδ (contract δ) hKillMe2
      omega
    --fst
    · rename_i c d ν ih; unfold contract at hCon
      split at hCon;
      · rename_i α β γ h
        subst β
        symm at h
        have hμ := ih (pairTerms c d μ γ) h
        simp[prfsize] at *
        omega
      · rename_i γ h
        have hObv : contract ν = contract ν := by rfl
        have hμ := ih (contract ν) hObv
        subst μ; simp[prfsize]; exact hμ
    --snd
    · rename_i c d ν ih; unfold contract at hCon
      split at hCon;
      · rename_i α β γ h
        subst γ
        symm at h
        have hμ := ih (pairTerms c d β μ) h
        simp[prfsize] at *
        omega
      · rename_i γ h
        have hObv : contract ν = contract ν := by rfl
        have hμ := ih (contract ν) hObv
        subst μ; simp[prfsize]; exact hμ
    --sencd
    · rename_i c d γ δ ihγ ihδ; unfold contract at hCon; rw[hCon]; simp[prfsize]
      have hKillMe1 : contract γ = contract γ := by ac_rfl
      have hConγ := ihγ (contract γ) hKillMe1
      have hKillMe2 : contract δ = contract δ := by ac_rfl
      have hConδ := ihδ (contract δ) hKillMe2
      omega
    --sdecd
    · rename_i c d γ δ ihγ ihδ; unfold contract at hCon
      split at hCon
      · rename_i ν νc νd hEq; subst νc
        symm at hEq
        have hμ := ihγ (sencd c d μ νd) hEq
        simp[prfsize] at *
        omega
      · rename_i α β
        have hObv : (contract γ) = (contract γ) := by rfl
        have hμ := ihγ (contract γ) hObv
        subst μ
        simp[prfsize] at * ; omega
    --aencd
    · rename_i c d γ δ ihγ ihδ; unfold contract at hCon; rw[hCon]; simp[prfsize]
      have hKillMe1 : contract γ = contract γ := by ac_rfl
      have hConγ := ihγ (contract γ) hKillMe1
      have hKillMe2 : contract δ = contract δ := by ac_rfl
      have hConδ := ihδ (contract δ) hKillMe2
      omega
    --adecd
    · rename_i c d γ δ ihγ ihδ; unfold contract at hCon
      split at hCon
      · rename_i ν νc νd hEq; subst νc
        symm at hEq
        have hμ := ihγ (aencd c d μ νd) hEq
        simp[prfsize] at *
        omega
      · rename_i α β
        have hObv : (contract γ) = (contract γ) := by rfl
        have hμ := ihγ (contract γ) hObv
        subst μ
        simp[prfsize] at * ; omega

-- Normalization : ∀ proofs π, contract(π) is normal

theorem normalization : ∀ t (π : dyprf t), isNormal (contract π) := by
  intro t π
  induction π
  --ax
  · rename_i u; unfold contract;
    have hObv : ax u = ax u := by rfl
    exact isNormal.axNorm u (ax u) hObv
  --pubKey
  · rename_i k ν hNorm ; unfold contract
    have hObv : pubKey k (contract ν) = pubKey k (contract ν) := by ac_rfl
    exact isNormal.pubKeyNorm k (contract ν) (pubKey k (contract ν)) hObv hNorm
  --pairTerms
  · rename_i a b α β hN1 hN2; unfold contract
    have hObv : (pairTerms a b (contract α) (contract β)) = (pairTerms a b (contract α) (contract β)) := by rfl
    exact isNormal.pairTermsNorm a b (contract α) (contract β) (pairTerms a b (contract α) (contract β)) hObv hN1 hN2
  --fst
  · rename_i a b ν hN; unfold contract
    split
    · rename_i γ α β hCon
      rw[hCon] at hN
      have hSP : ⟨a, α⟩ ∈ subproofs (pairTerms a b α β) := by
        simp[subproofs]
      exact sp_of_norm (pair a b) a (pairTerms a b α β) α hN hSP
    · rename_i γ h
      have hObv1 : (fst a b (contract ν)) = (fst a b (contract ν)) := by rfl
      have hObv2 : ¬ isCut (fst a b (contract ν)) := by
        intro hCut; apply fst_not_cut at hCut;
        obtain ⟨α, β, hPair⟩ := hCut
        exact h α β hPair
      exact isNormal.fstNorm a b (contract ν) (fst a b (contract ν)) hObv1 hN hObv2
  --snd
  · rename_i a b ν hN; unfold contract
    split
    · rename_i γ α β hCon
      rw[hCon] at hN
      have hSP : ⟨b, β⟩ ∈ subproofs (pairTerms a b α β) := by
        simp[subproofs]
      exact sp_of_norm (pair a b) b (pairTerms a b α β) β hN hSP
    · rename_i γ h
      have hObv1 : (snd a b (contract ν)) = (snd a b (contract ν)) := by rfl
      have hObv2 : ¬ isCut (snd a b (contract ν)) := by
        intro hCut; apply snd_not_cut at hCut;
        obtain ⟨α, β, hPair⟩ := hCut
        exact h α β hPair
      exact isNormal.sndNorm a b (contract ν) (snd a b (contract ν)) hObv1 hN hObv2
  --sencd
  · rename_i a b α β hN1 hN2; unfold contract
    have hObv : (sencd a b (contract α) (contract β)) = (sencd a b (contract α) (contract β)) := by rfl
    exact isNormal.sencdNorm a b (contract α) (contract β) (sencd a b (contract α) (contract β)) hObv hN1 hN2
  --sdecd
  · rename_i a b α β hN1 hN2; unfold contract
    split
    · rename_i π μ ν heq
      rw[heq] at hN1
      have hSP : ⟨a, μ⟩ ∈ subproofs (sencd a b μ ν) := by
        simp[subproofs]
      exact sp_of_norm (senc a b) a (sencd a b μ ν) μ hN1 hSP
    · rename_i γ h
      have hObv1 : sdecd a b (contract α) (contract β) = sdecd a b (contract α) (contract β) := by rfl
      have hObv2 : ¬ isCut (sdecd a b (contract α) (contract β)) := by
        intro hCut;
        apply sdecd_not_cut at hCut
        obtain ⟨x, y, hSdec⟩ := hCut
        exact h x y hSdec
      exact isNormal.sdecdNorm a b (contract α) (contract β) (sdecd a b (contract α) (contract β)) hObv1 hN1 hN2 hObv2
  --aencd
  · rename_i a b α β hN1 hN2; unfold contract
    have hObv : (aencd a b (contract α) (contract β)) = (aencd a b (contract α) (contract β)) := by rfl
    exact isNormal.aencdNorm a b (contract α) (contract β) (aencd a b (contract α) (contract β)) hObv hN1 hN2
  --adecd
  · rename_i a b α β hN1 hN2; unfold contract
    split
    · rename_i π μ ν heq
      rw[heq] at hN1
      have hSP : ⟨a, μ⟩ ∈ subproofs (aencd a b μ ν) := by
        simp[subproofs]
      exact sp_of_norm (aenc a b) a (aencd a b μ ν) μ hN1 hSP
    · rename_i γ h
      have hObv1 : adecd a b (contract α) (contract β) = adecd a b (contract α) (contract β) := by rfl
      have hObv2 : ¬ isCut (adecd a b (contract α) (contract β)) := by
        intro hCut;
        apply adecd_not_cut at hCut
        obtain ⟨x, y, hSdec⟩ := hCut
        exact h x y hSdec
      exact isNormal.adecdNorm a b (contract α) (contract β) (adecd a b (contract α) (contract β)) hObv1 hN1 hN2 hObv2



def sf_term_set (prf : DYPrf) : Set dyterm := Hypos prf ∪ {Conc prf}

-- theorem subformula_prop : ∀ (prf : DYPrf), dy.Termsin prf ∈ dy.ST (sf_term_set prf) := by
--     rintro ⟨t, π⟩
--     intro hSP hN
--     simp[Conc, dy.ST, Subproofs, sf_term_set, Hypos] at *
--     induction π
--     · rename_i a; simp[subproofs] at hSP;
--       injection hSP with h1 h2; subst u;
--       have h : a ∈ st a := by apply self_st a
--       left; assumption
--     · rename_i k ν ih
--       simp[subproofs]


-- end dyNorm
