import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_sat_to_3occ_sat

open CookLevin.Lang
open EvalCnfCmd (OUTPUT CNF_STREAM encodeLit encodeClause encodeCnf)
open SATStr (WCUR WHD WIDX WSA WSB WTAL flagOf scanBody scanLoop_run cnfOf)
open CnfWellFormed (wfCnfB scanRun encodeCnf_parseTotal parseTotal_of_not_wf botCnf)

/-! ## Semantic reduction: SAT → 3-OCC-SAT using bit-end positions as fresh variables -/

def litLen (l : literal) : Nat := l.2 + 3

lemma encodeLit_length (l : literal) : (encodeLit l).length = litLen l := by
  rcases l with ⟨pol, v⟩
  simp [encodeLit, litLen]

def renameClauseBody : clause → Nat → clause × Nat
  | [], pos => ([], pos)
  | (pol, v) :: rest, pos =>
      let res := renameClauseBody rest (pos + (v + 3))
      ((pol, pos + (v + 2)) :: res.1, res.2)

def renameCnf : cnf → Nat → cnf × Nat
  | [], pos => ([], pos)
  | C :: rest, pos =>
      let r1 := renameClauseBody C pos
      let r2 := renameCnf rest (r1.2 + 1)
      (r1.1 :: r2.1, r2.2)

def litEnds : clause → Nat → List (literal × Nat)
  | [], _ => []
  | (pol, v) :: rest, pos =>
      ((pol, v), pos + (v + 2)) :: litEnds rest (pos + (v + 3))

def cnfLitEnds : cnf → Nat → List (literal × Nat)
  | [], _ => []
  | C :: rest, pos =>
      litEnds C pos ++ cnfLitEnds rest ((renameClauseBody C pos).2 + 1)

def occsOfVar (N : cnf) (v : var) : List Nat :=
  ((cnfLitEnds N 0).filter (fun p => p.1.2 == v)).map Prod.snd

def cycleGo (first prev : Nat) : List Nat → cnf
  | [] => [[(false, prev), (true, first)]]
  | nxt :: tl => [(false, prev), (true, nxt)] :: cycleGo first nxt tl

def cycleForList : List Nat → cnf
  | [] => []
  | k0 :: rest => cycleGo k0 k0 rest

def cycleClauses (N : cnf) (bound : Nat) : cnf :=
  (List.range bound).flatMap (fun v => cycleForList (occsOfVar N v))

def threeOccCnf (N : cnf) (bound : Nat) : cnf :=
  (renameCnf N 0).1 ++ cycleClauses N bound

def threeOccStr (x : List Bool) : List Bool :=
  SATToSATStr.satToStr (threeOccCnf (cnfOf x) (encodeCnf (cnfOf x)).length)

lemma cnfOf_threeOccStr (x : List Bool) :
    cnfOf (threeOccStr x) = threeOccCnf (cnfOf x) (encodeCnf (cnfOf x)).length := by
  show CnfWellFormed.parseTotal
      (strBits (SATToSATStr.satToStr (threeOccCnf (cnfOf x) (encodeCnf (cnfOf x)).length))) = _
  rw [SATToSATStr.strBits_satToStr, CnfWellFormed.parseTotal_encodeCnf]

/-! ### Variable bound and positional properties -/

private lemma renameClauseBody_snd (C : clause) (pos : Nat) :
    (renameClauseBody C pos).2 = pos + (CnfSerialize.clauseBody C).length := by
  induction C generalizing pos with
  | nil => simp [renameClauseBody, CnfSerialize.clauseBody]
  | cons l rest ih =>
      rcases l with ⟨pol, v⟩
      rw [renameClauseBody, CnfSerialize.clauseBody_cons, List.length_append, ih, encodeLit_length]
      simp [litLen]; omega

private lemma renameCnf_snd (N : cnf) (pos : Nat) :
    (renameCnf N pos).2 = pos + (encodeCnf N).length := by
  induction N generalizing pos with
  | nil => simp [renameCnf, encodeCnf]
  | cons C rest ih =>
      rw [renameCnf, CnfSerialize.encodeCnf_cons, List.length_append, ih, renameClauseBody_snd,
        CnfSerialize.encodeClause_eq, List.length_append]
      simp; omega

private lemma var_lt_encodeCnf_length {N : cnf} {C : clause} {l : literal}
    (hC : C ∈ N) (hl : l ∈ C) :
    l.2 < (encodeCnf N).length := by
  induction N with
  | nil => cases hC
  | cons hd tl ih =>
      rw [CnfSerialize.encodeCnf_cons, List.length_append]
      rcases List.mem_cons.mp hC with rfl | htl
      · rw [CnfSerialize.encodeClause_eq, List.length_append]
        have hbody : ∀ {C0 : clause} {l0 : literal}, l0 ∈ C0 →
            l0.2 < (CnfSerialize.clauseBody C0).length := by
          intro C0
          induction C0 with
          | nil => intro _ h; cases h
          | cons a b ihb =>
              intro l0 hl0
              rw [CnfSerialize.clauseBody_cons, List.length_append]
              rcases List.mem_cons.mp hl0 with rfl | hmem
              · have := encodeLit_length l0; unfold litLen at this
                exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 3))
                  (by rw [this]; exact Nat.le_add_right _ _)
              · exact Nat.lt_of_lt_of_le (ihb hmem) (Nat.le_add_left _ _)
        exact Nat.lt_of_lt_of_le (hbody hl) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      · exact Nat.lt_of_lt_of_le (ih htl) (Nat.le_add_left _ _)

private lemma litEnds_bounds (C : clause) (pos : Nat) :
    ∀ p ∈ litEnds C pos, pos ≤ p.2 ∧ p.2 < (renameClauseBody C pos).2 := by
  induction C generalizing pos with
  | nil => intro _ h; cases h
  | cons l rest ih =>
      rcases l with ⟨pol, v⟩
      intro p hp
      simp only [litEnds, List.mem_cons] at hp
      have hge : pos + (v + 3) ≤ (renameClauseBody rest (pos + (v + 3))).2 := by
        rw [renameClauseBody_snd]; omega
      rcases hp with rfl | hrest
      · simp only [renameClauseBody]; omega
      · have ⟨h1, h2⟩ := ih (pos + (v + 3)) p hrest
        simp only [renameClauseBody]; omega

private lemma litEnds_nodup_snd (C : clause) (pos : Nat) :
    ((litEnds C pos).map Prod.snd).Nodup := by
  induction C generalizing pos with
  | nil => simp [litEnds]
  | cons l rest ih =>
      rcases l with ⟨pol, v⟩
      simp only [litEnds, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih (pos + (v + 3))⟩
      intro hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨p, hp, hpeq⟩
      have ⟨h1, _⟩ := litEnds_bounds rest (pos + (v + 3)) p hp
      omega

private lemma cnfLitEnds_bounds (N : cnf) (pos : Nat) :
    ∀ p ∈ cnfLitEnds N pos, pos ≤ p.2 ∧ p.2 < (renameCnf N pos).2 := by
  induction N generalizing pos with
  | nil => intro _ h; cases h
  | cons C rest ih =>
      intro p hp
      simp only [cnfLitEnds, List.mem_append] at hp
      have hge : (renameClauseBody C pos).2 + 1 ≤ (renameCnf rest ((renameClauseBody C pos).2 + 1)).2 := by
        rw [renameCnf_snd]; omega
      have hgeC : pos ≤ (renameClauseBody C pos).2 := by
        rw [renameClauseBody_snd]; omega
      rcases hp with hC | hrest
      · have ⟨h1, h2⟩ := litEnds_bounds C pos p hC
        simp only [renameCnf]; omega
      · have ⟨h1, h2⟩ := ih ((renameClauseBody C pos).2 + 1) p hrest
        simp only [renameCnf]; omega

private lemma cnfLitEnds_nodup_snd (N : cnf) (pos : Nat) :
    ((cnfLitEnds N pos).map Prod.snd).Nodup := by
  induction N generalizing pos with
  | nil => simp [cnfLitEnds]
  | cons C rest ih =>
      simp only [cnfLitEnds, List.map_append, List.nodup_append]
      refine ⟨litEnds_nodup_snd C pos, ih _, ?_⟩
      intro a ha b hb
      rw [List.mem_map] at ha hb
      rcases ha with ⟨pa, hpa, rfl⟩
      rcases hb with ⟨pb, hpb, rfl⟩
      have h1 := (litEnds_bounds C pos pa hpa).2
      have h2 := (cnfLitEnds_bounds rest ((renameClauseBody C pos).2 + 1) pb hpb).1
      omega

private lemma renameClauseBody_vars (C : clause) (pos : Nat) :
    (renameClauseBody C pos).1.map Prod.snd = (litEnds C pos).map Prod.snd := by
  induction C generalizing pos with
  | nil => rfl
  | cons l rest ih =>
      rcases l with ⟨pol, v⟩
      simp [renameClauseBody, litEnds, ih]

private lemma renameCnf_vars (N : cnf) (pos : Nat) :
    (renameCnf N pos).1.flatten.map Prod.snd = (cnfLitEnds N pos).map Prod.snd := by
  induction N generalizing pos with
  | nil => rfl
  | cons C rest ih =>
      simp [renameCnf, cnfLitEnds, renameClauseBody_vars, ih]

private lemma countP_eq_of_map_snd (L : List literal) (u : var) :
    L.countP (fun l => l.2 == u) = (L.map Prod.snd).countP (· == u) := by
  induction L with
  | nil => rfl
  | cons l rest ih => simp [List.countP_cons, ih]

private lemma countP_eq_of_nodup {L : List Nat} (hnodup : L.Nodup) (u : Nat) :
    L.countP (· == u) = if u ∈ L then 1 else 0 := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.countP_cons, ih hnodup.2]
      by_cases hxu : x = u
      · subst hxu; simp [hnodup.1]
      · have hbeq : (x == u) = false := beq_false_of_ne hxu
        have hne : u ≠ x := Ne.symm hxu
        simp [hbeq, hne]

private lemma renameCnf_countP_le_one (N : cnf) (u : var) :
    (renameCnf N 0).1.flatten.countP (fun l => l.2 == u) ≤ 1 := by
  rw [countP_eq_of_map_snd, renameCnf_vars, countP_eq_of_nodup (cnfLitEnds_nodup_snd N 0)]
  split_ifs <;> omega

private lemma cycleGo_countP (first prev : Nat) (L : List Nat) (u : var) :
    (cycleGo first prev L).flatten.countP (fun l => l.2 == u) =
      (if prev = u then 1 else 0) + (if first = u then 1 else 0) +
      2 * L.countP (· == u) := by
  induction L generalizing prev with
  | nil =>
      simp only [cycleGo, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.countP_cons, List.countP_nil, Nat.mul_zero, Nat.add_zero]
      by_cases hp : prev = u <;> by_cases hf : first = u <;> simp [hp, hf]
  | cons nxt tl ih =>
      simp only [cycleGo, List.flatten_cons, List.countP_append, List.countP_cons,
        List.countP_nil]
      rw [ih nxt]
      by_cases hp : prev = u <;> by_cases hn : nxt = u <;> by_cases hf : first = u <;>
        simp [hp, hn, hf] <;> omega

private lemma cycleForList_countP (L : List Nat) (u : var) :
    (cycleForList L).flatten.countP (fun l => l.2 == u) = 2 * L.countP (· == u) := by
  cases L with
  | nil => simp [cycleForList]
  | cons k0 rest =>
      simp only [cycleForList, cycleGo_countP, List.countP_cons]
      by_cases h : k0 = u <;> simp [h] <;> omega

private lemma occsOfVar_nodup (N : cnf) (v : var) : (occsOfVar N v).Nodup := by
  unfold occsOfVar
  have hsub : ((cnfLitEnds N 0).filter (fun p => p.1.2 == v)).Sublist (cnfLitEnds N 0) :=
    List.filter_sublist
  exact (cnfLitEnds_nodup_snd N 0).sublist (hsub.map Prod.snd)

private lemma cnfLitEnds_unique_fst {N : cnf} {p1 p2 : literal × Nat}
    (h1 : p1 ∈ cnfLitEnds N 0) (h2 : p2 ∈ cnfLitEnds N 0) (heq : p1.2 = p2.2) :
    p1 = p2 := by
  have hnd := cnfLitEnds_nodup_snd N 0
  rw [List.mem_iff_getElem] at h1 h2
  rcases h1 with ⟨i1, hi1, rfl⟩
  rcases h2 with ⟨i2, hi2, rfl⟩
  have hfin : (⟨i1, by simp [hi1]⟩ : Fin ((cnfLitEnds N 0).map Prod.snd).length) =
      ⟨i2, by simp [hi2]⟩ := (List.nodup_iff_injective_getElem.mp hnd) (by simp [heq])
  have hi : i1 = i2 := congrArg Fin.val hfin
  subst hi; rfl

private lemma occsOfVar_disjoint {N : cnf} {v1 v2 u : Nat}
    (h1 : u ∈ occsOfVar N v1) (h2 : u ∈ occsOfVar N v2) : v1 = v2 := by
  unfold occsOfVar at h1 h2
  rw [List.mem_map] at h1 h2
  rcases h1 with ⟨p1, hp1, rfl⟩
  rcases h2 with ⟨p2, hp2, hp2eq⟩
  rw [List.mem_filter] at hp1 hp2
  have heq := cnfLitEnds_unique_fst hp1.1 hp2.1 hp2eq.symm
  subst heq
  exact (beq_iff_eq.mp hp1.2).symm.trans (beq_iff_eq.mp hp2.2)

private lemma cycleClauses_countP_le_two (N : cnf) (bound : Nat) (u : var) :
    (cycleClauses N bound).flatten.countP (fun l => l.2 == u) ≤ 2 := by
  have hflat : ∀ (vs : List Nat), vs.Nodup →
      ((vs.flatMap (fun v => cycleForList (occsOfVar N v))).flatten.countP (fun l => l.2 == u)) ≤ 2 := by
    intro vs hnd
    induction vs with
    | nil => simp
    | cons v rest ih =>
        rw [List.nodup_cons] at hnd
        simp only [List.flatMap_cons, List.flatten_append, List.countP_append]
        rw [cycleForList_countP, countP_eq_of_nodup (occsOfVar_nodup N v)]
        by_cases hu : u ∈ occsOfVar N v
        · rw [if_pos hu]
          have hzero : ((rest.flatMap (fun w => cycleForList (occsOfVar N w))).flatten.countP
              (fun l => l.2 == u)) = 0 := by
            rw [List.countP_eq_zero]
            intro l hl
            rw [List.mem_flatten] at hl
            rcases hl with ⟨C, hC, hlC⟩
            rw [List.mem_flatMap] at hC
            rcases hC with ⟨w, hw, hCw⟩
            have hne : w ≠ v := fun heq => hnd.1 (heq ▸ hw)
            have hcnt_pos : 0 < (cycleForList (occsOfVar N w)).flatten.countP (fun l' => l'.2 == l.2) := by
              rw [List.countP_pos_iff]
              exact ⟨l, List.mem_flatten.mpr ⟨C, hCw, hlC⟩, beq_self_eq_true l.2⟩
            rw [cycleForList_countP, countP_eq_of_nodup (occsOfVar_nodup N w)] at hcnt_pos
            have hlmem : l.2 ∈ occsOfVar N w := by
              by_contra hnot; simp [hnot] at hcnt_pos
            simp only [beq_iff_eq]
            intro hequ
            rw [hequ] at hlmem
            exact hne (occsOfVar_disjoint hlmem hu)
          omega
        · rw [if_neg hu]
          have := ih hnd.2; omega
  exact hflat (List.range bound) List.nodup_range

private lemma threeOccCnf_countP_le_three (N : cnf) (bound : Nat) (u : var) :
    (threeOccCnf N bound).flatten.countP (fun l => l.2 == u) ≤ 3 := by
  unfold threeOccCnf
  rw [List.flatten_append, List.countP_append]
  have h1 := renameCnf_countP_le_one N u
  have h2 := cycleClauses_countP_le_two N bound u
  omega

/-! ### Equisatisfiability: `SAT N ↔ SAT (threeOccCnf N bound)` -/

private lemma renameClauseBody_eval (a a' : assgn) (C : clause) (pos : Nat)
    (hagree : ∀ p ∈ litEnds C pos, evalVar a' p.2 = evalVar a p.1.2) :
    evalClause a' (renameClauseBody C pos).1 = evalClause a C := by
  induction C generalizing pos with
  | nil => rfl
  | cons l rest ih =>
      rcases l with ⟨pol, v⟩
      simp only [renameClauseBody, evalClause, List.any_cons]
      have h0 : evalLiteral a' (pol, pos + (v + 2)) = evalLiteral a (pol, v) := by
        have h := hagree ((pol, v), pos + (v + 2)) (by simp [litEnds])
        cases pol <;> simp [evalLiteral, h]
      have hrest : evalClause a' (renameClauseBody rest (pos + (v + 3))).1 = evalClause a rest :=
        ih (pos + (v + 3)) (fun p hp => hagree p (by simp [litEnds, hp]))
      simp only [evalClause] at hrest
      rw [h0, hrest]

private lemma renameCnf_eval (a a' : assgn) (N : cnf) (pos : Nat)
    (hagree : ∀ p ∈ cnfLitEnds N pos, evalVar a' p.2 = evalVar a p.1.2) :
    evalCnf a' (renameCnf N pos).1 = evalCnf a N := by
  induction N generalizing pos with
  | nil => rfl
  | cons C rest ih =>
      simp only [renameCnf, evalCnf, List.all_cons]
      have hC := renameClauseBody_eval a a' C pos (fun p hp =>
        hagree p (List.mem_append_left _ hp))
      have hrest := ih ((renameClauseBody C pos).2 + 1) (fun p hp =>
        hagree p (List.mem_append_right _ hp))
      simp only [evalCnf] at hrest
      rw [hC, hrest]

private lemma evalCnf_append (a : assgn) (N1 N2 : cnf) :
    evalCnf a (N1 ++ N2) = (evalCnf a N1 && evalCnf a N2) := by
  simp [evalCnf, List.all_append]

private lemma cycleGo_eval_of_const (a' : assgn) (b : Bool) (first prev : Nat) (L : List Nat)
    (hf : evalVar a' first = b) (hp : evalVar a' prev = b)
    (hL : ∀ x ∈ L, evalVar a' x = b) :
    evalCnf a' (cycleGo first prev L) = true := by
  induction L generalizing prev with
  | nil =>
      simp only [cycleGo, evalCnf, List.all_cons, List.all_nil, Bool.and_true,
        evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral, hp, hf]
      cases b <;> rfl
  | cons nxt tl ih =>
      simp only [cycleGo, evalCnf, List.all_cons]
      have hn : evalVar a' nxt = b := hL nxt (List.mem_cons_self ..)
      have hhead : evalClause a' [(false, prev), (true, nxt)] = true := by
        simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral, hp, hn]
        cases b <;> rfl
      have htail : evalCnf a' (cycleGo first nxt tl) = true :=
        ih nxt hn (fun x hx => hL x (List.mem_cons_of_mem nxt hx))
      simp only [evalCnf] at htail
      rw [hhead, htail]; rfl

private lemma cycleGo_imp_chain (a' : assgn) (first prev : Nat) (L : List Nat)
    (hsat : evalCnf a' (cycleGo first prev L) = true) :
    (evalVar a' prev = true → evalVar a' first = true ∧ ∀ x ∈ L, evalVar a' x = true) ∧
    (∀ x ∈ L, evalVar a' x = true → evalVar a' first = true) := by
  induction L generalizing prev with
  | nil =>
      simp only [cycleGo, evalCnf, List.all_cons, List.all_nil, Bool.and_true,
        evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral] at hsat
      constructor
      · intro hp; rw [hp] at hsat
        exact ⟨by simpa using hsat, fun _ h => by cases h⟩
      · intro _ h; cases h
  | cons nxt tl ih =>
      simp only [cycleGo, evalCnf, List.all_cons, Bool.and_eq_true] at hsat
      have h1 : evalVar a' prev = true → evalVar a' nxt = true := by
        intro hp
        have hc := hsat.1
        simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral, hp] at hc
        simpa using hc
      have ⟨ih1, ih2⟩ := ih nxt hsat.2
      constructor
      · intro hp
        have hn := h1 hp
        have ⟨hf, htl⟩ := ih1 hn
        exact ⟨hf, fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hxtl
          · exact hn
          · exact htl x hxtl⟩
      · intro x hx hxt
        rcases List.mem_cons.mp hx with rfl | hxtl
        · exact (ih1 hxt).1
        · exact ih2 x hxtl hxt

private lemma cycleForList_all_eq (a' : assgn) (k0 : Nat) (rest : List Nat)
    (hsat : evalCnf a' (cycleForList (k0 :: rest)) = true) :
    ∀ k ∈ k0 :: rest, evalVar a' k = evalVar a' k0 := by
  have ⟨h1, h2⟩ := cycleGo_imp_chain a' k0 k0 rest hsat
  intro k hk
  rcases List.mem_cons.mp hk with rfl | hrest
  · rfl
  · cases hk0 : evalVar a' k0 with
    | true => exact (h1 hk0).2 k hrest
    | false =>
        cases hk' : evalVar a' k with
        | false => rfl
        | true =>
            have := h2 k hrest hk'
            rw [hk0] at this; cases this

private lemma mem_cnfLitEnds_mem_cnf {N : cnf} {pos : Nat} {p : literal × Nat}
    (hp : p ∈ cnfLitEnds N pos) : ∃ C ∈ N, p.1 ∈ C := by
  induction N generalizing pos with
  | nil => cases hp
  | cons C rest ih =>
      simp only [cnfLitEnds, List.mem_append] at hp
      rcases hp with hC | hrest
      · refine ⟨C, List.mem_cons_self .., ?_⟩
        have hlit : ∀ {C0 : clause} {pos0 : Nat}, p ∈ litEnds C0 pos0 → p.1 ∈ C0 := by
          intro C0
          induction C0 with
          | nil => intro _ h; cases h
          | cons l tl ihtl =>
              intro pos0 hm
              rcases l with ⟨pol, v⟩
              simp only [litEnds, List.mem_cons] at hm
              rcases hm with rfl | htl
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _ (ihtl htl)
        exact hlit hC
      · obtain ⟨C', hC', hpC'⟩ := ih hrest
        exact ⟨C', List.mem_cons_of_mem C hC', hpC'⟩

private lemma sat_iff_threeOccCnf (N : cnf) (bound : Nat)
    (hbound : ∀ C ∈ N, ∀ l ∈ C, l.2 < bound) :
    SAT N ↔ SAT (threeOccCnf N bound) := by
  constructor
  · rintro ⟨a, ha⟩
    unfold satisfiesCnf at ha
    let a' : assgn := ((cnfLitEnds N 0).filter (fun p => evalVar a p.1.2)).map Prod.snd
    have ha'_eval : ∀ p ∈ cnfLitEnds N 0, evalVar a' p.2 = evalVar a p.1.2 := by
      intro p hp
      apply Bool.eq_iff_iff.mpr
      simp only [evalVar, a', decide_eq_true_eq]
      constructor
      · intro hmem
        have hmem' : p.2 ∈ List.map Prod.snd ((cnfLitEnds N 0).filter (fun p => decide (p.1.2 ∈ a))) :=
          decide_eq_true_eq.mp hmem
        rw [List.mem_map] at hmem'
        rcases hmem' with ⟨q, hq, hqeq⟩
        rw [List.mem_filter] at hq
        have heq := cnfLitEnds_unique_fst hq.1 hp hqeq
        subst heq
        exact decide_eq_true_eq.mp hq.2
      · intro htr
        apply decide_eq_true_eq.mpr
        rw [List.mem_map]
        exact ⟨p, List.mem_filter.mpr ⟨hp, decide_eq_true_eq.mpr htr⟩, rfl⟩
    refine ⟨a', ?_⟩
    unfold satisfiesCnf threeOccCnf
    rw [evalCnf_append]
    have hren : evalCnf a' (renameCnf N 0).1 = true := by
      rw [renameCnf_eval a a' N 0 ha'_eval]; exact ha
    have hcyc : evalCnf a' (cycleClauses N bound) = true := by
      rw [evalCnf_clause_iff]
      intro C hC
      unfold cycleClauses at hC
      rw [List.mem_flatMap] at hC
      rcases hC with ⟨v, _, hCv⟩
      cases hoc : occsOfVar N v with
      | nil => rw [hoc] at hCv; simp [cycleForList] at hCv
      | cons k0 rest =>
          rw [hoc] at hCv
          have hval : ∀ k ∈ k0 :: rest, evalVar a' k = evalVar a v := by
            intro k hk
            rw [← hoc] at hk
            unfold occsOfVar at hk
            rw [List.mem_map] at hk
            rcases hk with ⟨p, hp, rfl⟩
            rw [List.mem_filter] at hp
            rw [ha'_eval p hp.1, beq_iff_eq.mp hp.2]
          have hall := cycleGo_eval_of_const a' (evalVar a v) k0 k0 rest
            (hval k0 (List.mem_cons_self ..)) (hval k0 (List.mem_cons_self ..))
            (fun x hx => hval x (List.mem_cons_of_mem k0 hx))
          exact (evalCnf_clause_iff a' (cycleGo k0 k0 rest)).mp hall C hCv
    rw [hren, hcyc]; rfl
  · rintro ⟨a', ha'⟩
    unfold satisfiesCnf threeOccCnf at ha'
    rw [evalCnf_append, Bool.and_eq_true] at ha'
    rcases ha' with ⟨hren, hcyc⟩
    let a : assgn := (List.range bound).filter (fun v =>
      match occsOfVar N v with
      | [] => false
      | k0 :: _ => evalVar a' k0)
    have hagree : ∀ p ∈ cnfLitEnds N 0, evalVar a' p.2 = evalVar a p.1.2 := by
      intro p hp
      set v := p.1.2 with hvdef
      have hvlt : v < bound := by
        obtain ⟨C, hC, hpC⟩ := mem_cnfLitEnds_mem_cnf hp
        exact hbound C hC p.1 hpC
      have hp_mem : p.2 ∈ occsOfVar N v := by
        unfold occsOfVar
        rw [List.mem_map]
        exact ⟨p, List.mem_filter.mpr ⟨hp, beq_self_eq_true v⟩, rfl⟩
      cases hoc : occsOfVar N v with
      | nil => rw [hoc] at hp_mem; cases hp_mem
      | cons k0 rest =>
          rw [hoc] at hp_mem
          have hcyc_v : evalCnf a' (cycleForList (k0 :: rest)) = true := by
            rw [evalCnf_clause_iff] at hcyc ⊢
            intro C hC
            apply hcyc
            unfold cycleClauses
            rw [List.mem_flatMap]
            exact ⟨v, List.mem_range.mpr hvlt, by rw [hoc]; exact hC⟩
          have heq := cycleForList_all_eq a' k0 rest hcyc_v p.2 hp_mem
          rw [heq]
          simp only [evalVar, a, decide_eq_decide, List.mem_filter, List.mem_range, hvlt, true_and,
            hoc]
          simp [evalVar]
    refine ⟨a, ?_⟩
    unfold satisfiesCnf
    rw [← renameCnf_eval a a' N 0 hagree]
    exact hren

/-! ## Pure bit-level transducers for Pass 1 (rename) and Pass 2 (cycles) -/

/-- Pass 1 step: `(inLit, gotPol, pos, out)`. -/
def pass1Step : Bool × Bool × Nat × List Nat → Nat → Bool × Bool × Nat × List Nat
  | (true, true, pos, out), c =>
      if c = 1 then (true, true, pos + 1, out)
      else (false, false, pos + 1, out ++ List.replicate pos 1 ++ [0])
  | (true, false, pos, out), c =>
      if c = 1 then (true, true, pos + 1, out ++ [1])
      else (true, true, pos + 1, out ++ [0])
  | (false, _, pos, out), c =>
      if c = 1 then (true, false, pos + 1, out ++ [1])
      else (false, false, pos + 1, out ++ [0])

def pass1Run (l : List Nat) : Bool × Bool × Nat × List Nat :=
  l.foldl pass1Step (false, false, 0, [])

private def pass1Take (l : List Nat) (i : Nat) : Bool × Bool × Nat × List Nat :=
  (l.take i).foldl pass1Step (false, false, 0, [])

private lemma pass1Take_succ (l : List Nat) (i : Nat) (hi : i < l.length) :
    pass1Take l (i + 1) = pass1Step (pass1Take l i) l[i] := by
  unfold pass1Take
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma pass1Take_pos (l : List Nat) (i : Nat) (hi : i ≤ l.length) :
    (pass1Take l i).2.2.1 = i := by
  induction i with
  | zero => rfl
  | succ k ih =>
      rw [pass1Take_succ l k (by omega)]
      have hprev := ih (by omega)
      rcases h : pass1Take l k with ⟨a, b, p, out⟩
      rw [h] at hprev; dsimp only at hprev; subst hprev
      cases a <;> cases b <;> dsimp only [pass1Step] <;> split_ifs <;> rfl

private lemma pass1Step_ones (m pos : Nat) (out : List Nat) :
    (List.replicate m 1).foldl pass1Step (true, true, pos, out) = (true, true, pos + m, out) := by
  induction m generalizing pos with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.foldl_cons]
      simp only [pass1Step, ↓reduceIte]
      rw [ih (pos + 1)]
      simp only [Nat.add_assoc, Nat.add_comm 1 k]

private lemma pass1Step_encodeLit (l : literal) (b : Bool) (pos : Nat) (out : List Nat) :
    (encodeLit l).foldl pass1Step (false, b, pos, out) =
      (false, false, pos + (l.2 + 3), out ++ encodeLit (l.1, pos + (l.2 + 2))) := by
  rcases l with ⟨pol, v⟩
  unfold encodeLit
  rw [List.foldl_cons, List.foldl_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
  cases pol with
  | false =>
      change (pass1Step ((List.replicate v 1).foldl pass1Step (true, true, pos + 1 + 1, out ++ [1] ++ [0])) 0) = _
      rw [pass1Step_ones]
      simp only [pass1Step, Nat.zero_ne_one, ↓reduceIte, encodeLit, List.append_assoc,
        List.cons_append, List.nil_append, Prod.mk.injEq, true_and]
      exact ⟨by omega, by rw [show pos + 1 + 1 + v = pos + (v + 2) by omega]; simp [List.append_assoc]⟩
  | true =>
      change (pass1Step ((List.replicate v 1).foldl pass1Step (true, true, pos + 1 + 1, out ++ [1] ++ [1])) 0) = _
      rw [pass1Step_ones]
      simp only [pass1Step, Nat.zero_ne_one, ↓reduceIte, encodeLit, List.append_assoc,
        List.cons_append, List.nil_append, Prod.mk.injEq, true_and]
      exact ⟨by omega, by rw [show pos + 1 + 1 + v = pos + (v + 2) by omega]⟩

private lemma pass1Step_clauseBody (C : clause) (b : Bool) (pos : Nat) (out : List Nat) :
    ∃ b', (CnfSerialize.clauseBody C).foldl pass1Step (false, b, pos, out) =
      (false, b', (renameClauseBody C pos).2, out ++ CnfSerialize.clauseBody (renameClauseBody C pos).1) := by
  induction C generalizing b pos out with
  | nil => exact ⟨b, by simp [CnfSerialize.clauseBody, renameClauseBody]⟩
  | cons l rest ih =>
      rcases l with ⟨pol, v⟩
      rw [CnfSerialize.clauseBody_cons, List.foldl_append, pass1Step_encodeLit]
      obtain ⟨b', hb'⟩ := ih false (pos + (v + 3)) (out ++ encodeLit (pol, pos + (v + 2)))
      refine ⟨b', ?_⟩
      rw [hb']
      simp only [renameClauseBody, CnfSerialize.clauseBody_cons, List.append_assoc]

private lemma pass1Step_encodeClause (C : clause) (b : Bool) (pos : Nat) (out : List Nat) :
    (encodeClause C).foldl pass1Step (false, b, pos, out) =
      (false, false, (renameClauseBody C pos).2 + 1, out ++ encodeClause (renameClauseBody C pos).1) := by
  rw [CnfSerialize.encodeClause_eq, List.foldl_append]
  obtain ⟨b', hb'⟩ := pass1Step_clauseBody C b pos out
  rw [hb', List.foldl_cons, List.foldl_nil]
  simp only [pass1Step, Nat.zero_ne_one, ↓reduceIte]
  rw [CnfSerialize.encodeClause_eq, List.append_assoc]

private lemma pass1Step_encodeCnf (N : cnf) (pos : Nat) (out : List Nat) :
    (encodeCnf N).foldl pass1Step (false, false, pos, out) =
      (false, false, (renameCnf N pos).2, out ++ encodeCnf (renameCnf N pos).1) := by
  induction N generalizing pos out with
  | nil => simp [encodeCnf, renameCnf]
  | cons C rest ih =>
      rw [CnfSerialize.encodeCnf_cons, List.foldl_append, pass1Step_encodeClause, ih]
      simp only [renameCnf, CnfSerialize.encodeCnf_cons, List.append_assoc]

private lemma pass1Run_encodeCnf (N : cnf) :
    (pass1Run (encodeCnf N)).2.2.2 = encodeCnf (renameCnf N 0).1 := by
  unfold pass1Run
  rw [pass1Step_encodeCnf]
  simp

/-- Pass 2 inner step for a fixed target variable `v`. -/
structure P2State where
  inLit : Bool
  gotPol : Bool
  pos : Nat
  curV : Nat
  hasF : Bool
  first : Nat
  prev : Nat
  out : List Nat

def emitImplBits (prev nxt : Nat) : List Nat :=
  encodeClause [(false, prev), (true, nxt)]

def pass2Step (v : Nat) (st : P2State) (c : Nat) : P2State :=
  if st.inLit then
    if st.gotPol then
      if c = 1 then
        { st with pos := st.pos + 1, curV := st.curV + 1 }
      else
        if st.curV = v then
          if st.hasF then
            { inLit := false, gotPol := false, pos := st.pos + 1, curV := 0,
              hasF := true, first := st.first, prev := st.pos,
              out := st.out ++ emitImplBits st.prev st.pos }
          else
            { inLit := false, gotPol := false, pos := st.pos + 1, curV := 0,
              hasF := true, first := st.pos, prev := st.pos, out := st.out }
        else
          { st with inLit := false, gotPol := false, pos := st.pos + 1, curV := 0 }
    else
      { st with gotPol := true, pos := st.pos + 1 }
  else
    if c = 1 then
      { st with inLit := true, gotPol := false, pos := st.pos + 1, curV := 0 }
    else
      { st with gotPol := false, pos := st.pos + 1 }

def pass2Init (out : List Nat) : P2State :=
  { inLit := false, gotPol := false, pos := 0, curV := 0,
    hasF := false, first := 0, prev := 0, out := out }

def pass2Finish (st : P2State) : List Nat :=
  if st.hasF then st.out ++ emitImplBits st.prev st.first else st.out

def pass2VarOut (v : Nat) (l out : List Nat) : List Nat :=
  pass2Finish (l.foldl (pass2Step v) (pass2Init out))

private def pass2Take (v : Nat) (l out : List Nat) (i : Nat) : P2State :=
  (l.take i).foldl (pass2Step v) (pass2Init out)

private lemma pass2Take_succ (v : Nat) (l out : List Nat) (i : Nat) (hi : i < l.length) :
    pass2Take v l out (i + 1) = pass2Step v (pass2Take v l out i) l[i] := by
  unfold pass2Take
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma pass2Take_pos (v : Nat) (l out : List Nat) (i : Nat) (hi : i ≤ l.length) :
    (pass2Take v l out i).pos = i := by
  induction i with
  | zero => rfl
  | succ k ih =>
      rw [pass2Take_succ v l out k (by omega)]
      have hprev := ih (by omega)
      unfold pass2Step
      split_ifs <;> simp [hprev]

private lemma pass2Step_ones (v m : Nat) (st : P2State) (hi : st.inLit = true) (hg : st.gotPol = true) :
    (List.replicate m 1).foldl (pass2Step v) st = { st with pos := st.pos + m, curV := st.curV + m } := by
  induction m generalizing st with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.foldl_cons]
      have h1 : pass2Step v st 1 = { st with pos := st.pos + 1, curV := st.curV + 1 } := by
        simp [pass2Step, hi, hg]
      rw [h1, ih { st with pos := st.pos + 1, curV := st.curV + 1 } hi hg]
      simp only [Nat.add_assoc, Nat.add_comm 1 k]

private def occStep (v : Nat) (st : Bool × Nat × Nat × List Nat) (p : literal × Nat) :
    Bool × Nat × Nat × List Nat :=
  if p.1.2 = v then
    if st.1 then
      (true, st.2.1, p.2, st.2.2.2 ++ emitImplBits st.2.2.1 p.2)
    else
      (true, p.2, p.2, st.2.2.2)
  else st

private lemma pass2Step_encodeLit (v : Nat) (l : literal) (st : P2State) (hi : st.inLit = false) :
    (encodeLit l).foldl (pass2Step v) st =
      let r := occStep v (st.hasF, st.first, st.prev, st.out) (l, st.pos + (l.2 + 2))
      { inLit := false, gotPol := false, pos := st.pos + (l.2 + 3), curV := 0,
        hasF := r.1, first := r.2.1, prev := r.2.2.1, out := r.2.2.2 } := by
  rcases l with ⟨pol, u⟩
  unfold encodeLit
  rw [List.foldl_cons, List.foldl_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have h1 : pass2Step v st 1 = { st with inLit := true, gotPol := false, pos := st.pos + 1, curV := 0 } := by
    simp [pass2Step, hi]
  rw [h1]
  have h2 : pass2Step v { st with inLit := true, gotPol := false, pos := st.pos + 1, curV := 0 }
      (if pol then 1 else 0) =
      { st with inLit := true, gotPol := true, pos := st.pos + 2, curV := 0 } := by
    simp only [pass2Step, ↓reduceIte, Bool.false_eq_true, P2State.mk.injEq, true_and, and_true]
  rw [h2, pass2Step_ones v u _ rfl rfl]
  simp only [Nat.zero_add, pass2Step, ↓reduceIte, Nat.zero_ne_one, occStep]
  have hp1 : st.pos + 2 + u = st.pos + (u + 2) := by omega
  have hp2 : st.pos + 2 + u + 1 = st.pos + (u + 3) := by omega
  rcases st with ⟨inL, gotP, pos, curV, hasF, first, prev, out⟩
  dsimp only at hi hp1 hp2 ⊢
  by_cases huv : u = v <;> cases hasF <;> simp_all [hp1, hp2]

private lemma pass2Step_encodeClause (v : Nat) (C : clause) (st : P2State)
    (hi : st.inLit = false) (hc : st.curV = 0) :
    let r := (litEnds C st.pos).foldl (occStep v) (st.hasF, st.first, st.prev, st.out)
    (encodeClause C).foldl (pass2Step v) st =
      { inLit := false, gotPol := false, pos := (renameClauseBody C st.pos).2 + 1, curV := 0,
        hasF := r.1, first := r.2.1, prev := r.2.2.1, out := r.2.2.2 } := by
  induction C generalizing st with
  | nil =>
      simp only [CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody, List.nil_append,
        List.foldl_cons, List.foldl_nil, litEnds, renameClauseBody]
      cases st
      simp only at hi hc
      subst hi; subst hc
      simp [pass2Step]
  | cons l rest ih =>
      rcases l with ⟨pol, u⟩
      rw [CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody_cons, List.append_assoc,
        List.foldl_append, pass2Step_encodeLit v (pol, u) st hi]
      set r1 := occStep v (st.hasF, st.first, st.prev, st.out) ((pol, u), st.pos + (u + 2))
      set st1 : P2State := {
        inLit := false, gotPol := false, pos := st.pos + (u + 3), curV := 0,
        hasF := r1.1, first := r1.2.1, prev := r1.2.2.1, out := r1.2.2.2 }
      have hrest := ih st1 rfl rfl
      rw [← CnfSerialize.encodeClause_eq, hrest]
      simp [litEnds, renameClauseBody, st1, r1]

private lemma pass2Step_encodeCnf (v : Nat) (N : cnf) (st : P2State)
    (hi : st.inLit = false) (hg : st.gotPol = false) (hc : st.curV = 0) :
    let r := (cnfLitEnds N st.pos).foldl (occStep v) (st.hasF, st.first, st.prev, st.out)
    (encodeCnf N).foldl (pass2Step v) st =
      { inLit := false, gotPol := false, pos := (renameCnf N st.pos).2, curV := 0,
        hasF := r.1, first := r.2.1, prev := r.2.2.1, out := r.2.2.2 } := by
  induction N generalizing st with
  | nil =>
      simp only [encodeCnf, List.foldl_nil, cnfLitEnds, renameCnf]
      cases st
      simp only at hi hg hc
      subst hi; subst hg; subst hc
      rfl
  | cons C rest ih =>
      rw [CnfSerialize.encodeCnf_cons, List.foldl_append, pass2Step_encodeClause v C st hi hc]
      set r1 := (litEnds C st.pos).foldl (occStep v) (st.hasF, st.first, st.prev, st.out)
      set st1 : P2State := {
        inLit := false, gotPol := false, pos := (renameClauseBody C st.pos).2 + 1, curV := 0,
        hasF := r1.1, first := r1.2.1, prev := r1.2.2.1, out := r1.2.2.2 }
      rw [ih st1 rfl rfl rfl]
      simp [cnfLitEnds, renameCnf, List.foldl_append, st1, r1]

private lemma encodeCnf_append (N1 N2 : cnf) :
    encodeCnf (N1 ++ N2) = encodeCnf N1 ++ encodeCnf N2 := by
  induction N1 with
  | nil => rfl
  | cons C rest ih =>
      simp only [List.cons_append, CnfSerialize.encodeCnf_cons, ih, List.append_assoc]

private lemma occStep_foldl_eq (v : Nat) (L : List (literal × Nat))
    (st : Bool × Nat × Nat × List Nat) :
    L.foldl (occStep v) st =
      ((L.filter (fun p => p.1.2 == v)).map Prod.snd).foldl
        (fun s idx =>
          if s.1 then (true, s.2.1, idx, s.2.2.2 ++ emitImplBits s.2.2.1 idx)
          else (true, idx, idx, s.2.2.2)) st := by
  induction L generalizing st with
  | nil => rfl
  | cons p tl ih =>
      simp only [List.foldl_cons, List.filter_cons]
      by_cases h : p.1.2 = v
      · have hb : (p.1.2 == v) = true := beq_iff_eq.mpr h
        simp only [hb, ↓reduceIte, List.map_cons, List.foldl_cons]
        dsimp only [occStep]
        rw [if_pos h]
        exact ih _
      · have hb : (p.1.2 == v) = false := beq_false_of_ne h
        simp only [hb, Bool.false_eq_true, ↓reduceIte, occStep, h]
        exact ih st

private lemma foldl_cycleGo (first prev : Nat) (L : List Nat) (out : List Nat) :
    let r := L.foldl (fun s idx =>
      if s.1 then (true, s.2.1, idx, s.2.2.2 ++ emitImplBits s.2.2.1 idx)
      else (true, idx, idx, s.2.2.2)) (true, first, prev, out)
    r.1 = true ∧ r.2.1 = first ∧
    r.2.2.2 ++ emitImplBits r.2.2.1 r.2.1 = out ++ encodeCnf (cycleGo first prev L) := by
  induction L generalizing prev out with
  | nil =>
      simp [cycleGo, emitImplBits, encodeCnf]
  | cons nxt tl ih =>
      simp only [List.foldl_cons, ↓reduceIte]
      have ⟨h1, h2, h3⟩ := ih nxt (out ++ emitImplBits prev nxt)
      refine ⟨h1, h2, ?_⟩
      rw [h3, cycleGo, CnfSerialize.encodeCnf_cons, emitImplBits, List.append_assoc]

private lemma pass2VarOut_encodeCnf (v : Nat) (N : cnf) (out : List Nat) :
    pass2VarOut v (encodeCnf N) out = out ++ encodeCnf (cycleForList (occsOfVar N v)) := by
  unfold pass2VarOut pass2Finish
  have hrun := pass2Step_encodeCnf v N (pass2Init out) rfl rfl rfl
  rw [hrun]
  dsimp only [pass2Init]
  have hocc := occStep_foldl_eq v (cnfLitEnds N 0) (false, 0, 0, out)
  simp only [hocc]
  have hf_eq : ∀ (L : List Nat),
      (let r := L.foldl (fun (s : Bool × Nat × Nat × List Nat) idx =>
          if s.1 then (true, s.2.1, idx, s.2.2.2 ++ emitImplBits s.2.2.1 idx)
          else (true, idx, idx, s.2.2.2)) (false, 0, 0, out)
       if r.1 then r.2.2.2 ++ emitImplBits r.2.2.1 r.2.1 else r.2.2.2) =
      out ++ encodeCnf (cycleForList L) := by
    intro L
    cases L with
    | nil => simp [cycleForList, encodeCnf]
    | cons k0 rest =>
        simp only [List.foldl_cons, Bool.false_eq_true, ↓reduceIte, cycleForList]
        have ⟨h1, h2, h3⟩ := foldl_cycleGo k0 k0 rest out
        rw [h1, if_pos rfl, h3]
  exact hf_eq (occsOfVar N v)

/-! ## Registers and `CookLevin.Lang.Cmd` implementation -/

def RVVAR  : Var := 11
def RCURV  : Var := 12
def RHASF  : Var := 13
def RFIRST : Var := 14
def RPREV  : Var := 15
def RMATCH : Var := 16

def setBotCnf : Cmd :=
  Cmd.op (.clear CNF_STREAM) ;; Cmd.op (.appendZero CNF_STREAM)

def phase1Pre : Cmd :=
  Cmd.op (.copy CNF_STREAM OUTPUT) ;;
  Cmd.op (.copy WCUR OUTPUT) ;;
  Cmd.op (.clear WSA) ;;
  Cmd.op (.clear WSB) ;;
  Cmd.op (.clear WTAL)

def phase1Post : Cmd :=
  Cmd.ifBit WSA setBotCnf
    (Cmd.ifBit WSB setBotCnf (Cmd.op (.clear WHD)))

def phase1Cmd : Cmd :=
  phase1Pre ;; Cmd.forBnd WIDX WCUR scanBody ;; phase1Post

def pass1Pre : Cmd :=
  Cmd.op (.copy WCUR CNF_STREAM) ;;
  Cmd.op (.clear OUTPUT) ;;
  Cmd.op (.clear WSA) ;;
  Cmd.op (.clear WSB)

def pass1Body : Cmd :=
  Cmd.op (.head WHD WCUR) ;;
  Cmd.op (.tail WCUR WCUR) ;;
  Cmd.ifBit WSA
    (Cmd.ifBit WSB
      (Cmd.ifBit WHD
        (Cmd.op (.clear WHD))
        (Cmd.op (.concat OUTPUT OUTPUT WIDX) ;;
         Cmd.op (.appendZero OUTPUT) ;;
         Cmd.op (.clear WSA) ;;
         Cmd.op (.clear WSB)))
      (Cmd.ifBit WHD
        (Cmd.op (.appendOne OUTPUT) ;; Cmd.op (.appendOne WSB))
        (Cmd.op (.appendZero OUTPUT) ;; Cmd.op (.appendOne WSB))))
    (Cmd.ifBit WHD
      (Cmd.op (.appendOne OUTPUT) ;; Cmd.op (.appendOne WSA) ;; Cmd.op (.clear WSB))
      (Cmd.op (.appendZero OUTPUT) ;; Cmd.op (.clear WSB)))

def pass1Cmd : Cmd :=
  pass1Pre ;; Cmd.forBnd WIDX WCUR pass1Body

def emitImplCmd (rPrev rNxt : Var) : Cmd :=
  Cmd.op (.appendOne OUTPUT) ;;
  Cmd.op (.appendZero OUTPUT) ;;
  Cmd.op (.concat OUTPUT OUTPUT rPrev) ;;
  Cmd.op (.appendZero OUTPUT) ;;
  Cmd.op (.appendOne OUTPUT) ;;
  Cmd.op (.appendOne OUTPUT) ;;
  Cmd.op (.concat OUTPUT OUTPUT rNxt) ;;
  Cmd.op (.appendZero OUTPUT) ;;
  Cmd.op (.appendZero OUTPUT)

def pass2InnerBody : Cmd :=
  Cmd.op (.head WHD WCUR) ;;
  Cmd.op (.tail WCUR WCUR) ;;
  Cmd.ifBit WSA
    (Cmd.ifBit WSB
      (Cmd.ifBit WHD
        (Cmd.op (.appendOne RCURV))
        (Cmd.op (.eqBit RMATCH RCURV RVVAR) ;;
         Cmd.ifBit RMATCH
           (Cmd.ifBit RHASF
             (emitImplCmd RPREV WIDX ;; Cmd.op (.copy RPREV WIDX))
             (Cmd.op (.appendOne RHASF) ;; Cmd.op (.copy RFIRST WIDX) ;; Cmd.op (.copy RPREV WIDX)))
           (Cmd.op (.clear WHD)) ;;
         Cmd.op (.clear WSA) ;;
         Cmd.op (.clear WSB) ;;
         Cmd.op (.clear RCURV)))
      (Cmd.op (.appendOne WSB)))
    (Cmd.ifBit WHD
      (Cmd.op (.appendOne WSA) ;; Cmd.op (.clear WSB) ;; Cmd.op (.clear RCURV))
      (Cmd.op (.clear WSB)))

def pass2OuterBody : Cmd :=
  Cmd.op (.copy WCUR CNF_STREAM) ;;
  Cmd.op (.clear WSA) ;;
  Cmd.op (.clear WSB) ;;
  Cmd.op (.clear RCURV) ;;
  Cmd.op (.clear RHASF) ;;
  Cmd.op (.clear RFIRST) ;;
  Cmd.op (.clear RPREV) ;;
  Cmd.forBnd WIDX WCUR pass2InnerBody ;;
  Cmd.ifBit RHASF (emitImplCmd RPREV RFIRST) (Cmd.op (.clear WHD))

def pass2Cmd : Cmd :=
  Cmd.forBnd RVVAR CNF_STREAM pass2OuterBody

def threeOccCmd : Cmd :=
  phase1Cmd ;; pass1Cmd ;; pass2Cmd

/-! ## Correctness of `threeOccCmd` -/

private lemma phase1_run (x : List Bool) :
    State.get (phase1Cmd.eval (certState x)) CNF_STREAM = encodeCnf (cnfOf x) := by
  have hin : State.get (certState x) OUTPUT = strBits x := rfl
  rw [phase1Cmd, Cmd.eval_seq, Cmd.eval_seq]
  set s0 := phase1Pre.eval (certState x) with hs0
  have hs0_CNF : State.get s0 CNF_STREAM = strBits x := by
    rw [hs0, phase1Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ WTAL _ CNF_STREAM (by decide),
      State.get_set_ne _ WSB _ CNF_STREAM (by decide),
      State.get_set_ne _ WSA _ CNF_STREAM (by decide),
      State.get_set_ne _ WCUR _ CNF_STREAM (by decide), State.get_set_eq]
    exact hin
  have hs0_C : State.get s0 WCUR = strBits x := by
    rw [hs0, phase1Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ WTAL _ WCUR (by decide),
      State.get_set_ne _ WSB _ WCUR (by decide),
      State.get_set_ne _ WSA _ WCUR (by decide), State.get_set_eq,
      State.get_set_ne _ CNF_STREAM _ OUTPUT (by decide)]
    exact hin
  have hs0_A : State.get s0 WSA = [] := by
    rw [hs0, phase1Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ WTAL _ WSA (by decide),
      State.get_set_ne _ WSB _ WSA (by decide), State.get_set_eq]
  have hs0_B : State.get s0 WSB = [] := by
    rw [hs0, phase1Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ WTAL _ WSB (by decide), State.get_set_eq]
  have hs0_T : State.get s0 WTAL = [] := by
    rw [hs0, phase1Pre]; simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq]
  obtain ⟨hA, hB, _⟩ := scanLoop_run (strBits x) s0 hs0_C hs0_A hs0_B hs0_T
  set u := (Cmd.forBnd WIDX WCUR scanBody).eval s0 with hu
  have hu_CNF : State.get u CNF_STREAM = strBits x := by
    rw [hu, Cmd.eval_get_of_not_writes _ _ CNF_STREAM (by decide)]
    exact hs0_CNF
  have hsetBot : ∀ st : State, State.get (setBotCnf.eval st) CNF_STREAM = encodeCnf botCnf := by
    intro st
    simp only [setBotCnf, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq, List.nil_append]
    rfl
  rw [phase1Post]
  cases ha : (scanRun (strBits x)).1
  · rw [ha] at hA
    rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hA]; simp [flagOf])]
    cases hb : (scanRun (strBits x)).2.1
    · rw [hb] at hB
      rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hB]; simp [flagOf])]
      simp only [Cmd.eval_op, Op.eval]
      rw [State.get_set_ne _ WHD _ CNF_STREAM (by decide), hu_CNF]
      have hwf : wfCnfB (strBits x) = true := by
        show (!(scanRun (strBits x)).1 && !(scanRun (strBits x)).2.1) = true
        rw [ha, hb]; rfl
      exact (encodeCnf_parseTotal _ (strBits_bit x) hwf).symm
    · rw [hb] at hB
      rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hB]; rfl), hsetBot]
      have hnw : wfCnfB (strBits x) = false := by
        show (!(scanRun (strBits x)).1 && !(scanRun (strBits x)).2.1) = false
        rw [ha, hb]; rfl
      have hbot : cnfOf x = botCnf := parseTotal_of_not_wf _ (by simpa using hnw)
      rw [hbot]
  · rw [ha] at hA
    rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hA]; rfl), hsetBot]
    have hnw : wfCnfB (strBits x) = false := by
      show (!(scanRun (strBits x)).1 && !(scanRun (strBits x)).2.1) = false
      rw [ha]; rfl
    have hbot : cnfOf x = botCnf := parseTotal_of_not_wf _ (by simpa using hnw)
    rw [hbot]

private lemma pass1Body_run (l : List Nat) (i : Nat) (hi : i < l.length) (s : State)
    (hI : State.get s WIDX = List.replicate i 1)
    (hC : State.get s WCUR = l.drop i)
    (hA : State.get s WSA = flagOf (pass1Take l i).1)
    (hB : State.get s WSB = flagOf (pass1Take l i).2.1)
    (hO : State.get s OUTPUT = (pass1Take l i).2.2.2) :
    let s' := pass1Body.eval s
    State.get s' WCUR = l.drop (i + 1) ∧
    State.get s' WSA = flagOf (pass1Take l (i + 1)).1 ∧
    State.get s' WSB = flagOf (pass1Take l (i + 1)).2.1 ∧
    State.get s' OUTPUT = (pass1Take l (i + 1)).2.2.2 := by
  have hdrop : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi
  have hpos : (pass1Take l i).2.2.1 = i := pass1Take_pos l i (by omega)
  rw [pass1Take_succ l i hi]
  dsimp only [pass1Body]
  rw [Cmd.eval_seq, Cmd.eval_seq]
  set s1 := (Cmd.op (.head WHD WCUR)).eval s
  set s2 := (Cmd.op (.tail WCUR WCUR)).eval s1
  have hs2_H : State.get s2 WHD = [l[i]] := by
    simp only [s2, s1, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ WCUR _ WHD (by decide), State.get_set_eq, hC, hdrop]
  have hs2_C : State.get s2 WCUR = l.drop (i + 1) := by
    simp only [s2, s1, Cmd.eval_op, Op.eval, State.get_set_eq]
    rw [State.get_set_ne _ WHD _ WCUR (by decide), hC, hdrop]; rfl
  have hs2_other : ∀ r, r ≠ WCUR → r ≠ WHD → State.get s2 r = State.get s r := fun r h1 h2 => by
    simp only [s2, s1, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ WCUR _ r h1, State.get_set_ne _ WHD _ r h2]
  have hs2_I : State.get s2 WIDX = List.replicate i 1 := by rw [hs2_other WIDX (by decide) (by decide), hI]
  have hs2_A : State.get s2 WSA = flagOf (pass1Take l i).1 := by rw [hs2_other WSA (by decide) (by decide), hA]
  have hs2_B : State.get s2 WSB = flagOf (pass1Take l i).2.1 := by rw [hs2_other WSB (by decide) (by decide), hB]
  have hs2_O : State.get s2 OUTPUT = (pass1Take l i).2.2.2 := by rw [hs2_other OUTPUT (by decide) (by decide), hO]
  rcases htk : pass1Take l i with ⟨a, b, p, out⟩
  rw [htk] at hs2_A hs2_B hs2_O hpos
  dsimp only at hs2_A hs2_B hs2_O hpos
  subst p
  cases a
  · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hs2_A]; simp [flagOf])]
    by_cases h1 : l[i] = 1
    · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hs2_H, h1])]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [pass1Step, h1, ↓reduceIte, flagOf, Cmd.eval_seq, Cmd.eval_op, Op.eval]
      · rw [State.get_set_ne _ WSB _ WCUR (by decide), State.get_set_ne _ WSA _ WCUR (by decide),
          State.get_set_ne _ OUTPUT _ WCUR (by decide), hs2_C]
      · rw [State.get_set_ne _ WSB _ WSA (by decide), State.get_set_eq,
          State.get_set_ne _ OUTPUT _ WSA (by decide), hs2_A]; rfl
      · rw [State.get_set_eq]; rfl
      · rw [State.get_set_ne _ WSB _ OUTPUT (by decide), State.get_set_ne _ WSA _ OUTPUT (by decide),
          State.get_set_eq, hs2_O]
    · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hs2_H]; simp [h1])]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [pass1Step, h1, ↓reduceIte, flagOf, Cmd.eval_seq, Cmd.eval_op, Op.eval]
      · rw [State.get_set_ne _ WSB _ WCUR (by decide), State.get_set_ne _ OUTPUT _ WCUR (by decide), hs2_C]
      · rw [State.get_set_ne _ WSB _ WSA (by decide), State.get_set_ne _ OUTPUT _ WSA (by decide), hs2_A]; rfl
      · rw [State.get_set_eq]; rfl
      · rw [State.get_set_ne _ WSB _ OUTPUT (by decide), State.get_set_eq, hs2_O]
  · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hs2_A]; rfl)]
    cases b
    · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hs2_B]; simp [flagOf])]
      by_cases h1 : l[i] = 1
      · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hs2_H, h1])]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp only [pass1Step, h1, ↓reduceIte, flagOf, Cmd.eval_seq, Cmd.eval_op, Op.eval]
        · rw [State.get_set_ne _ WSB _ WCUR (by decide), State.get_set_ne _ OUTPUT _ WCUR (by decide), hs2_C]
        · rw [State.get_set_ne _ WSB _ WSA (by decide), State.get_set_ne _ OUTPUT _ WSA (by decide), hs2_A]; rfl
        · rw [State.get_set_eq, State.get_set_ne _ OUTPUT _ WSB (by decide), hs2_B]; rfl
        · rw [State.get_set_ne _ WSB _ OUTPUT (by decide), State.get_set_eq, hs2_O]
      · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hs2_H]; simp [h1])]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp only [pass1Step, h1, ↓reduceIte, flagOf, Cmd.eval_seq, Cmd.eval_op, Op.eval]
        · rw [State.get_set_ne _ WSB _ WCUR (by decide), State.get_set_ne _ OUTPUT _ WCUR (by decide), hs2_C]
        · rw [State.get_set_ne _ WSB _ WSA (by decide), State.get_set_ne _ OUTPUT _ WSA (by decide), hs2_A]; rfl
        · rw [State.get_set_eq, State.get_set_ne _ OUTPUT _ WSB (by decide), hs2_B]; rfl
        · rw [State.get_set_ne _ WSB _ OUTPUT (by decide), State.get_set_eq, hs2_O]
    · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hs2_B]; rfl)]
      by_cases h1 : l[i] = 1
      · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hs2_H, h1])]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp only [pass1Step, h1, ↓reduceIte, flagOf, Cmd.eval_op, Op.eval]
        · rw [State.get_set_ne _ WHD _ WCUR (by decide), hs2_C]
        · rw [State.get_set_ne _ WHD _ WSA (by decide), hs2_A]; rfl
        · rw [State.get_set_ne _ WHD _ WSB (by decide), hs2_B]; rfl
        · rw [State.get_set_ne _ WHD _ OUTPUT (by decide), hs2_O]
      · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hs2_H]; simp [h1])]
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp only [pass1Step, h1, ↓reduceIte, flagOf, Cmd.eval_seq, Cmd.eval_op, Op.eval]
        · rw [State.get_set_ne _ WSB _ WCUR (by decide), State.get_set_ne _ WSA _ WCUR (by decide),
            State.get_set_ne _ OUTPUT _ WCUR (by decide), State.get_set_ne _ OUTPUT _ WCUR (by decide), hs2_C]
        · rw [State.get_set_ne _ WSB _ WSA (by decide), State.get_set_eq]; rfl
        · rw [State.get_set_eq]; rfl
        · rw [State.get_set_ne _ WSB _ OUTPUT (by decide), State.get_set_ne _ WSA _ OUTPUT (by decide),
            State.get_set_eq, State.get_set_eq, hs2_O, hs2_I]

private lemma pass1Loop_run (l : List Nat) (s0 : State)
    (hC : State.get s0 WCUR = l) (hA : State.get s0 WSA = [])
    (hB : State.get s0 WSB = []) (hO : State.get s0 OUTPUT = []) :
    State.get ((Cmd.forBnd WIDX WCUR pass1Body).eval s0) OUTPUT = (pass1Run l).2.2.2 := by
  have hlen : (State.get s0 WCUR).length = l.length := by rw [hC]
  rw [Cmd.eval_forBnd, hlen]
  have key := Cmd.foldlState_range_induct pass1Body WIDX l.length s0
    (fun i st =>
      State.get st WCUR = l.drop i ∧
      State.get st WSA = flagOf (pass1Take l i).1 ∧
      State.get st WSB = flagOf (pass1Take l i).2.1 ∧
      State.get st OUTPUT = (pass1Take l i).2.2.2)
    ⟨by simpa using hC, hA, hB, hO⟩
    (by
      rintro i st hi ⟨hc, ha, hb, ho⟩
      refine pass1Body_run l i hi _ (by rw [State.get_set_eq]) ?_ ?_ ?_ ?_
      · rw [State.get_set_ne _ WIDX _ WCUR (by decide)]; exact hc
      · rw [State.get_set_ne _ WIDX _ WSA (by decide)]; exact ha
      · rw [State.get_set_ne _ WIDX _ WSB (by decide)]; exact hb
      · rw [State.get_set_ne _ WIDX _ OUTPUT (by decide)]; exact ho)
  simpa [pass1Take, pass1Run] using key.2.2.2

private lemma emitImplCmd_run (rPrev rNxt : Var) (hP : rPrev ≠ OUTPUT) (hN : rNxt ≠ OUTPUT)
    (s : State) (p n : Nat)
    (hp : State.get s rPrev = List.replicate p 1)
    (hn : State.get s rNxt = List.replicate n 1) :
    State.get ((emitImplCmd rPrev rNxt).eval s) OUTPUT = State.get s OUTPUT ++ emitImplBits p n ∧
    (∀ r, r ≠ OUTPUT → State.get ((emitImplCmd rPrev rNxt).eval s) r = State.get s r) := by
  have hne : ∀ r, r ≠ OUTPUT → State.get ((emitImplCmd rPrev rNxt).eval s) r = State.get s r := by
    intro r hr
    simp only [emitImplCmd, Cmd.eval_seq, Cmd.eval_op, Op.eval]
    repeat rw [State.get_set_ne _ OUTPUT _ r hr]
  refine ⟨?_, hne⟩
  simp only [emitImplCmd, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq]
  repeat rw [State.get_set_ne _ OUTPUT _ rPrev hP]
  repeat rw [State.get_set_ne _ OUTPUT _ rNxt hN]
  rw [hp, hn]
  simp [emitImplBits, encodeClause, CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody,
    encodeLit, List.append_assoc]

set_option maxHeartbeats 800000 in
private lemma pass2InnerBody_run (v : Nat) (l out0 : List Nat) (i : Nat) (hi : i < l.length) (s : State)
    (hI : State.get s WIDX = List.replicate i 1)
    (hV : State.get s RVVAR = List.replicate v 1)
    (hC : State.get s WCUR = l.drop i)
    (hA : State.get s WSA = flagOf (pass2Take v l out0 i).inLit)
    (hB : State.get s WSB = flagOf (pass2Take v l out0 i).gotPol)
    (hCurV : State.get s RCURV = List.replicate (pass2Take v l out0 i).curV 1)
    (hHasF : State.get s RHASF = flagOf (pass2Take v l out0 i).hasF)
    (hFirst : State.get s RFIRST = List.replicate (pass2Take v l out0 i).first 1)
    (hPrev : State.get s RPREV = List.replicate (pass2Take v l out0 i).prev 1)
    (hO : State.get s OUTPUT = (pass2Take v l out0 i).out) :
    let s' := pass2InnerBody.eval s
    let st' := pass2Take v l out0 (i + 1)
    State.get s' RVVAR = List.replicate v 1 ∧
    State.get s' WCUR = l.drop (i + 1) ∧
    State.get s' WSA = flagOf st'.inLit ∧
    State.get s' WSB = flagOf st'.gotPol ∧
    State.get s' RCURV = List.replicate st'.curV 1 ∧
    State.get s' RHASF = flagOf st'.hasF ∧
    State.get s' RFIRST = List.replicate st'.first 1 ∧
    State.get s' RPREV = List.replicate st'.prev 1 ∧
    State.get s' OUTPUT = st'.out := by
  have hdrop : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi
  have hpos : (pass2Take v l out0 i).pos = i := pass2Take_pos v l out0 i (by omega)
  dsimp only
  rw [pass2Take_succ v l out0 i hi]
  dsimp only [pass2InnerBody]
  rw [Cmd.eval_seq, Cmd.eval_seq]
  set s1 := (Cmd.op (.head WHD WCUR)).eval s
  set s2 := (Cmd.op (.tail WCUR WCUR)).eval s1
  have hs2_H : State.get s2 WHD = [l[i]] := by
    simp only [s2, s1, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ WCUR _ WHD (by decide), State.get_set_eq, hC, hdrop]
  have hs2_C : State.get s2 WCUR = l.drop (i + 1) := by
    simp only [s2, s1, Cmd.eval_op, Op.eval, State.get_set_eq]
    rw [State.get_set_ne _ WHD _ WCUR (by decide), hC, hdrop]; rfl
  have hs2_other : ∀ r, r ≠ WCUR → r ≠ WHD → State.get s2 r = State.get s r := fun r hr1 hr2 => by
    simp only [s2, s1, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ WCUR _ r hr1, State.get_set_ne _ WHD _ r hr2]
  have hs2_I : State.get s2 WIDX = List.replicate i 1 := by rw [hs2_other WIDX (by decide) (by decide), hI]
  have hs2_V : State.get s2 RVVAR = List.replicate v 1 := by rw [hs2_other RVVAR (by decide) (by decide), hV]
  have hs2_A : State.get s2 WSA = flagOf (pass2Take v l out0 i).inLit := by rw [hs2_other WSA (by decide) (by decide), hA]
  have hs2_B : State.get s2 WSB = flagOf (pass2Take v l out0 i).gotPol := by rw [hs2_other WSB (by decide) (by decide), hB]
  have hs2_CurV : State.get s2 RCURV = List.replicate (pass2Take v l out0 i).curV 1 := by rw [hs2_other RCURV (by decide) (by decide), hCurV]
  have hs2_HasF : State.get s2 RHASF = flagOf (pass2Take v l out0 i).hasF := by rw [hs2_other RHASF (by decide) (by decide), hHasF]
  have hs2_First : State.get s2 RFIRST = List.replicate (pass2Take v l out0 i).first 1 := by rw [hs2_other RFIRST (by decide) (by decide), hFirst]
  have hs2_Prev : State.get s2 RPREV = List.replicate (pass2Take v l out0 i).prev 1 := by rw [hs2_other RPREV (by decide) (by decide), hPrev]
  have hs2_O : State.get s2 OUTPUT = (pass2Take v l out0 i).out := by rw [hs2_other OUTPUT (by decide) (by decide), hO]
  rcases htk : pass2Take v l out0 i with ⟨inL, gotP, pos, curV, hasF, first, prev, out⟩
  rw [htk] at hs2_A hs2_B hs2_CurV hs2_HasF hs2_First hs2_Prev hs2_O hpos
  dsimp only at hs2_A hs2_B hs2_CurV hs2_HasF hs2_First hs2_Prev hs2_O hpos
  subst pos
  cases inL
  · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hs2_A]; simp [flagOf])]
    by_cases h1 : l[i] = 1
    · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hs2_H, h1])]
      simp only [pass2Step, h1, ↓reduceIte, flagOf, Cmd.eval_seq, Cmd.eval_op, Op.eval]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.get_set_ne _ RCURV _ RVVAR (by decide), State.get_set_ne _ WSB _ RVVAR (by decide),
          State.get_set_ne _ WSA _ RVVAR (by decide), hs2_V]
      · rw [State.get_set_ne _ RCURV _ WCUR (by decide), State.get_set_ne _ WSB _ WCUR (by decide),
          State.get_set_ne _ WSA _ WCUR (by decide), hs2_C]
      · rw [State.get_set_ne _ RCURV _ WSA (by decide), State.get_set_ne _ WSB _ WSA (by decide),
          State.get_set_eq, hs2_A]; rfl
      · rw [State.get_set_ne _ RCURV _ WSB (by decide), State.get_set_eq]; rfl
      · rw [State.get_set_eq]; rfl
      · rw [State.get_set_ne _ RCURV _ RHASF (by decide), State.get_set_ne _ WSB _ RHASF (by decide),
          State.get_set_ne _ WSA _ RHASF (by decide), hs2_HasF]; rfl
      · rw [State.get_set_ne _ RCURV _ RFIRST (by decide), State.get_set_ne _ WSB _ RFIRST (by decide),
          State.get_set_ne _ WSA _ RFIRST (by decide), hs2_First]; rfl
      · rw [State.get_set_ne _ RCURV _ RPREV (by decide), State.get_set_ne _ WSB _ RPREV (by decide),
          State.get_set_ne _ WSA _ RPREV (by decide), hs2_Prev]; rfl
      · rw [State.get_set_ne _ RCURV _ OUTPUT (by decide), State.get_set_ne _ WSB _ OUTPUT (by decide),
          State.get_set_ne _ WSA _ OUTPUT (by decide), hs2_O]; rfl
    · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hs2_H]; simp [h1])]
      simp only [pass2Step, h1, ↓reduceIte, flagOf, Cmd.eval_op, Op.eval]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.get_set_ne _ WSB _ RVVAR (by decide), hs2_V]
      · rw [State.get_set_ne _ WSB _ WCUR (by decide), hs2_C]
      · rw [State.get_set_ne _ WSB _ WSA (by decide), hs2_A]; rfl
      · rw [State.get_set_eq]; rfl
      · rw [State.get_set_ne _ WSB _ RCURV (by decide), hs2_CurV]; rfl
      · rw [State.get_set_ne _ WSB _ RHASF (by decide), hs2_HasF]; rfl
      · rw [State.get_set_ne _ WSB _ RFIRST (by decide), hs2_First]; rfl
      · rw [State.get_set_ne _ WSB _ RPREV (by decide), hs2_Prev]; rfl
      · rw [State.get_set_ne _ WSB _ OUTPUT (by decide), hs2_O]; rfl
  · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hs2_A]; rfl)]
    cases gotP
    · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hs2_B]; simp [flagOf])]
      simp only [pass2Step, ↓reduceIte, flagOf, Cmd.eval_op, Op.eval]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.get_set_ne _ WSB _ RVVAR (by decide), hs2_V]
      · rw [State.get_set_ne _ WSB _ WCUR (by decide), hs2_C]
      · rw [State.get_set_ne _ WSB _ WSA (by decide), hs2_A]; rfl
      · rw [State.get_set_eq, hs2_B]; rfl
      · rw [State.get_set_ne _ WSB _ RCURV (by decide), hs2_CurV]; rfl
      · rw [State.get_set_ne _ WSB _ RHASF (by decide), hs2_HasF]; rfl
      · rw [State.get_set_ne _ WSB _ RFIRST (by decide), hs2_First]; rfl
      · rw [State.get_set_ne _ WSB _ RPREV (by decide), hs2_Prev]; rfl
      · rw [State.get_set_ne _ WSB _ OUTPUT (by decide), hs2_O]; rfl
    · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hs2_B]; rfl)]
      by_cases h1 : l[i] = 1
      · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hs2_H, h1])]
        simp only [pass2Step, h1, ↓reduceIte, flagOf, Cmd.eval_op, Op.eval]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.get_set_ne _ RCURV _ RVVAR (by decide), hs2_V]
        · rw [State.get_set_ne _ RCURV _ WCUR (by decide), hs2_C]
        · rw [State.get_set_ne _ RCURV _ WSA (by decide), hs2_A]; rfl
        · rw [State.get_set_ne _ RCURV _ WSB (by decide), hs2_B]; rfl
        · rw [State.get_set_eq, hs2_CurV, List.replicate_succ']
        · rw [State.get_set_ne _ RCURV _ RHASF (by decide), hs2_HasF]; rfl
        · rw [State.get_set_ne _ RCURV _ RFIRST (by decide), hs2_First]
        · rw [State.get_set_ne _ RCURV _ RPREV (by decide), hs2_Prev]
        · rw [State.get_set_ne _ RCURV _ OUTPUT (by decide), hs2_O]
      · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hs2_H]; simp [h1])]
        simp only [pass2Step, ↓reduceIte, h1]
        rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
        set s3 := (Cmd.op (.eqBit RMATCH RCURV RVVAR)).eval s2
        have hs3_M : State.get s3 RMATCH = if curV = v then [1] else [0] := by
          simp only [s3, Cmd.eval_op, Op.eval, State.get_set_eq, hs2_CurV, hs2_V]
          by_cases hcv : curV = v
          · simp [hcv]
          · have hne : List.replicate curV 1 ≠ List.replicate v 1 := fun heq =>
              hcv (by simpa using congrArg List.length heq)
            simp [hcv, hne]
        have hs3_other : ∀ r, r ≠ RMATCH → State.get s3 r = State.get s2 r := fun r hr => by
          simp only [s3, Cmd.eval_op, Op.eval]
          rw [State.get_set_ne _ RMATCH _ r hr]
        -- Helper to peel off the final 3 clears (WSA, WSB, RCURV)
        have peel3 : ∀ (st : State) (hf : Bool) (fi pr : Nat) (ou : List Nat),
            State.get st RVVAR = List.replicate v 1 →
            State.get st WCUR = l.drop (i + 1) →
            State.get st RHASF = flagOf hf →
            State.get st RFIRST = List.replicate fi 1 →
            State.get st RPREV = List.replicate pr 1 →
            State.get st OUTPUT = ou →
            let stf := (Cmd.op (.clear RCURV)).eval ((Cmd.op (.clear WSB)).eval ((Cmd.op (.clear WSA)).eval st))
            State.get stf RVVAR = List.replicate v 1 ∧
            State.get stf WCUR = l.drop (i + 1) ∧
            State.get stf WSA = flagOf false ∧
            State.get stf WSB = flagOf false ∧
            State.get stf RCURV = List.replicate 0 1 ∧
            State.get stf RHASF = flagOf hf ∧
            State.get stf RFIRST = List.replicate fi 1 ∧
            State.get stf RPREV = List.replicate pr 1 ∧
            State.get stf OUTPUT = ou := by
          intro st hf fi pr ou h1' h2' h3' h4' h5' h6'
          dsimp only [Cmd.eval_op, Op.eval, flagOf]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [State.get_set_ne _ RCURV _ RVVAR (by decide), State.get_set_ne _ WSB _ RVVAR (by decide),
              State.get_set_ne _ WSA _ RVVAR (by decide), h1']
          · rw [State.get_set_ne _ RCURV _ WCUR (by decide), State.get_set_ne _ WSB _ WCUR (by decide),
              State.get_set_ne _ WSA _ WCUR (by decide), h2']
          · rw [State.get_set_ne _ RCURV _ WSA (by decide), State.get_set_ne _ WSB _ WSA (by decide),
              State.get_set_eq]; rfl
          · rw [State.get_set_ne _ RCURV _ WSB (by decide), State.get_set_eq]; rfl
          · rw [State.get_set_eq]; rfl
          · rw [State.get_set_ne _ RCURV _ RHASF (by decide), State.get_set_ne _ WSB _ RHASF (by decide),
              State.get_set_ne _ WSA _ RHASF (by decide), h3']; rfl
          · rw [State.get_set_ne _ RCURV _ RFIRST (by decide), State.get_set_ne _ WSB _ RFIRST (by decide),
              State.get_set_ne _ WSA _ RFIRST (by decide), h4']
          · rw [State.get_set_ne _ RCURV _ RPREV (by decide), State.get_set_ne _ WSB _ RPREV (by decide),
              State.get_set_ne _ WSA _ RPREV (by decide), h5']
          · rw [State.get_set_ne _ RCURV _ OUTPUT (by decide), State.get_set_ne _ WSB _ OUTPUT (by decide),
              State.get_set_ne _ WSA _ OUTPUT (by decide), h6']
        by_cases hcv : curV = v
        · rw [if_pos hcv, Cmd.eval_ifBit_true _ _ _ _ (by rw [hs3_M, if_pos hcv])]
          cases hasF
          · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hs3_other RHASF (by decide), hs2_HasF]; simp [flagOf])]
            exact peel3 _ true i i out
              (by simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
                  rw [State.get_set_ne _ RPREV _ RVVAR (by decide), State.get_set_ne _ RFIRST _ RVVAR (by decide),
                    State.get_set_ne _ RHASF _ RVVAR (by decide), hs3_other RVVAR (by decide), hs2_V])
              (by simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
                  rw [State.get_set_ne _ RPREV _ WCUR (by decide), State.get_set_ne _ RFIRST _ WCUR (by decide),
                    State.get_set_ne _ RHASF _ WCUR (by decide), hs3_other WCUR (by decide), hs2_C])
              (by simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
                  rw [State.get_set_ne _ RPREV _ RHASF (by decide), State.get_set_ne _ RFIRST _ RHASF (by decide),
                    State.get_set_eq, hs3_other RHASF (by decide), hs2_HasF]; rfl)
              (by simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
                  rw [State.get_set_ne _ RPREV _ RFIRST (by decide), State.get_set_eq,
                    State.get_set_ne _ RHASF _ WIDX (by decide), hs3_other WIDX (by decide), hs2_I])
              (by simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq]
                  rw [State.get_set_ne _ RFIRST _ WIDX (by decide), State.get_set_ne _ RHASF _ WIDX (by decide),
                    hs3_other WIDX (by decide), hs2_I])
              (by simp only [Cmd.eval_seq, Cmd.eval_op, Op.eval]
                  rw [State.get_set_ne _ RPREV _ OUTPUT (by decide), State.get_set_ne _ RFIRST _ OUTPUT (by decide),
                    State.get_set_ne _ RHASF _ OUTPUT (by decide), hs3_other OUTPUT (by decide), hs2_O])
          · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hs3_other RHASF (by decide), hs2_HasF]; rfl)]
            rw [Cmd.eval_seq]
            have ⟨hemO, hemRest⟩ := emitImplCmd_run RPREV WIDX (by decide) (by decide) s3 prev i
              (by rw [hs3_other RPREV (by decide), hs2_Prev])
              (by rw [hs3_other WIDX (by decide), hs2_I])
            exact peel3 _ true first i (out ++ emitImplBits prev i)
              (by simp only [Cmd.eval_op, Op.eval]
                  rw [State.get_set_ne _ RPREV _ RVVAR (by decide), hemRest RVVAR (by decide),
                    hs3_other RVVAR (by decide), hs2_V])
              (by simp only [Cmd.eval_op, Op.eval]
                  rw [State.get_set_ne _ RPREV _ WCUR (by decide), hemRest WCUR (by decide),
                    hs3_other WCUR (by decide), hs2_C])
              (by simp only [Cmd.eval_op, Op.eval]
                  rw [State.get_set_ne _ RPREV _ RHASF (by decide), hemRest RHASF (by decide),
                    hs3_other RHASF (by decide), hs2_HasF])
              (by simp only [Cmd.eval_op, Op.eval]
                  rw [State.get_set_ne _ RPREV _ RFIRST (by decide), hemRest RFIRST (by decide),
                    hs3_other RFIRST (by decide), hs2_First])
              (by simp only [Cmd.eval_op, Op.eval, State.get_set_eq]
                  rw [hemRest WIDX (by decide), hs3_other WIDX (by decide), hs2_I])
              (by simp only [Cmd.eval_op, Op.eval]
                  rw [State.get_set_ne _ RPREV _ OUTPUT (by decide), hemO, hs3_other OUTPUT (by decide), hs2_O])
        · rw [if_neg hcv, Cmd.eval_ifBit_false _ _ _ _ (by rw [hs3_M, if_neg hcv]; simp)]
          exact peel3 _ hasF first prev out
            (by simp only [Cmd.eval_op, Op.eval]
                rw [State.get_set_ne _ WHD _ RVVAR (by decide), hs3_other RVVAR (by decide), hs2_V])
            (by simp only [Cmd.eval_op, Op.eval]
                rw [State.get_set_ne _ WHD _ WCUR (by decide), hs3_other WCUR (by decide), hs2_C])
            (by simp only [Cmd.eval_op, Op.eval]
                rw [State.get_set_ne _ WHD _ RHASF (by decide), hs3_other RHASF (by decide), hs2_HasF])
            (by simp only [Cmd.eval_op, Op.eval]
                rw [State.get_set_ne _ WHD _ RFIRST (by decide), hs3_other RFIRST (by decide), hs2_First])
            (by simp only [Cmd.eval_op, Op.eval]
                rw [State.get_set_ne _ WHD _ RPREV (by decide), hs3_other RPREV (by decide), hs2_Prev])
            (by simp only [Cmd.eval_op, Op.eval]
                rw [State.get_set_ne _ WHD _ OUTPUT (by decide), hs3_other OUTPUT (by decide), hs2_O])

private lemma pass2OuterBody_run (v : Nat) (l out0 : List Nat) (s : State)
    (hCNF : State.get s CNF_STREAM = l)
    (hV : State.get s RVVAR = List.replicate v 1)
    (hO : State.get s OUTPUT = out0) :
    State.get (pass2OuterBody.eval s) CNF_STREAM = l ∧
    State.get (pass2OuterBody.eval s) OUTPUT = pass2VarOut v l out0 := by
  have hcnf_pres : State.get (pass2OuterBody.eval s) CNF_STREAM = l := by
    rw [Cmd.eval_get_of_not_writes _ _ CNF_STREAM (by decide)]
    exact hCNF
  refine ⟨hcnf_pres, ?_⟩
  dsimp only [pass2OuterBody]
  repeat rw [Cmd.eval_seq]
  set s0 := (Cmd.op (.clear RPREV)).eval ((Cmd.op (.clear RFIRST)).eval ((Cmd.op (.clear RHASF)).eval
    ((Cmd.op (.clear RCURV)).eval ((Cmd.op (.clear WSB)).eval ((Cmd.op (.clear WSA)).eval
      ((Cmd.op (.copy WCUR CNF_STREAM)).eval s))))))
  have hs0_V : State.get s0 RVVAR = List.replicate v 1 := by
    simp only [s0, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ RPREV _ RVVAR (by decide), State.get_set_ne _ RFIRST _ RVVAR (by decide),
      State.get_set_ne _ RHASF _ RVVAR (by decide), State.get_set_ne _ RCURV _ RVVAR (by decide),
      State.get_set_ne _ WSB _ RVVAR (by decide), State.get_set_ne _ WSA _ RVVAR (by decide),
      State.get_set_ne _ WCUR _ RVVAR (by decide), hV]
  have hs0_C : State.get s0 WCUR = l := by
    simp only [s0, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ RPREV _ WCUR (by decide), State.get_set_ne _ RFIRST _ WCUR (by decide),
      State.get_set_ne _ RHASF _ WCUR (by decide), State.get_set_ne _ RCURV _ WCUR (by decide),
      State.get_set_ne _ WSB _ WCUR (by decide), State.get_set_ne _ WSA _ WCUR (by decide),
      State.get_set_eq, hCNF]
  have hs0_A : State.get s0 WSA = [] := by
    simp only [s0, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ RPREV _ WSA (by decide), State.get_set_ne _ RFIRST _ WSA (by decide),
      State.get_set_ne _ RHASF _ WSA (by decide), State.get_set_ne _ RCURV _ WSA (by decide),
      State.get_set_ne _ WSB _ WSA (by decide), State.get_set_eq]
  have hs0_B : State.get s0 WSB = [] := by
    simp only [s0, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ RPREV _ WSB (by decide), State.get_set_ne _ RFIRST _ WSB (by decide),
      State.get_set_ne _ RHASF _ WSB (by decide), State.get_set_ne _ RCURV _ WSB (by decide),
      State.get_set_eq]
  have hs0_CurV : State.get s0 RCURV = [] := by
    simp only [s0, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ RPREV _ RCURV (by decide), State.get_set_ne _ RFIRST _ RCURV (by decide),
      State.get_set_ne _ RHASF _ RCURV (by decide), State.get_set_eq]
  have hs0_HasF : State.get s0 RHASF = [] := by
    simp only [s0, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ RPREV _ RHASF (by decide), State.get_set_ne _ RFIRST _ RHASF (by decide),
      State.get_set_eq]
  have hs0_First : State.get s0 RFIRST = [] := by
    simp only [s0, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ RPREV _ RFIRST (by decide), State.get_set_eq]
  have hs0_Prev : State.get s0 RPREV = [] := by
    simp only [s0, Cmd.eval_op, Op.eval, State.get_set_eq]
  have hs0_O : State.get s0 OUTPUT = out0 := by
    simp only [s0, Cmd.eval_op, Op.eval]
    rw [State.get_set_ne _ RPREV _ OUTPUT (by decide), State.get_set_ne _ RFIRST _ OUTPUT (by decide),
      State.get_set_ne _ RHASF _ OUTPUT (by decide), State.get_set_ne _ RCURV _ OUTPUT (by decide),
      State.get_set_ne _ WSB _ OUTPUT (by decide), State.get_set_ne _ WSA _ OUTPUT (by decide),
      State.get_set_ne _ WCUR _ OUTPUT (by decide), hO]
  have hlen : (State.get s0 WCUR).length = l.length := by rw [hs0_C]
  rw [Cmd.eval_forBnd, hlen]
  have hfin := Cmd.foldlState_range_induct pass2InnerBody WIDX l.length s0
    (fun k sk =>
      let tk := pass2Take v l out0 k
      State.get sk RVVAR = List.replicate v 1 ∧
      State.get sk WCUR = l.drop k ∧
      State.get sk WSA = flagOf tk.inLit ∧
      State.get sk WSB = flagOf tk.gotPol ∧
      State.get sk RCURV = List.replicate tk.curV 1 ∧
      State.get sk RHASF = flagOf tk.hasF ∧
      State.get sk RFIRST = List.replicate tk.first 1 ∧
      State.get sk RPREV = List.replicate tk.prev 1 ∧
      State.get sk OUTPUT = tk.out)
    ⟨hs0_V, by simpa using hs0_C, hs0_A, hs0_B, hs0_CurV, hs0_HasF, hs0_First, hs0_Prev, hs0_O⟩
    (by
      rintro m sk hm ⟨hv, hc, ha, hb, hcv, hhf, hfi, hpr, ho⟩
      exact pass2InnerBody_run v l out0 m hm _ (by rw [State.get_set_eq])
        (by rw [State.get_set_ne _ WIDX _ RVVAR (by decide)]; exact hv)
        (by rw [State.get_set_ne _ WIDX _ WCUR (by decide)]; exact hc)
        (by rw [State.get_set_ne _ WIDX _ WSA (by decide)]; exact ha)
        (by rw [State.get_set_ne _ WIDX _ WSB (by decide)]; exact hb)
        (by rw [State.get_set_ne _ WIDX _ RCURV (by decide)]; exact hcv)
        (by rw [State.get_set_ne _ WIDX _ RHASF (by decide)]; exact hhf)
        (by rw [State.get_set_ne _ WIDX _ RFIRST (by decide)]; exact hfi)
        (by rw [State.get_set_ne _ WIDX _ RPREV (by decide)]; exact hpr)
        (by rw [State.get_set_ne _ WIDX _ OUTPUT (by decide)]; exact ho))
  set sLoop := Cmd.foldlState pass2InnerBody WIDX (List.range l.length) s0
  set stFin := l.foldl (pass2Step v) (pass2Init out0)
  have htk_eq : pass2Take v l out0 l.length = stFin := by simp [pass2Take, stFin]
  rw [htk_eq] at hfin
  dsimp only [sLoop] at hfin ⊢
  unfold pass2VarOut pass2Finish
  cases hf : stFin.hasF
  · rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hfin.2.2.2.2.2.1, hf]; simp [flagOf])]
    simp only [Cmd.eval_op, Op.eval, Bool.false_eq_true, ↓reduceIte]
    rw [State.get_set_ne _ WHD _ OUTPUT (by decide), hfin.2.2.2.2.2.2.2.2]
  · rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hfin.2.2.2.2.2.1, hf]; rfl)]
    simp only [↓reduceIte]
    have ⟨hemO, _⟩ := emitImplCmd_run RPREV RFIRST (by decide) (by decide) sLoop stFin.prev stFin.first
      hfin.2.2.2.2.2.2.2.1 hfin.2.2.2.2.2.2.1
    rw [hemO, hfin.2.2.2.2.2.2.2.2]

set_option maxHeartbeats 800000 in
private lemma pass2Loop_run (N : cnf) (s0 : State)
    (hCNF : State.get s0 CNF_STREAM = encodeCnf N)
    (hO : State.get s0 OUTPUT = encodeCnf (renameCnf N 0).1) :
    State.get (pass2Cmd.eval s0) OUTPUT = encodeCnf (threeOccCnf N (encodeCnf N).length) := by
  unfold pass2Cmd
  have hlen : (State.get s0 CNF_STREAM).length = (encodeCnf N).length := by rw [hCNF]
  rw [Cmd.eval_forBnd, hlen]
  have key := Cmd.foldlState_range_induct pass2OuterBody RVVAR (encodeCnf N).length s0
    (fun k sk =>
      State.get sk CNF_STREAM = encodeCnf N ∧
      State.get sk OUTPUT = encodeCnf (threeOccCnf N k))
    ⟨hCNF, by simpa [threeOccCnf, cycleClauses] using hO⟩
    (by
      rintro m sk _ ⟨hcnf, ho⟩
      have hstep := pass2OuterBody_run m (encodeCnf N) (encodeCnf (threeOccCnf N m))
        (sk.set RVVAR (List.replicate m 1))
        (by rw [State.get_set_ne _ RVVAR _ CNF_STREAM (by decide)]; exact hcnf)
        (by rw [State.get_set_eq])
        (by rw [State.get_set_ne _ RVVAR _ OUTPUT (by decide)]; exact ho)
      refine ⟨hstep.1, ?_⟩
      rw [hstep.2, pass2VarOut_encodeCnf, ← encodeCnf_append]
      congr 1
      unfold threeOccCnf cycleClauses
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc])
  exact key.2

theorem threeOccCmd_run (x : List Bool) :
    State.get (threeOccCmd.eval (certState x)) OUTPUT =
      encodeCnf (threeOccCnf (cnfOf x) (encodeCnf (cnfOf x)).length) := by
  rw [threeOccCmd, Cmd.eval_seq, Cmd.eval_seq]
  have h1 : State.get (phase1Cmd.eval (certState x)) CNF_STREAM = encodeCnf (cnfOf x) :=
    phase1_run x
  set s1 := phase1Cmd.eval (certState x)
  have hp1_cnf : State.get (pass1Cmd.eval s1) CNF_STREAM = encodeCnf (cnfOf x) := by
    rw [Cmd.eval_get_of_not_writes _ _ CNF_STREAM (by decide)]
    exact h1
  have hp1_out : State.get (pass1Cmd.eval s1) OUTPUT = encodeCnf (renameCnf (cnfOf x) 0).1 := by
    rw [pass1Cmd, Cmd.eval_seq]
    set s2 := pass1Pre.eval s1
    have hs2_C : State.get s2 WCUR = encodeCnf (cnfOf x) := by
      simp only [s2, pass1Pre, Cmd.eval_seq, Cmd.eval_op, Op.eval]
      rw [State.get_set_ne _ WSB _ WCUR (by decide), State.get_set_ne _ WSA _ WCUR (by decide),
        State.get_set_ne _ OUTPUT _ WCUR (by decide), State.get_set_eq, h1]
    have hs2_O : State.get s2 OUTPUT = [] := by
      simp only [s2, pass1Pre, Cmd.eval_seq, Cmd.eval_op, Op.eval]
      rw [State.get_set_ne _ WSB _ OUTPUT (by decide), State.get_set_ne _ WSA _ OUTPUT (by decide),
        State.get_set_eq]
    have hs2_A : State.get s2 WSA = [] := by
      simp only [s2, pass1Pre, Cmd.eval_seq, Cmd.eval_op, Op.eval]
      rw [State.get_set_ne _ WSB _ WSA (by decide), State.get_set_eq]
    have hs2_B : State.get s2 WSB = [] := by
      simp only [s2, pass1Pre, Cmd.eval_seq, Cmd.eval_op, Op.eval, State.get_set_eq]
    rw [pass1Loop_run _ s2 hs2_C hs2_A hs2_B hs2_O, pass1Run_encodeCnf]
  exact pass2Loop_run (cnfOf x) (pass1Cmd.eval s1) hp1_cnf hp1_out

/-! ## Bounds and `PolyTimeComputableLang threeOccStr` -/

def regs25 : Nat := 2 ^ 25 - 1

theorem threeOccCmd_chk : (threeOccCmd.chk regs25).1 = true := by decide

theorem threeOccCmd_usesBelow : Cmd.UsesBelow threeOccCmd 25 := by
  simp [threeOccCmd, phase1Cmd, phase1Pre, phase1Post, setBotCnf, scanBody,
    pass1Cmd, pass1Pre, pass1Body, pass2Cmd, pass2OuterBody, pass2InnerBody, emitImplCmd,
    Cmd.UsesBelow, Op.UsesBelow,
    WCUR, WIDX, WHD, WSA, WSB, WTAL, OUTPUT, CNF_STREAM,
    RVVAR, RCURV, RHASF, RFIRST, RPREV, RMATCH]

private lemma state_size_certState (x : List Bool) :
    State.size (certState x) ≤ encodable.size x := by
  have hlen : x.length ≤ encodable.size x := CookLevin.length_le_size x
  have hs : State.size (certState x) = x.length := by
    simp [State.size, certState]
  omega

theorem threeOccCmd_cost : ∃ budget : Nat → Nat, inOPoly budget ∧ monotonic budget ∧
    ∀ x : List Bool, threeOccCmd.cost (certState x) ≤ budget (encodable.size x) := by
  obtain ⟨K, D, hb⟩ := Cmd.costLeSize_of_chk threeOccCmd regs25 threeOccCmd_chk
  refine ⟨fun n => K * (n + 1) ^ (D + 1), ?_, ?_, fun x => hb (certState x) _ (state_size_certState x)⟩
  · refine inOPoly_mul (inOPoly_const K) ⟨D + 1, 2 ^ (D + 1), 1, ?_⟩
    intro n hn
    calc (n + 1) ^ (D + 1) ≤ (2 * n) ^ (D + 1) := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (D + 1) * n ^ (D + 1) := by rw [Nat.mul_pow]
  · exact fun a b hab => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

private lemma encodeCnf_cnfOf_len_le (x : List Bool) :
    (encodeCnf (cnfOf x)).length ≤ x.length + 1 := by
  by_cases hwf : wfCnfB (strBits x) = true
  · have h : encodeCnf (cnfOf x) = strBits x := encodeCnf_parseTotal _ (strBits_bit x) hwf
    rw [h, strBits_length]; omega
  · have hbot : cnfOf x = botCnf := parseTotal_of_not_wf _ (by simpa using hwf)
    rw [hbot]; simp [botCnf, encodeCnf, encodeClause]

private lemma encodeCnf_threeOcc_len_le (N : cnf) :
    (encodeCnf (threeOccCnf N (encodeCnf N).length)).length ≤
      4 * ((encodeCnf N).length + 1) ^ 2 := by
  set L := (encodeCnf N).length with hL
  unfold threeOccCnf
  rw [encodeCnf_append, List.length_append]
  -- Bound 1: `encodeCnf (renameCnf N 0).1`
  have hren_len : (encodeCnf (renameCnf N 0).1).length ≤ L * (L + 3) := by
    have hstep : ∀ (l : List Nat) (st : Bool × Bool × Nat × List Nat),
        (l.foldl pass1Step st).2.2.2.length ≤
          st.2.2.2.length + l.length * (st.2.2.1 + l.length + 1) := by
      intro l
      induction l with
      | nil => intro st; simp
      | cons c tl ih =>
          intro ⟨a, b, p, out⟩
          rw [List.foldl_cons]
          have h1 := ih (pass1Step (a, b, p, out) c)
          have hp : (pass1Step (a, b, p, out) c).2.2.1 = p + 1 := by
            cases a <;> cases b <;> dsimp only [pass1Step] <;> split_ifs <;> rfl
          have ho : (pass1Step (a, b, p, out) c).2.2.2.length ≤ out.length + (p + 1) := by
            cases a <;> cases b <;> dsimp only [pass1Step] <;> split_ifs <;> simp <;> omega
          rw [hp] at h1
          have h2 : (c :: tl).length = tl.length + 1 := rfl
          rw [h2]
          nlinarith
    have h0 := hstep (encodeCnf N) (false, false, 0, [])
    rw [show ((encodeCnf N).foldl pass1Step (false, false, 0, [])).2.2.2 =
        encodeCnf (renameCnf N 0).1 from pass1Run_encodeCnf N] at h0
    simp only [List.length_nil, Nat.zero_add] at h0
    nlinarith
  -- Bound 2: `encodeCnf (cycleClauses N L)`
  have hcyc_len : (encodeCnf (cycleClauses N L)).length ≤ (cnfLitEnds N 0).length * (2 * L + 7) := by
    have hgo_len : ∀ (first prev : Nat) (R : List Nat),
        first < L → prev < L → (∀ u ∈ R, u < L) →
        (encodeCnf (cycleGo first prev R)).length ≤ (R.length + 1) * (2 * L + 7) := by
      intro first prev R hf hp hR
      induction R generalizing prev with
      | nil =>
          have h1 : (encodeClause [(false, prev), (true, first)]).length = prev + first + 7 := by
            simp [CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody, encodeLit]; omega
          have h0 : encodeCnf (cycleGo first prev []) = encodeClause [(false, prev), (true, first)] := by
            simp [cycleGo, CnfSerialize.encodeCnf_cons, encodeCnf]
          rw [h0, h1]; simp; omega
      | cons nxt tl ih =>
          simp only [cycleGo, CnfSerialize.encodeCnf_cons, List.length_append]
          have hnxt : nxt < L := hR nxt (List.mem_cons_self ..)
          have h1 : (encodeClause [(false, prev), (true, nxt)]).length ≤ 2 * L + 7 := by
            have heq : (encodeClause [(false, prev), (true, nxt)]).length = prev + nxt + 7 := by
              simp [CnfSerialize.encodeClause_eq, CnfSerialize.clauseBody, encodeLit]; omega
            omega
          have h2 := ih nxt hnxt (fun u hu => hR u (List.mem_cons_of_mem nxt hu))
          simp only [List.length_cons]
          nlinarith
    have hfor_len : ∀ (v : Nat),
        (encodeCnf (cycleForList (occsOfVar N v))).length ≤
          (occsOfVar N v).length * (2 * L + 7) := by
      intro v
      have hall : ∀ u ∈ occsOfVar N v, u < L := by
        intro u hu
        unfold occsOfVar at hu
        rw [List.mem_map] at hu
        rcases hu with ⟨p, hp, rfl⟩
        rw [List.mem_filter] at hp
        have hlt := (cnfLitEnds_bounds N 0 p hp.1).2
        rw [renameCnf_snd, Nat.zero_add] at hlt
        exact hlt
      cases hoc : occsOfVar N v with
      | nil => simp [cycleForList, encodeCnf]
      | cons k0 rest =>
          rw [hoc] at hall
          simpa [cycleForList] using hgo_len k0 k0 rest
            (hall k0 (List.mem_cons_self ..)) (hall k0 (List.mem_cons_self ..))
            (fun u hu => hall u (List.mem_cons_of_mem k0 hu))
    have hsum : ∀ (vs : List Nat), vs.Nodup →
        (encodeCnf (vs.flatMap (fun v => cycleForList (occsOfVar N v)))).length ≤
          ((cnfLitEnds N 0).filter (fun p => p.1.2 ∈ vs)).length * (2 * L + 7) := by
      intro vs hnd
      induction vs with
      | nil => simp [encodeCnf]
      | cons v rest ih =>
          rw [List.nodup_cons] at hnd
          rw [List.flatMap_cons, encodeCnf_append, List.length_append]
          have h1 := hfor_len v
          have h2 := ih hnd.2
          have hpart : (occsOfVar N v).length +
              ((cnfLitEnds N 0).filter (fun p => p.1.2 ∈ rest)).length =
              ((cnfLitEnds N 0).filter (fun p => p.1.2 ∈ v :: rest)).length := by
            unfold occsOfVar
            rw [List.length_map]
            have hgen : ∀ (P : List (literal × Nat)),
                (P.filter (fun p => p.1.2 == v)).length +
                (P.filter (fun p => decide (p.1.2 ∈ rest))).length =
                (P.filter (fun p => decide (p.1.2 ∈ v :: rest))).length := by
              intro P
              induction P with
              | nil => simp
              | cons q qs ihq =>
                  simp only [List.filter_cons]
                  by_cases hqv : q.1.2 = v
                  · have hnr : q.1.2 ∉ rest := fun hm => hnd.1 (hqv ▸ hm)
                    have h1 : (q.1.2 == v) = true := beq_iff_eq.mpr hqv
                    have h2 : decide (q.1.2 ∈ rest) = false := decide_eq_false hnr
                    have h3 : decide (q.1.2 ∈ v :: rest) = true := decide_eq_true (hqv ▸ List.mem_cons_self ..)
                    simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, List.length_cons]
                    omega
                  · have h1 : (q.1.2 == v) = false := beq_false_of_ne hqv
                    have h3 : (q.1.2 ∈ v :: rest) ↔ (q.1.2 ∈ rest) := by simp [hqv]
                    simp only [h1, Bool.false_eq_true, ↓reduceIte, h3]
                    by_cases hqr : q.1.2 ∈ rest
                    · simp only [decide_eq_true hqr, ↓reduceIte, List.length_cons]; omega
                    · simp only [decide_eq_false hqr, Bool.false_eq_true, ↓reduceIte]; omega
            exact hgen (cnfLitEnds N 0)
          nlinarith
    have hle_filt : ((cnfLitEnds N 0).filter (fun p => p.1.2 ∈ List.range L)).length ≤
        (cnfLitEnds N 0).length := List.length_filter_le _ _
    have h3 := hsum (List.range L) List.nodup_range
    unfold cycleClauses
    nlinarith
  have hends_le : (cnfLitEnds N 0).length ≤ L := by
    have hgen : ∀ (N0 : cnf) (pos : Nat), (cnfLitEnds N0 pos).length ≤ (encodeCnf N0).length := by
      intro N0
      induction N0 with
      | nil => intro _; simp [cnfLitEnds, encodeCnf]
      | cons C rest ih =>
          intro pos
          rw [cnfLitEnds, List.length_append, CnfSerialize.encodeCnf_cons, List.length_append,
            CnfSerialize.encodeClause_eq, List.length_append]
          have hc : ∀ (C0 : clause) (p0 : Nat),
              (litEnds C0 p0).length ≤ (CnfSerialize.clauseBody C0).length := by
            intro C0
            induction C0 with
            | nil => intro _; simp [litEnds, CnfSerialize.clauseBody]
            | cons l tl ihtl =>
                intro p0
                rcases l with ⟨pol, v⟩
                rw [litEnds, List.length_cons, CnfSerialize.clauseBody_cons, List.length_append,
                  encodeLit_length]
                have := ihtl (p0 + (v + 3)); unfold litLen; omega
          have h1 := hc C pos
          have h2 := ih ((renameClauseBody C pos).2 + 1)
          omega
    exact hgen N 0
  have hcyc_le2 : (encodeCnf (cycleClauses N L)).length ≤ L * (2 * L + 7) := by
    calc (encodeCnf (cycleClauses N L)).length
      _ ≤ (cnfLitEnds N 0).length * (2 * L + 7) := hcyc_len
      _ ≤ L * (2 * L + 7) := Nat.mul_le_mul_right _ hends_le
  nlinarith

private lemma size_threeOccStr_le (x : List Bool) :
    encodable.size (threeOccStr x) ≤ 8 * (encodable.size x + 2) ^ 2 := by
  have h1 : encodable.size (threeOccStr x) ≤ 2 * (threeOccStr x).length :=
    CookLevin.size_le_two_mul_length (threeOccStr x)
  have h2 : (threeOccStr x).length =
      (encodeCnf (threeOccCnf (cnfOf x) (encodeCnf (cnfOf x)).length)).length := by
    simp [threeOccStr, SATToSATStr.satToStr, boolsOf]
  have h3 := encodeCnf_threeOcc_len_le (cnfOf x)
  have h4 := encodeCnf_cnfOf_len_le x
  have h5 : x.length ≤ encodable.size x := CookLevin.length_le_size x
  nlinarith

noncomputable def threeOccCostBound (n : Nat) : Nat :=
  threeOccCmd_cost.choose n + 8 * (n + 2) ^ 2

theorem threeOccCostBound_poly : inOPoly threeOccCostBound := by
  refine inOPoly_add threeOccCmd_cost.choose_spec.1 ?_
  refine inOPoly_mul (inOPoly_const 8) ⟨2, 9, 1, ?_⟩
  intro n hn
  nlinarith

theorem threeOccCostBound_mono : monotonic threeOccCostBound := by
  intro a b h
  have h1 := threeOccCmd_cost.choose_spec.2.1 a b h
  show _ + 8 * (a + 2) ^ 2 ≤ _ + 8 * (b + 2) ^ 2
  nlinarith

noncomputable def threeOccLang : PolyTimeComputableLang threeOccStr where
  c := threeOccCmd
  encodeIn := certState
  decodeOut := fun s => boolsOf (State.get s OUTPUT)
  cost_bound := threeOccCostBound
  cost_bound_poly := threeOccCostBound_poly
  cost_bound_mono := threeOccCostBound_mono
  encBound := fun n => n
  encBound_poly := inOPoly_id
  encBound_mono := fun _ _ h => h
  encodeIn_size := state_size_certState
  computes := fun x => by
    show boolsOf (State.get (threeOccCmd.eval (certState x)) OUTPUT) = threeOccStr x
    rw [threeOccCmd_run]
    rfl
  cost_le := fun x => by
    have h1 := threeOccCmd_cost.choose_spec.2.2 x
    unfold threeOccCostBound
    omega
  output_size_le := fun x => by
    have h := size_threeOccStr_le x
    unfold threeOccCostBound
    omega
  enc_bit := fun x => by
    intro reg hreg v hv
    simp only [certState, List.mem_singleton] at hreg
    subst hreg
    simp only [List.mem_map] at hv
    rcases hv with ⟨b, _, rfl⟩
    cases b <;> simp
  regBound := 25
  usesBelow := threeOccCmd_usesBelow
  width_le := fun _ => by simp [certState]
  decode_agree := fun x m => by
    have hpad : AgreeBelow 25 (certState x ++ List.replicate m []) (certState x) :=
      fun r _ => State.get_append_replicate_nil (certState x) m r
    have h := Cmd.eval_agree threeOccCmd 25 threeOccCmd_usesBelow hpad
    show boolsOf (State.get _ OUTPUT) = boolsOf (State.get _ OUTPUT)
    rw [h OUTPUT (by decide)]

end PvsNP.Units.m3_sat_to_3occ_sat

theorem PvsNP.Units.m3_sat_to_3occ_sat :
    CookLevin.reducesPoly SATStr
      (fun x => (∀ v : var, ((SATStr.cnfOf x).flatten.countP (fun l => l.2 == v)) ≤ 3) ∧
        SAT (SATStr.cnfOf x)) := by
  obtain ⟨t, M, ht, hM, h1, hcomp⟩ :=
    PvsNP.Units.m3_sat_to_3occ_sat.threeOccLang.toMachine (fun _ => rfl) (fun _ _ => rfl)
  refine ⟨PvsNP.Units.m3_sat_to_3occ_sat.threeOccStr, t, M, ht, hM, h1, hcomp, fun x => ?_⟩
  dsimp only
  rw [PvsNP.Units.m3_sat_to_3occ_sat.cnfOf_threeOccStr]
  constructor
  · intro hsat
    refine ⟨PvsNP.Units.m3_sat_to_3occ_sat.threeOccCnf_countP_le_three _ _, ?_⟩
    exact (PvsNP.Units.m3_sat_to_3occ_sat.sat_iff_threeOccCnf _ _
      (fun C hC l hl => PvsNP.Units.m3_sat_to_3occ_sat.var_lt_encodeCnf_length hC hl)).mp hsat
  · intro ⟨_, hsat⟩
    exact (PvsNP.Units.m3_sat_to_3occ_sat.sat_iff_threeOccCnf _ _
      (fun C hC l hl => PvsNP.Units.m3_sat_to_3occ_sat.var_lt_encodeCnf_length hC hl)).mpr hsat
