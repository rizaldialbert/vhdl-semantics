(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Signed_Add_Trans_Typed
  imports VHDL_Hoare_Typed Bits_Int_Aux
begin

datatype sig = A | B | C

definition add :: "sig conc_stmt" where
  "add \<equiv> process {A, B} : Bassign_trans C (Badd (Bsig A) (Bsig B)) 1"

locale signed_addition =
  fixes \<Gamma> :: "sig tyenv"
  fixes len len1 len2 :: nat
  assumes len_def: "len = max len1 len2"
  assumes atype: "\<Gamma> A = Lty Sig len1" and btype: "\<Gamma> B = Lty Sig len2" and ctype: "\<Gamma> C = Lty Sig len"
  assumes len1: "0 < len1" and len2: "0 < len2"
begin

lemma well_typed:
  "seq_wt \<Gamma> (Bassign_trans C (Badd (Bsig A) (Bsig B)) 1)"
  by (metis atype bexp_wt.intros(16) bexp_wt.intros(3) btype ctype len1 len2 len_def
  seq_wt.intros(4))

abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

text \<open>Here we factor out common expression in both inv1 and inv2. It is parametrised by the index
we are interested with for C (first argument) and A (the second argument). Note that the index
we are interested with for A should be the same as the index for B.\<close>

definition inv :: "sig assn2" where
  "inv tw \<equiv> (lof_wline tw C (fst tw) = bin_to_bl len (sbl_to_bin (lof_wline tw A (fst tw - 1)) + sbl_to_bin (lof_wline tw B (fst tw - 1))))"

definition inv2 :: "sig assn2" where
  "inv2 tw \<equiv> (disjnt {A, B} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. lof_wline tw C i = lof_wline tw C (fst tw)))"

lemma inv_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Badd (Bsig A) (Bsig B))"
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv (fst tw' + 1, snd tw')"
proof - 
  have bexpA: "bexp_wt \<Gamma> (Bsig A) (Lty Sig len1)" and bexpB: "bexp_wt \<Gamma> (Bsig B) (Lty Sig len2)"
    using signed_addition_axioms unfolding signed_addition_def by (metis bexp_wt.intros(3))+
  obtain bsA bsB where evalA: "eval_world_raw (fst tw) (snd tw) (Bsig A) = Lv Sig bsA" and" length bsA = len1 " and
                       evalB: "eval_world_raw (fst tw) (snd tw) (Bsig B) = Lv Sig bsB" and" length bsB = len2 "
      using eval_world_raw_lv[OF bexpA `wityping \<Gamma> (snd tw)`] eval_world_raw_lv[OF bexpB `wityping \<Gamma> (snd tw)`] by blast
  have "lof_wline tw' C (fst tw + 1) = lval_of v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = bin_to_bl len (sbl_to_bin (lof_wline tw A (fst tw)) + sbl_to_bin (lof_wline tw B (fst tw)))"
    using evalA evalB `length bsA = len1` `length bsB = len2`
    unfolding v_def eval_world_raw.simps eval_arith.simps len_def Let_def by auto
  finally show ?thesis
    unfolding inv_def tw'_def worldline_upd2_def worldline_upd_def  by auto
qed

lemma inv2_next_time:
  fixes tw v
  defines "tw' \<equiv> tw[C, 1 :=\<^sub>2 v]"
  shows   "inv2 (fst tw' + 1, snd tw')"
  unfolding inv2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma add_conc_hoare:
  "\<And>tw. inv tw \<and> inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> inv (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "inv tw \<and> inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "inv tw" and "inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  have "lof_wline tw C (fst tw + 1) = lof_wline tw C (fst tw)"
    using `inv2 tw` `disjnt {A, B} (event_of tw)` unfolding inv2_def by auto 
  also have "... = bin_to_bl len (sbl_to_bin (lval_of (wline_of tw A (get_time tw - 1))) + sbl_to_bin (lval_of (wline_of tw B (get_time tw - 1))))"
    using `inv tw` unfolding inv_def by auto
  also have "... = bin_to_bl len (sbl_to_bin (lval_of (wline_of tw A (fst tw))) + sbl_to_bin (lval_of (wline_of tw B (fst tw))))"
    using `disjnt {A, B} (event_of tw)`  unfolding event_of_alt_def  
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)
  finally show "inv (fst tw + 1, snd tw)"
    unfolding inv_def by auto
qed

lemma add_conc_hoare2:
  "\<And>tw. inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> inv2 (fst tw + 1, snd tw)"
  unfolding inv2_def by auto

lemma conc_stmt_wf_add:
  "conc_stmt_wf add"
  unfolding add_def conc_stmt_wf_def by auto  

lemma nonneg_delay_conc_add:
  "nonneg_delay_conc add"
  unfolding add_def by auto

lemma nonneg_delay_conc_add':
  "nonneg_delay_conc ( process {A, B} : Bassign_trans C (Badd (Bsig A) (Bsig B)) 1)"
  using nonneg_delay_conc_add unfolding add_def by auto

lemma conc_wt_add:
  "conc_wt \<Gamma> add"
  unfolding add_def  by (meson conc_wt.intros(1) well_typed)

lemma conc_wt_add':
  "conc_wt \<Gamma> ( process {A, B} : Bassign_trans C (Badd (Bsig A) (Bsig B)) 1)"
  using conc_wt_add unfolding add_def by auto

lemma add_conc_sim2':
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace> add \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> add (\<lambda>tw. inv  (fst tw + 1, snd tw) \<and> 
                                                      inv2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_add, rule nonneg_delay_conc_add, rule conc_wt_add, simp)
  unfolding add_def  wp3_conc_single'[OF conc_wt_add' nonneg_delay_conc_add'] wp3_fun.simps
  using inv_next_time inv2_next_time add_conc_hoare add_conc_hoare2 by presburger

text \<open>Initialisation preserves the invariant\<close>

lemma nonneg_delay_add:
  " nonneg_delay (Bassign_trans C (Badd (Bsig A) (Bsig B)) 1)"
  using nonneg_delay_conc_add' by auto

lemma init_sat_nand_inv_comb:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) add (\<lambda>tw. inv tw \<and> inv2 tw)"
  unfolding add_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv (fst tw + 1, snd tw) \<and> inv2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF well_typed nonneg_delay_add], simp)
  unfolding wp3_fun.simps using inv_next_time inv2_next_time by blast

lemma correctness:
  assumes "sim_fin2 w (i + 1) add tw'" and "wityping \<Gamma> w"
  shows "lof_wline tw' C (i + 1) = bin_to_bl len (sbl_to_bin (lof_wline tw' A i) + sbl_to_bin (lof_wline tw' B i))"
  using grand_correctness[OF assms conc_stmt_wf_add conc_wt_add nonneg_delay_conc_add add_conc_sim2' init_sat_nand_inv_comb]
  unfolding add_def inv_def by (metis (no_types, lifting) add_diff_cancel_right' assms(1)
  sim_fin2.cases world_maxtime_lt_fst_tres)
end

end
