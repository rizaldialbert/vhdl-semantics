(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Shift_Left_Hoare_Typed
  imports VHDL_Hoare_Typed Bits_Int_Aux
begin

datatype sig = IN | OUT

definition shiftl :: "nat \<Rightarrow> sig conc_stmt" where
  "shiftl n \<equiv> process {IN} : Bassign_trans OUT (Bshiftl (Bsig IN) n) 1"

lemma potential_tyenv:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bshiftl (Bsig IN) n) 1)"
  shows "\<exists>len>0. \<Gamma> IN = Lty Uns len \<and> \<Gamma> OUT = Lty Uns len \<or> \<Gamma> IN = Lty Sig len \<and> \<Gamma> OUT = Lty Sig len"
  apply (rule seq_wt_cases(4)[OF assms])
  by (metis bexp_wt_cases_shiftl bexp_wt_cases_slice(2))

locale unsigned_shift_left =
  fixes \<Gamma> :: "sig tyenv"
  fixes len :: nat
  fixes amount :: nat
  assumes "0 < len"
  assumes "\<Gamma> IN = Lty Uns len \<and> \<Gamma> OUT = Lty Uns len"
begin

lemma well_typed:
  "seq_wt \<Gamma> (Bassign_trans OUT (Bshiftl (Bsig IN) n) 1)"
  by (rule seq_wt.intros(4))
     (smt bexp_wt.intros(21) bexp_wt.intros(22) bexp_wt.intros(3) unsigned_shift_left_axioms
     unsigned_shift_left_def)

abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

definition inv :: "sig assn2" where
  "inv tw \<equiv> (lof_wline tw OUT (fst tw) = drop amount (lof_wline tw IN (fst tw - 1) @ replicate amount False))"

definition inv2 :: "sig assn2" where
  "inv2 tw \<equiv> (disjnt {IN} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. lof_wline tw OUT i = lof_wline tw OUT (fst tw)))"

lemma inv_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bshiftl (Bsig IN) amount)"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv (fst tw' + 1, snd tw')"
proof - 
  have bexpIN: "bexp_wt \<Gamma> (Bsig IN) (Lty Uns len)" 
    using unsigned_shift_left_axioms unfolding unsigned_shift_left_def by (metis bexp_wt.intros(3))+
  obtain bsIN where evalIN: "eval_world_raw (fst tw) (snd tw) (Bsig IN) = Lv Uns bsIN" and" length bsIN = len "
      using eval_world_raw_lv[OF bexpIN `wityping \<Gamma> (snd tw)`] by blast
  have "lof_wline tw' OUT (fst tw + 1) = lval_of v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = drop amount (lof_wline tw IN (fst tw) @ replicate amount False)"
    using evalIN unfolding v_def eval_world_raw.simps eval_arith.simps Let_def by auto
  finally show ?thesis
    unfolding inv_def tw'_def worldline_upd2_def worldline_upd_def  by auto
qed

lemma inv2_next_time:
  fixes tw v
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  shows   "inv2 (fst tw' + 1, snd tw')"
  unfolding inv2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma conc_hoare:
  "\<And>tw. inv tw \<and> inv2 tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> inv (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "inv tw \<and> inv2 tw \<and> disjnt {IN} (event_of tw)"
  hence "inv tw" and "inv2 tw" and "disjnt {IN} (event_of tw)"
    by auto
  have "lof_wline tw OUT (fst tw + 1) = lof_wline tw OUT (fst tw)"
    using `inv2 tw` `disjnt {IN} (event_of tw)` unfolding inv2_def by auto 
  also have "... = drop amount (lval_of (wline_of tw IN (get_time tw - 1)) @ replicate amount False)"
    using `inv tw` unfolding inv_def by auto
  also have "... = drop amount (lval_of (wline_of tw IN (get_time tw)) @ replicate amount False)"
    using `disjnt {IN} (event_of tw)`  unfolding event_of_alt_def   by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)
  finally show "inv (fst tw + 1, snd tw)"
    unfolding inv_def by auto
qed

lemma conc_hoare2:
  "\<And>tw. inv2 tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> inv2 (fst tw + 1, snd tw)"
  unfolding inv2_def by auto

lemma conc_stmt_wf:
  "conc_stmt_wf (shiftl amount)"
  unfolding shiftl_def conc_stmt_wf_def by auto  

lemma nonneg_delay_conc:
  "nonneg_delay_conc (shiftl amount)"
  unfolding shiftl_def by auto

lemma nonneg_delay_conc':
  "nonneg_delay_conc ( process {IN} : Bassign_trans OUT (Bshiftl (Bsig IN) amount) 1)"
  using nonneg_delay_conc unfolding shiftl_def by auto

lemma conc_wt:
  "conc_wt \<Gamma> (shiftl amount)"
  unfolding shiftl_def  by (meson conc_wt.intros(1) well_typed)

lemma conc_wt':
  "conc_wt \<Gamma> ( process {IN} : Bassign_trans OUT (Bshiftl (Bsig IN) amount) 1)"
  using conc_wt unfolding shiftl_def by auto

lemma conc_sim2':
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace> shiftl amount \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> (shiftl amount) (\<lambda>tw. inv  (fst tw + 1, snd tw) \<and> 
                                                              inv2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf, rule nonneg_delay_conc, rule conc_wt, simp)
  unfolding shiftl_def wp3_conc_single'[OF conc_wt' nonneg_delay_conc'] wp3_fun.simps
  using inv_next_time inv2_next_time conc_hoare conc_hoare2 by presburger

lemma nonneg_delay_add:
  " nonneg_delay (Bassign_trans OUT (Bshiftl (Bsig IN) amount) 1)"
  using nonneg_delay_conc' by auto

lemma init_sat_nand_inv_comb:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) (shiftl amount) (\<lambda>tw. inv tw \<and> inv2 tw)"
  unfolding shiftl_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv (fst tw + 1, snd tw) \<and> inv2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF well_typed nonneg_delay_add], simp)
  unfolding wp3_fun.simps using inv_next_time inv2_next_time by blast

lemma correctness:
  assumes "sim_fin2 w (i + 1) (shiftl amount) tw'" and "wityping \<Gamma> w"
  shows "lof_wline tw' OUT (i + 1) = drop amount (lof_wline tw' IN (i) @ replicate amount False)"
  using grand_correctness[OF assms conc_stmt_wf conc_wt nonneg_delay_conc conc_sim2' init_sat_nand_inv_comb]
  unfolding shiftl_def inv_def  by (metis (no_types, lifting) add_diff_cancel_right' assms(1)
  sim_fin2.cases world_maxtime_lt_fst_tres)

end

end

