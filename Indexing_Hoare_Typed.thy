(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Indexing_Hoare_Typed
  imports VHDL_Hoare_Typed
begin

datatype sig = IN | OUT

definition index :: "sig conc_stmt" where
  "index \<equiv> process {IN} : Bassign_trans OUT (Bindex IN 3) 1"

abbreviation "bof_wline tw sig n \<equiv> bval_of (wline_of tw sig n)"
abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

definition inv :: "sig assn2" where
  "inv tw \<equiv> (bof_wline tw OUT (fst tw) = (lof_wline tw IN (fst tw - 1)) ! 3)"

definition inv' :: "sig assn2" where
  "inv' tw = (disjnt {IN} (event_of tw) \<longrightarrow> (\<forall>i>fst tw. bof_wline tw OUT i = bof_wline tw OUT (fst tw)))"

lemma potential_tyenv:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  shows   "\<exists>ki len. 3 < len \<and> \<Gamma> IN = Lty ki len \<and> \<Gamma> OUT = Bty"
proof (rule seq_wt_cases(4)[OF assms])
  assume "bexp_wt \<Gamma> (Bindex IN 3) (\<Gamma> OUT)"
  then obtain ki len where "bexp_wt \<Gamma> (Bsig IN) (Lty ki len) \<and> 3 < len \<and> \<Gamma> OUT = Bty"
    by (meson bexp_wt_cases(10))
  hence "\<Gamma> IN = Lty ki len" and "\<Gamma> OUT = Bty" and "3 < len"
    by (metis bexp_wt_cases(9))+
  thus ?thesis
    by blast
qed

locale indexing =
  fixes \<Gamma> :: "sig tyenv" and len :: nat
  assumes tyin: "\<Gamma> IN =  Lty Neu len" and tyout: "\<Gamma> OUT = Bty" and len3: "3 < len"
begin

lemma inv_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bindex IN 3)"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv (fst tw' + 1, snd tw')"
proof -
  have bexpIN: "bexp_wt \<Gamma> (Bsig IN) (Lty Neu len)" using tyin  by (metis bexp_wt.intros(3))
  then obtain bsIN where evalIN: "eval_world_raw (fst tw) (snd tw) (Bsig IN) = Lv Neu bsIN" and "length bsIN = len"
    using eval_world_raw_lv[OF bexpIN assms(3)] by auto
  have "bof_wline tw' OUT (fst tw + 1) \<longleftrightarrow> bval_of v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (bsIN ! 3)"
    unfolding v_def using evalIN by auto
  also have "... = lof_wline tw IN (fst tw) ! 3"
    using evalIN by auto
  finally show ?thesis
    unfolding inv_def tw'_def worldline_upd2_def worldline_upd_def  by auto
qed

lemma inv'_next_time:
  fixes tw v
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  shows   "inv' (fst tw' + 1, snd tw')"
  unfolding inv'_def  tw'_def worldline_upd2_def worldline_upd_def by auto

lemma index_conc_hoare:
  "\<And>tw. inv tw \<and> inv' tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow>inv (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "inv tw \<and> inv' tw \<and> disjnt {IN} (event_of tw)"
  hence "inv tw" and "inv' tw" and "disjnt {IN} (event_of tw)"
    by auto
  have "bof_wline tw OUT (fst tw + 1) = bof_wline tw OUT (fst tw)"
    using `inv' tw` `disjnt {IN} (event_of tw)` unfolding inv'_def by auto 
  also have "... = lof_wline tw IN (get_time tw - 1) ! 3"
    using `inv tw` unfolding inv_def by auto
  also have "... = lof_wline tw IN (fst tw) ! 3"
    using `disjnt {IN} (event_of tw)`  unfolding event_of_alt_def  
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)
  finally show "inv (fst tw + 1, snd tw)"
    unfolding inv_def by auto
qed

lemma index_conc_hoare2:
  "\<And>tw. inv' tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> inv' (fst tw + 1, snd tw)"
  unfolding inv'_def by auto

lemma conc_stmt_wf_index:
  "conc_stmt_wf index"
  unfolding index_def conc_stmt_wf_def by auto  

lemma nonneg_delay_conc_index:
  "nonneg_delay_conc index"
  unfolding index_def by auto

lemma nonneg_delay_conc_index':
  "nonneg_delay_conc ( process {IN} : Bassign_trans OUT (Bindex IN 3) 1)"
  using nonneg_delay_conc_index unfolding index_def by auto

lemma conc_wt_index:
  "conc_wt \<Gamma> index"
  unfolding index_def using tyout tyin
  by (intro conc_wt.intros seq_wt.intros)(metis bexp_wt.intros(14) bexp_wt.intros(3) len3)

lemma well_typed:
  "seq_wt \<Gamma> (Bassign_trans OUT (Bindex IN 3) 1)"
  using conc_wt_index unfolding index_def by auto

lemma conc_wt_index':
  "conc_wt \<Gamma> ( process {IN} : Bassign_trans OUT (Bindex IN 3) 1)"
  using conc_wt_index unfolding index_def by auto

lemma index_conc_sim2':
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv tw \<and> inv' tw\<rbrace> index \<lbrace>\<lambda>tw. inv tw \<and> inv' tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> index (\<lambda>tw. inv  (fst tw + 1, snd tw) \<and> 
                                                      inv' (fst tw + 1, snd tw))", rotated])
    apply (rule wp3_conc_is_pre[ OF conc_stmt_wf_index nonneg_delay_conc_index conc_wt_index], simp)
  unfolding index_def wp3_conc_single'[OF conc_wt_index' nonneg_delay_conc_index'] wp3_fun.simps
  using inv_next_time inv'_next_time index_conc_hoare index_conc_hoare2 by presburger

text \<open>Initialisation preserves the invariant\<close>

lemma nonneg_delay_index:
  " nonneg_delay (Bassign_trans OUT (Bindex IN 3) 1)"
  using nonneg_delay_conc_index' by auto

lemma init_sat_index_inv_comb:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) index (\<lambda>tw. inv tw \<and> inv' tw)"
  unfolding index_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv (fst tw + 1, snd tw) \<and> inv' (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF well_typed nonneg_delay_index], simp)
  unfolding wp3_fun.simps using inv_next_time inv'_next_time by blast

lemma correctness:
  assumes "sim_fin2 w (i + 1) index tw'" and "wityping \<Gamma> w"
  shows   "bof_wline tw' OUT (i + 1) = lof_wline tw' IN i ! 3"
  using grand_correctness[OF assms conc_stmt_wf_index conc_wt_index nonneg_delay_conc_index index_conc_sim2' init_sat_index_inv_comb]
  unfolding index_def inv_def by (metis (no_types, lifting) add_diff_cancel_right' assms(1)
  sim_fin2.cases world_maxtime_lt_fst_tres)  

end

end
