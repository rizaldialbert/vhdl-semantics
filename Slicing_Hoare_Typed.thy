(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Slicing_Hoare_Typed
  imports VHDL_Hoare_Typed
begin

datatype sig = IN | OUT

definition slicer :: "sig conc_stmt" where
  "slicer = process {IN} : Bassign_trans OUT (Bslice IN 3 2) 1"

lemma potential_tyenv:
  assumes "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  shows "\<exists>ki len. 3 < len \<and> \<Gamma> IN = Lty ki len \<and> \<Gamma> OUT = Lty ki 2"
proof (rule seq_wt_cases(4)[OF assms])
  assume "bexp_wt \<Gamma> (Bslice IN 3 2) (\<Gamma> OUT)"
  then obtain ki len where "bexp_wt \<Gamma> (Bsig IN) (Lty ki len) \<and> 3 < len \<and> \<Gamma> OUT = Lty ki 2"
    by (metis add_2_eq_Suc add_Suc add_Suc_right add_diff_cancel_right' bexp_wt_cases(8)
    numeral_2_eq_2 numeral_3_eq_3)
  hence "bexp_wt \<Gamma> (Bsig IN) (Lty ki len)" and "3 < len" and "\<Gamma> OUT = Lty ki 2"
    by auto
  hence "\<Gamma> IN = Lty ki len"
    using bexp_wt_cases(9)[OF \<open>bexp_wt \<Gamma> (Bsig IN) (Lty ki len)\<close>] by metis
  thus ?thesis
    using \<open>3 < len\<close> \<open>\<Gamma> OUT = Lty ki 2\<close> by blast
qed

abbreviation "lof_wline tw sig i \<equiv> lval_of (wline_of tw sig i)"

locale slicer_typed = 
  fixes \<Gamma> :: "sig tyenv" and len :: nat and ki :: "signedness"
  assumes tyin: "\<Gamma> IN = Lty ki len" and tyout: "\<Gamma> OUT = Lty ki 2" and len3: "3 < len"
begin

definition inv :: "sig assn2" where
  "inv tw = (let ins = lof_wline tw IN (fst tw - 1); idx = length ins - 1 in
                                          lof_wline tw OUT (fst tw) = nths ins {idx - 3 .. idx - 2})"

definition inv2 :: "sig assn2" where
  "inv2 tw = (disjnt {IN} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. lof_wline tw OUT i = lof_wline tw OUT (fst tw)))"

text \<open>Note that we need the assumption that @{term "type_of x = Lty ki 2"} as there is no
guarantee that @{term "beval_world_raw2 tw (Bslice IN 3 2) x"} would result in a list
of length 2.\<close>

lemma inv_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bslice IN 3 2)"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv (fst tw' + 1, snd tw')"
proof - 
  have bexpIN: "bexp_wt \<Gamma> (Bsig IN) (Lty ki len)" 
    using slicer_typed_axioms unfolding slicer_typed_def by (metis bexp_wt.intros(3))+
  obtain bsIN where evalIN: "eval_world_raw (fst tw) (snd tw) (Bsig IN) = Lv ki bsIN" and" length bsIN = len "
      using eval_world_raw_lv[OF bexpIN `wityping \<Gamma> (snd tw)`] by blast
  have "lof_wline tw' OUT (fst tw + 1) = lval_of v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (let ins = lof_wline tw IN (fst tw); idx = length ins - 1 in nths ins {idx - 3 .. idx - 2})"
    using evalIN `length bsIN = len` len3 unfolding v_def eval_world_raw.simps eval_arith.simps Let_def 
    by (metis comp_def diff_commute val.sel(3) val.simps(6))
  finally show ?thesis
    unfolding inv_def Let_def tw'_def worldline_upd2_def worldline_upd_def by auto
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
  also have "... = (let ins = lof_wline tw IN (get_time tw - 1); idx = length ins - 1 in nths ins {idx - 3..idx - 2})"
    using `inv tw` unfolding inv_def Let_def by auto
  also have "... = (let ins = lof_wline tw IN (get_time tw); idx = length ins - 1 in nths ins {idx - 3..idx - 2})"
    using `disjnt {IN} (event_of tw)`  unfolding event_of_alt_def   by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)
  finally show "inv (fst tw + 1, snd tw)"
    unfolding inv_def by auto
qed

lemma conc_hoare2:
  "\<And>tw. inv2 tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> inv2 (fst tw + 1, snd tw)"
  unfolding inv2_def by auto

lemma conc_stmt_wf:
  "conc_stmt_wf (slicer)"
  unfolding slicer_def conc_stmt_wf_def by auto  

lemma nonneg_delay_conc:
  "nonneg_delay_conc (slicer)"
  unfolding slicer_def by auto

lemma nonneg_delay_conc':
  "nonneg_delay_conc ( process {IN} : Bassign_trans OUT (Bslice IN 3 2) 1)"
  using nonneg_delay_conc unfolding slicer_def by auto

lemma well_typed:
  "seq_wt \<Gamma> (Bassign_trans OUT (Bslice IN 3 2) 1)"
  by (intro seq_wt.intros)
     (smt Suc_diff_Suc Suc_eq_plus1 add_lessD1 bexp_wt.intros(3) bexp_wt.simps
  cancel_comm_monoid_add_class.diff_cancel len3 lessI nat_less_le numeral_2_eq_2 numeral_3_eq_3 tyin
  tyout)

lemma conc_wt:
  "conc_wt \<Gamma> (slicer)"
  unfolding slicer_def  by (meson conc_wt.intros(1) well_typed)

lemma conc_wt':
  "conc_wt \<Gamma> ( process {IN} : Bassign_trans OUT (Bslice IN 3 2) 1)"
  using conc_wt unfolding slicer_def by auto

lemma conc_sim2':
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace> slicer \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> slicer (\<lambda>tw. inv  (fst tw + 1, snd tw) \<and> 
                                                       inv2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf, rule nonneg_delay_conc, rule conc_wt, simp)
  unfolding slicer_def wp3_conc_single'[OF conc_wt' nonneg_delay_conc'] wp3_fun.simps
  using inv_next_time inv2_next_time conc_hoare conc_hoare2 by presburger

lemma nonneg_delay_add:
  " nonneg_delay (Bassign_trans OUT (Bslice IN 3 2) 1)"
  using nonneg_delay_conc' by auto

lemma init_sat_nand_inv_comb:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) (slicer) (\<lambda>tw. inv tw \<and> inv2 tw)"
  unfolding slicer_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv (fst tw + 1, snd tw) \<and> inv2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF well_typed nonneg_delay_add], simp)
  unfolding wp3_fun.simps using inv_next_time inv2_next_time by blast

lemma correctness:
  assumes "sim_fin2 w (i + 1) (slicer) tw'" and "wityping \<Gamma> w"
  shows "let ins = lof_wline tw' IN i; idx = length ins - 1 in
                                          lof_wline tw' OUT (i + 1) = nths ins {idx - 3 .. idx - 2}"
  using grand_correctness[OF assms conc_stmt_wf conc_wt nonneg_delay_conc conc_sim2' init_sat_nand_inv_comb]
  unfolding slicer_def inv_def  by (metis (no_types, lifting) add_diff_cancel_right' assms(1)
  sim_fin2.cases world_maxtime_lt_fst_tres)

end