(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Multiplexer_Hoare_Typed
  imports VHDL_Hoare_Typed
begin

text \<open>Define the new datatype for the all signals occurred in a multiplexer. A multiplexer has three
inputs: in0, in1, and a selector.\<close>

datatype sig = IN0 | IN1 | SEL | OUT

\<comment> \<open>We put suffix 2 because it only selects between two inputs\<close>
definition mux2 :: "sig conc_stmt" where
  "mux2 = process {IN0, IN1, SEL} : Bguarded (Bsig SEL)
                                      (Bassign_trans OUT (Bsig IN1) 1)
                                      (Bassign_trans OUT (Bsig IN0) 1)"

lemma potential_tyenv:
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL)
                                      (Bassign_trans OUT (Bsig IN1) 1)
                                      (Bassign_trans OUT (Bsig IN0) 1))"
  shows "\<exists>ki len. \<Gamma> IN0 = Bty \<and> \<Gamma> IN1 = Bty \<and> \<Gamma> SEL = Bty \<and> \<Gamma> OUT = Bty
             \<or> \<Gamma> IN0 = Lty ki len \<and> \<Gamma> IN1 = Lty ki len \<and> \<Gamma> SEL = Bty \<and> \<Gamma> OUT = Lty ki len"
proof  (rule seq_wt_cases(3)[OF assms])
  assume "bexp_wt \<Gamma> (Bsig SEL) Bty"
  assume "seq_wt \<Gamma> (Bassign_trans OUT (Bsig IN1) 1)"
  assume "seq_wt \<Gamma> (Bassign_trans OUT (Bsig IN0) 1)"
  have "\<Gamma> SEL = Bty"
    by (rule bexp_wt_cases_all[OF \<open>bexp_wt \<Gamma> (Bsig SEL) Bty\<close>]) auto
  have " bexp_wt \<Gamma> (Bsig IN1) (\<Gamma> OUT)"
    using seq_wt_cases(4)[OF \<open>seq_wt \<Gamma> (Bassign_trans OUT (Bsig IN1) 1)\<close>] by auto
  hence "\<Gamma> IN1 = \<Gamma> OUT"
    by (rule bexp_wt_cases_all) auto
  have "bexp_wt \<Gamma> (Bsig IN0) (\<Gamma> OUT)"
    using seq_wt_cases(4)[OF \<open>seq_wt \<Gamma> (Bassign_trans OUT (Bsig IN0) 1)\<close>] by auto
  hence "\<Gamma> IN0 = \<Gamma> OUT"
    by (rule bexp_wt_cases_all) auto
  obtain ki len where "\<Gamma> OUT = Bty \<or> \<Gamma> OUT = Lty ki len"
    using ty.exhaust by meson
  moreover
  { assume "\<Gamma> OUT = Bty"
    hence "\<Gamma> IN0 = Bty"
      by (simp add: \<open>\<Gamma> IN0 = \<Gamma> OUT\<close>)
    moreover have "\<Gamma> IN1 = Bty"
      using \<open>\<Gamma> IN1 = \<Gamma> OUT\<close> \<open>\<Gamma> OUT = Bty\<close> by auto
    ultimately have ?thesis
      using \<open>\<Gamma> OUT = Bty\<close> \<open>\<Gamma> SEL = Bty\<close> by blast }
  moreover
  { assume "\<Gamma> OUT = Lty ki len"
    moreover hence "\<Gamma> IN0 = Lty ki len" and "\<Gamma> IN1 = Lty ki len"
      using \<open>\<Gamma> IN0 = \<Gamma> OUT\<close> \<open>\<Gamma> IN1 = \<Gamma> OUT\<close> by auto
    ultimately have ?thesis
      using \<open>\<Gamma> SEL = Bty\<close> by blast }
  ultimately show ?thesis
    by auto
qed

abbreviation "bval_of_wline tw sig t \<equiv> bval_of (wline_of tw sig t)"

locale multiplexer_typed = 
  fixes \<Gamma> :: "sig tyenv" and len :: nat and ki :: "signedness"
  assumes tyin0: "\<Gamma> IN0 = Lty ki len" and tyin1: "\<Gamma> IN1 = Lty ki len " and tysel: " \<Gamma> SEL = Bty" and tyout: "\<Gamma> OUT = Lty ki len"  
begin

definition inv :: "sig assn2" where
  "inv \<equiv> \<lambda>tw. (wline_of tw OUT (fst tw) = (if bval_of_wline tw SEL (fst tw - 1) then wline_of tw IN1 (fst tw - 1) else wline_of tw IN0 (fst tw - 1)))"

definition inv2 :: "sig assn2" where
  "inv2 \<equiv> (\<lambda>tw. disjnt {IN0, IN1, SEL} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. wline_of tw OUT i = wline_of tw OUT (fst tw)))"

lemma inv_next_time_true:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bsig IN1)"
  assumes "eval_world_raw2 tw (Bsig SEL) = Bv True"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  shows   "inv (fst tw' + 1, snd tw')"
proof - 
  have bexpIN1: "bexp_wt \<Gamma> (Bsig SEL) (Bty)" 
    using multiplexer_typed_axioms unfolding multiplexer_typed_def by (metis bexp_wt.intros(3))+
  have "wline_of tw' OUT (fst tw + 1) = v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw IN0 (fst tw))"
    using assms(2) unfolding v_def eval_world_raw.simps eval_arith.simps  Let_def comp_def by auto
  finally show ?thesis
    unfolding inv_def tw'_def worldline_upd2_def worldline_upd_def  by auto
qed

lemma inv_next_time_false:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bsig IN0)"
  assumes "eval_world_raw2 tw (Bsig SEL) \<noteq> Bv True"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "inv (fst tw' + 1, snd tw')"
proof - 
  have bexpIN1: "bexp_wt \<Gamma> (Bsig SEL) (Bty)" 
    using multiplexer_typed_axioms unfolding multiplexer_typed_def by (metis bexp_wt.intros(3))+
  hence "eval_world_raw2 tw (Bsig SEL) = Bv False"
    using eval_world_raw_bv[OF bexpIN1 assms(4)] assms(2) by metis
  have "wline_of tw' OUT (fst tw + 1) = v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw IN0 (fst tw))"
    using `eval_world_raw2 tw (Bsig SEL) = Bv False` unfolding v_def eval_world_raw.simps eval_arith.simps  Let_def comp_def by auto
  finally show ?thesis
    unfolding inv_def tw'_def worldline_upd2_def worldline_upd_def  by auto
qed

lemma inv2_next_time:
  fixes tw v
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  shows   "inv2 (fst tw' + 1, snd tw')"
  unfolding inv2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma mult_conc_hoare:
  "\<And>tw. inv tw \<and> inv2 tw \<and> disjnt {IN0, IN1, SEL} (event_of tw) \<Longrightarrow> inv (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "inv tw \<and> inv2 tw \<and> disjnt {IN0, IN1, SEL} (event_of tw)"
  hence "inv tw" and "inv2 tw" and "disjnt {IN0, IN1, SEL} (event_of tw)"
    by auto
  have "wline_of tw OUT (fst tw + 1) = wline_of tw OUT (fst tw)"
    using `inv2 tw` `disjnt {IN0, IN1, SEL} (event_of tw)` unfolding inv2_def by auto 
  also have "... = (if bval_of_wline tw SEL (get_time tw - 1) then wline_of tw IN1 (get_time tw - 1) else wline_of tw IN0 (get_time tw - 1))"
    using `inv tw` unfolding inv_def by auto
  also have "... = (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw IN0 (fst tw))"
    using `disjnt {IN0, IN1, SEL} (event_of tw)`  unfolding event_of_alt_def  
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)
  finally show "inv (fst tw + 1, snd tw)"
    unfolding inv_def by auto
qed

lemma mult_conc_hoare2:
  "\<And>tw. inv2 tw \<and> disjnt {IN0, IN1, SEL} (event_of tw) \<Longrightarrow> inv2 (fst tw + 1, snd tw)"
  unfolding inv2_def by auto

lemma conc_stmt_wf_mult:
  "conc_stmt_wf mux2"
  unfolding mux2_def conc_stmt_wf_def by auto  

lemma nonneg_delay_conc_mult:
  "nonneg_delay_conc mux2"
  unfolding mux2_def by auto

lemma nonneg_delay_conc_mult':
  "nonneg_delay_conc ( process {IN0, IN1, SEL} : Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  using nonneg_delay_conc_mult unfolding mux2_def by auto

lemma well_typed:
  "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  by (metis bexp_wt.intros(3) seq_wt.intros(3) seq_wt.intros(4) tyin0 tyin1 tyout tysel)

lemma conc_wt_mult:
  "conc_wt \<Gamma> mux2"
  unfolding mux2_def by (meson conc_wt.intros(1) well_typed)

lemma conc_wt_mult':
  "conc_wt \<Gamma> ( process {IN0, IN1, SEL} : Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  using conc_wt_mult unfolding mux2_def by auto

lemma mult_conc_sim2':
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace> mux2 \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> mux2 (\<lambda>tw. inv  (fst tw + 1, snd tw) \<and> 
                                                     inv2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_mult, rule nonneg_delay_conc_mult, rule conc_wt_mult, simp)
  unfolding mux2_def  wp3_conc_single'[OF conc_wt_mult' nonneg_delay_conc_mult'] wp3_fun.simps  
  using inv_next_time_true inv_next_time_false inv2_next_time mult_conc_hoare mult_conc_hoare2 by presburger

text \<open>Initialisation preserves the invariant\<close>

lemma nonneg_delay_mult:
  "nonneg_delay ( Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  using nonneg_delay_conc_mult' by auto

lemma init_sat_nand_inv_comb:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) mux2 (\<lambda>tw. inv tw \<and> inv2 tw)"
  unfolding mux2_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv (fst tw + 1, snd tw) \<and> inv2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF well_typed nonneg_delay_mult], simp)
  unfolding wp3_fun.simps using inv_next_time_true inv_next_time_false inv2_next_time by auto

lemma correctness:
  assumes "sim_fin2 w (i + 1) mux2 tw'" and "wityping \<Gamma> w"
  shows "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL (i) then wline_of tw' IN1 (i) else wline_of tw' IN0 (i))"
  using grand_correctness[OF assms conc_stmt_wf_mult conc_wt_mult nonneg_delay_conc_mult mult_conc_sim2' init_sat_nand_inv_comb]
  unfolding mux2_def inv_def by (metis (no_types, lifting) add_diff_cancel_right' assms(1)
  sim_fin2.cases world_maxtime_lt_fst_tres)
end

end