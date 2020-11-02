(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Decoder_Typed
  imports VHDL_Hoare_Typed
begin

datatype sig = IN | OUT

abbreviation dec_list :: "(sig choices \<times> sig seq_stmt) list" where
  "dec_list \<equiv>
[ (Explicit (Bliteral Neu (to_bl (0b00 :: 2 word))), Bassign_trans OUT (Bliteral Neu (to_bl (0x1:: 4 word))) 1)
, (Explicit (Bliteral Neu (to_bl (0b01 :: 2 word))), Bassign_trans OUT (Bliteral Neu (to_bl (0x2:: 4 word))) 1)
, (Explicit (Bliteral Neu (to_bl (0b10 :: 2 word))), Bassign_trans OUT (Bliteral Neu (to_bl (0x4:: 4 word))) 1)
, (Explicit (Bliteral Neu (to_bl (0b11 :: 2 word))), Bassign_trans OUT (Bliteral Neu (to_bl (0x8:: 4 word))) 1)
]"

definition dec :: "sig conc_stmt" where
  "dec = process {IN} : Bcase (Bsig IN) dec_list"

lemma potential_tyenv:
  assumes "seq_wt \<Gamma> (Bcase (Bsig IN) dec_list)"
  shows   "\<Gamma> IN = Lty Neu 2 \<and> \<Gamma> OUT = Lty Neu 4"
proof (rule seq_wt_cases_bcase[OF assms, rotated 2])
  fix ty exp' ss choices
  assume "bexp_wt \<Gamma> (Bsig IN) ty"
  assume "bexp_wt \<Gamma> exp' ty"
  assume "seq_wt \<Gamma> ss"
  assume "seq_wt \<Gamma> (Bcase (Bsig IN) choices)"
  assume "dec_list = ((Explicit exp', ss) # choices)"
  hence "exp' = Bliteral Neu (to_bl (0b00 :: 2 word))" and "choices = tl dec_list" and
        ss_def: "ss = Bassign_trans OUT (Bliteral Neu (to_bl (0x1 :: 4 word))) 1"
    by auto
  hence 0: "bexp_wt \<Gamma> (Bliteral Neu (to_bl (0b000 :: 2 word))) ty"
    using \<open>bexp_wt \<Gamma> exp' ty\<close> by auto
  have "ty = Lty Neu 2"
    by (rule bexp_wt_cases_lit[OF 0]) auto
  with \<open>bexp_wt \<Gamma> (Bsig IN) ty\<close> have "\<Gamma> IN = Lty Neu 2"
    by (metis bexp_wt_cases_slice(2))
  hence 1: "seq_wt \<Gamma> (Bassign_trans OUT (Bliteral Neu (to_bl (0x1 :: 4 word))) 1)"
    using \<open>seq_wt \<Gamma> ss\<close> unfolding ss_def by auto
  have "\<Gamma> OUT = Lty Neu 4"
    apply (rule seq_wt_cases(4)[OF 1])
    apply (erule bexp_wt_cases_lit)
    by auto
  thus ?thesis
    using \<open>\<Gamma> IN = Lty Neu 2\<close> by auto
qed auto

abbreviation "lof_wline tw sig t \<equiv> lval_of (wline_of tw sig t)"

locale decoder =
  fixes \<Gamma> :: "sig tyenv"
  assumes tyin: "\<Gamma> IN =  Lty Neu 2" and tyout: "\<Gamma> OUT = Lty Neu 4"
begin

definition dec_inv :: "sig assn2" where
  "dec_inv \<equiv> \<lambda>tw. bl_to_bin (lof_wline tw OUT (fst tw)) = 2 ^ nat (bl_to_bin (lof_wline tw IN (fst tw - 1)))"

definition dec_inv2 :: "sig assn2" where
  "dec_inv2 \<equiv> \<lambda>tw. disjnt {IN} (event_of tw) \<longrightarrow> (\<forall>i > fst tw.  lof_wline tw OUT i = lof_wline tw OUT (fst tw))"

abbreviation "ntime tw \<equiv> next_time_world tw"

lemma one_encoding:
  "to_bl (1 :: 2 word) = [False, True]"
  by eval

lemma conc_stmt_wf_dec:
  "conc_stmt_wf dec"
  unfolding dec_def conc_stmt_wf_def by auto  

lemma nonneg_delay_conc_dec:
  "nonneg_delay_conc dec"
  unfolding dec_def by auto

lemma nonneg_delay_conc_dec':
  "nonneg_delay_conc (process {IN} : Bcase (Bsig IN) dec_list)"
  using nonneg_delay_conc_dec unfolding dec_def by auto

lemma len4:
  "length (to_bl (n :: 4 word)) = 4"
  by simp

lemma len2:
  "length (to_bl (n :: 2 word)) = 2"
  by simp

lemma seq_wt_dec:
  "seq_wt \<Gamma> (Bcase (Bsig IN) dec_list)"
  using tyin tyout 
  by (metis bexp_wt.intros(26) bexp_wt.intros(3) len2 len4 seq_wt.intros(4) seq_wt.intros(6)
  seq_wt.intros(8) tyin tyout)

lemma conc_wt_dec:
  "conc_wt \<Gamma> dec"
  unfolding dec_def using seq_wt_dec conc_wt.intros(1) by blast 
  
lemma conc_wt_dec':
  "conc_wt \<Gamma> ( process {IN} : Bcase (Bsig IN) dec_list)"
  using conc_wt_dec unfolding dec_def by auto

lemma one_encoding4:
  "to_bl (1 :: 4 word) = [False, False, False, True]"
  by eval

lemma case0:
  assumes "eval_world_raw2 tw (Bsig IN) = eval_world_raw2 tw (Bliteral Neu (to_bl (0 :: 2 word)))"
  defines "v \<equiv> eval_world_raw2 tw (Bliteral Neu (to_bl (1 :: 4 word)))"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "dec_inv (fst tw' + 1, snd tw')"
proof -
  have "lof_wline tw' OUT (fst tw + 1) = lval_of v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = [False, False, False, True]"
    using one_encoding4 unfolding v_def by auto
  finally have *: "bl_to_bin (lof_wline tw' OUT (fst tw + 1)) = 1"
    by simp eval
  have "lof_wline tw' IN (fst tw) = lof_wline tw IN (fst tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = [False, False]"
    using assms(1) by auto
  finally have "bl_to_bin (lof_wline tw' IN (fst tw)) = 0"
    by simp 
  thus ?thesis
    using * unfolding dec_inv_def  by (simp add: tw'_def)
qed

lemma case1:
  assumes "eval_world_raw2 tw (Bsig IN) = eval_world_raw2 tw (Bliteral Neu (to_bl (1 :: 2 word)))"
  defines "v \<equiv> eval_world_raw2 tw (Bliteral Neu (to_bl (2 :: 4 word)))"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "dec_inv (fst tw' + 1, snd tw')"
proof -
  have "lof_wline tw' OUT (fst tw + 1) = lval_of v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = [False, False, True, False]"
    using one_encoding4 unfolding v_def by auto
  finally have *: "bl_to_bin (lof_wline tw' OUT (fst tw + 1)) = 2"
    by simp eval
  have "lof_wline tw' IN (fst tw) = lof_wline tw IN (fst tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = [False, True]"
    using assms(1) by auto eval
  finally have "bl_to_bin (lof_wline tw' IN (fst tw)) = 1"
    by simp eval
  thus ?thesis
    using * unfolding dec_inv_def  by (simp add: tw'_def)
qed

lemma case2:
  assumes "eval_world_raw2 tw (Bsig IN) = eval_world_raw2 tw (Bliteral Neu (to_bl (2 :: 2 word)))"
  defines "v \<equiv> eval_world_raw2 tw (Bliteral Neu (to_bl (4 :: 4 word)))"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "dec_inv (fst tw' + 1, snd tw')"
proof -
  have "lof_wline tw' OUT (fst tw + 1) = lval_of v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = [False, True, False, False]"
    using one_encoding4 unfolding v_def by auto
  finally have *: "bl_to_bin (lof_wline tw' OUT (fst tw + 1)) = 4"
    by simp eval
  have "lof_wline tw' IN (fst tw) = lof_wline tw IN (fst tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = [True, False]"
    using assms(1) by auto
  finally have "bl_to_bin (lof_wline tw' IN (fst tw)) = 2"
    by simp eval
  thus ?thesis
    using * unfolding dec_inv_def  by (simp add: tw'_def)
qed

lemma case3:
  assumes "eval_world_raw2 tw (Bsig IN) = eval_world_raw2 tw (Bliteral Neu (to_bl (3 :: 2 word)))"
  defines "v \<equiv> eval_world_raw2 tw (Bliteral Neu (to_bl (8 :: 4 word)))"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "dec_inv (fst tw' + 1, snd tw')"
proof -
  have "lof_wline tw' OUT (fst tw + 1) = lval_of v"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = [True, False, False, False]"
    using one_encoding4 unfolding v_def by auto
  finally have *: "bl_to_bin (lof_wline tw' OUT (fst tw + 1)) = 8"
    by simp eval
  have "lof_wline tw' IN (fst tw) = lof_wline tw IN (fst tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = [True, True]"
    using assms(1) by auto
  finally have "bl_to_bin (lof_wline tw' IN (fst tw)) = 3"
    by simp eval
  thus ?thesis
    using * unfolding dec_inv_def  by (simp add: tw'_def)
qed

lemma dec_inv2_next_time:
  fixes tw v
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  shows   "dec_inv2 (fst tw' + 1, snd tw')"
  unfolding dec_inv2_def tw'_def worldline_upd2_def worldline_upd_def by auto

lemma dec_conc_hoare:
  "\<And>tw. dec_inv tw \<and> dec_inv2 tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> dec_inv (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "dec_inv tw \<and> dec_inv2 tw \<and> disjnt {IN} (event_of tw)"
  hence "dec_inv tw" and "dec_inv2 tw" and "disjnt {IN} (event_of tw)"
    by auto
  have "lof_wline tw OUT (fst tw + 1) = lof_wline tw OUT (fst tw)"
    using `dec_inv2 tw` `disjnt {IN} (event_of tw)` unfolding dec_inv2_def by auto 
  also have "bl_to_bin ... = 2 ^ nat (bl_to_bin (lof_wline tw IN (get_time tw - 1)))"
    using `dec_inv tw` unfolding dec_inv_def by auto
  also have "... = 2 ^ nat (bl_to_bin (lof_wline tw IN (get_time tw)))"
    using `disjnt {IN} (event_of tw)`  unfolding event_of_alt_def  
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)
  finally show "dec_inv (fst tw + 1, snd tw)"
    unfolding dec_inv_def by auto
qed

lemma dec_conc_hoare2:
  "\<And>tw. dec_inv2 tw \<and> disjnt {IN} (event_of tw) \<Longrightarrow> dec_inv2 (fst tw + 1, snd tw)"
  unfolding dec_inv2_def by auto


lemma cases: 
  assumes "wityping \<Gamma> (snd tw)"
  shows "eval_world_raw2 tw (Bsig IN) = Lv Neu [False, False] \<or> eval_world_raw2 tw (Bsig IN) = Lv Neu [False, True]
      \<or> eval_world_raw2 tw (Bsig IN) = Lv Neu [True, False] \<or> eval_world_raw2 tw (Bsig IN) = Lv Neu [True, True]"
proof -
  have "bexp_wt \<Gamma> (Bsig IN) (Lty Neu 2)"
    using tyin by (metis bexp_wt.intros(3))
  then obtain xs where *: "eval_world_raw2 tw (Bsig IN) = Lv Neu xs" and "length xs = 2"
    using eval_world_raw_lv[OF _ assms] by blast
  have "xs = [False, False] \<or> xs = [False, True] \<or> xs = [True, False] \<or> xs = [True, True]"
    using \<open>length xs = 2\<close>
  proof (induction xs)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs)
    have "a = True \<or> a = False"
      by auto
    hence "length xs = 1"
      using Cons by auto
    hence "xs = [True] \<or> xs = [False]"
      by (metis (full_types) One_nat_def length_0_conv length_Suc_conv)
    then show ?case
      using \<open>a = True \<or> a = False\<close> by auto
  qed
  thus ?thesis
    using * by auto
qed

lemma dec_sim:
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. dec_inv tw \<and> dec_inv2 tw\<rbrace> dec \<lbrace>\<lambda>tw. dec_inv tw \<and> dec_inv2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> dec (\<lambda>tw. dec_inv  (fst tw + 1, snd tw) \<and> 
                                                    dec_inv2 (fst tw + 1, snd tw))", rotated])
    apply (rule wp3_conc_is_pre[OF conc_stmt_wf_dec nonneg_delay_conc_dec conc_wt_dec], simp)
  unfolding dec_def  wp3_conc_single'[OF conc_wt_dec' nonneg_delay_conc_dec'] wp3_fun.simps
  using case0 case1 case2 case3 cases dec_inv2_next_time dec_conc_hoare dec_conc_hoare2 one_encoding
  by auto fastforce+

text \<open>Initialisation preserves the invariant\<close>

lemma nonneg_delay_dec:
  "nonneg_delay (Bcase (Bsig IN) dec_list)"
  by auto

lemma init_sat_nand_inv_comb:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) dec (\<lambda>tw. dec_inv tw \<and> dec_inv2 tw)"
  unfolding dec_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. dec_inv (fst tw + 1, snd tw) \<and> dec_inv2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_dec nonneg_delay_dec], simp)
  unfolding wp3_fun.simps using one_encoding  case0 case1 case2 case3 cases dec_inv2_next_time
  by auto fastforce+

lemma nand_correctness:
  assumes "sim_fin2 w (i + 1) dec tw'" and "wityping \<Gamma> w"
  shows   "bl_to_bin (lof_wline tw' OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline tw' IN i))"
  using grand_correctness[OF assms conc_stmt_wf_dec conc_wt_dec nonneg_delay_conc_dec dec_sim init_sat_nand_inv_comb]
  unfolding dec_inv_def  by (metis (no_types, lifting) add_diff_cancel_right' assms(1)
  sim_fin2.cases world_maxtime_lt_fst_tres)

end