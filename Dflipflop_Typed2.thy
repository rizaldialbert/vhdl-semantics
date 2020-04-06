(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Dflipflop_Typed2
  imports VHDL_Hoare_Typed
begin

text \<open>datatype for all signals\<close>

datatype sig = D | CLK | OUT

definition dflipflop :: "sig conc_stmt" where
  "dflipflop \<equiv> process {CLK} : Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull"

text \<open>The following positive edge is only defined for a scalar signal.\<close>

abbreviation is_posedge2 :: "'signal worldline_init \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow>  bool" where
  "is_posedge2 w s j \<equiv> (snd w s (j - 1) = Bv False \<and> snd w s j = Bv True)"

locale ff_typed = 
  fixes \<Gamma> :: "sig tyenv"
  assumes tyd: "\<Gamma> D = Bty" and tyclk: "\<Gamma> CLK = Bty" and tyout: "\<Gamma> OUT = Bty"
begin

definition inv :: "sig assn2" where
  "inv tw \<equiv> 1 < fst tw \<longrightarrow> wline_of tw OUT (fst tw) = (if is_posedge2 (snd tw) CLK (fst tw - 1) then wline_of tw D (fst tw - 1) else wline_of tw OUT (fst tw - 1))"

definition inv2 :: "sig assn2" where
  "inv2 tw \<equiv> disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True) \<longrightarrow> (\<forall>i > fst tw. wline_of tw OUT i = wline_of tw OUT (fst tw))"

lemma conc_stmt_wf_mult:
  "conc_stmt_wf dflipflop"
  unfolding dflipflop_def conc_stmt_wf_def by auto  

lemma nonneg_delay_conc_mult:
  "nonneg_delay_conc dflipflop"
  unfolding dflipflop_def by auto

lemma nonneg_delay_conc_mult':
  "  nonneg_delay_conc ( process {CLK} : Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull)"
  using nonneg_delay_conc_mult unfolding dflipflop_def by auto

lemma well_typed:
  "seq_wt \<Gamma> (Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull)"
  by (metis bexp_wt.intros(3) seq_wt.intros(1) seq_wt.intros(3) seq_wt.intros(4) tyclk tyd tyout)
  
lemma conc_wt_mult:
  "conc_wt \<Gamma> dflipflop"
  unfolding dflipflop_def by (meson conc_wt.intros(1) well_typed)

lemma conc_wt_mult':
  "conc_wt \<Gamma> ( process {CLK} : Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull)"
  using conc_wt_mult unfolding dflipflop_def by auto

lemma inv_next_time:
  fixes tw
  assumes "\<not> disjnt {CLK} (event_of tw)"
  defines "v \<equiv> eval_world_raw2 tw (Bsig D)"
  assumes "eval_world_raw2 tw (Bsig CLK) = Bv True"
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  assumes "wityping \<Gamma> (snd tw)"
  assumes "inv tw"
  shows   "inv (fst tw' + 1, snd tw')"
proof - 
  { assume "1 < fst tw' + 1"
    hence "0 < fst tw" 
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    have bexpIN1: "bexp_wt \<Gamma> (Bsig CLK) (Bty)" 
      using ff_typed_axioms unfolding ff_typed_def by (metis bexp_wt.intros(3))+
    have *: "wline_of tw CLK (fst tw) \<noteq> wline_of tw CLK (fst tw - 1)"
      using assms(1) `0 < fst tw` unfolding event_of_alt_def by auto
    have **: "wline_of tw CLK (fst tw) = Bv True"
      using assms(3) by auto
    have "is_posedge2 (snd tw) CLK (fst tw)"  
    proof -
      from * have neq: "wline_of tw CLK (fst tw) \<noteq> wline_of tw CLK (fst tw - 1)"
        by auto
      obtain bool where "wline_of tw CLK (fst tw - 1) = Bv bool" 
        using eval_world_raw_bv[OF bexpIN1 `wityping \<Gamma> (snd tw)`, of "fst tw - 1"] by auto
      then show ?thesis 
        using ** neq by auto
    qed
    have "wline_of tw' OUT (fst tw + 1) = v"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    also have "... = wline_of tw D (fst tw)"
      using assms(2) unfolding v_def eval_world_raw.simps eval_arith.simps  Let_def comp_def by auto
    also have "... = (if is_posedge2 (snd tw) CLK (fst tw) then wline_of tw D (fst tw) else wline_of tw OUT (fst tw))"
      using `is_posedge2 (snd tw) CLK (fst tw)` by auto
    finally have "wline_of tw' OUT (fst tw + 1) = (if is_posedge2 (snd tw) CLK (fst tw) then wline_of tw D (fst tw) else wline_of tw OUT (fst tw))"
      by auto }
  thus ?thesis
    unfolding inv_def tw'_def worldline_upd2_def worldline_upd_def  by fastforce
qed

lemma inv2_next_time:
  fixes tw v
  defines "tw' \<equiv> tw[OUT, 1 :=\<^sub>2 v]"
  shows   "inv2 (fst tw' + 1, snd tw')"
  unfolding inv2_def  tw'_def worldline_upd2_def worldline_upd_def by auto

lemma conc_hoare:
  "\<And>tw. inv tw \<and> inv2 tw \<and> (disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True)) \<Longrightarrow> inv (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "inv tw \<and> inv2 tw \<and> (disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True))"
  hence "inv tw" and "inv2 tw" and "disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True)"
    by auto
  { assume "1 < fst tw"
    have "wline_of tw OUT (fst tw + 1) = wline_of tw OUT (fst tw)"
      using `inv2 tw` `disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True)` unfolding inv2_def by auto 
    also have *: "... = (if is_posedge2 (snd tw) CLK (get_time tw - 1) then wline_of tw D (get_time tw - 1) else wline_of tw OUT (get_time tw - 1))"
      using `inv tw` `1 < fst tw` unfolding inv_def by auto 
    also have "... = (if is_posedge2 (snd tw) CLK (get_time tw) then wline_of tw D (get_time tw) else wline_of tw OUT (get_time tw))"
      using `disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True)`  unfolding event_of_alt_def   using * 
      by (smt comp_apply diff_is_0_eq' disjnt_insert1 le_numeral_extra(1) mem_Collect_eq val.inject(1))
    finally have "wline_of tw OUT (fst tw + 1) = (if is_posedge2 (snd tw) CLK (get_time tw) then wline_of tw D (get_time tw) else wline_of tw OUT (get_time tw))"
      by auto }
  thus "inv (fst tw + 1, snd tw)"
    unfolding inv_def using \<open>local.inv tw\<close> local.inv_def 
    by (smt \<open>local.inv tw \<and> inv2 tw \<and> (disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (get_time tw) \<noteq>
    Bv True)\<close> add_diff_cancel_right' comp_def disjnt_insert1 event_of_alt_def1 fst_conv inv2_def
    less_add_one mem_Collect_eq snd_conv val.inject(1) zero_less_diff)
qed

lemma conc_hoare2:
  "\<And>tw. inv2 tw \<and> (disjnt {CLK} (event_of tw) \<or> wline_of tw CLK (fst tw) \<noteq> (Bv True)) \<Longrightarrow> inv2 (fst tw + 1, snd tw)"
  unfolding inv2_def by auto

lemma conc_sim2':
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace> dflipflop \<lbrace>\<lambda>tw. inv tw \<and> inv2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> dflipflop (\<lambda>tw. inv  (fst tw + 1, snd tw) \<and> 
                                                          inv2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_mult, rule nonneg_delay_conc_mult, rule conc_wt_mult, simp)
  unfolding dflipflop_def  wp3_conc_single'[OF conc_wt_mult' nonneg_delay_conc_mult'] wp3_fun.simps  
  using inv_next_time inv2_next_time conc_hoare conc_hoare2 by auto

subsection \<open>Initialisation satisfies @{term "inv"} and @{term "inv2"}\<close>

lemma nonneg_delay:
  "nonneg_delay ( Bguarded (Bsig CLK) (Bassign_trans OUT (Bsig D) 1) Bnull)"
  using nonneg_delay_conc_mult' by auto

lemma inv_next_time0:
  assumes "fst tw = 0"
  defines "v \<equiv> eval_world_raw2 tw (Bsig D)"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "inv (fst tw' + 1, snd tw')"
  unfolding inv_def by (simp add: assms(1) tw'_def)

lemma inv2_next_time0:
  assumes "fst tw = 0"
  assumes "eval_world_raw2 tw (Bsig CLK) \<noteq> Bv True"
  assumes "\<forall>i. wline_of tw OUT i = wline_of tw OUT 0"
  shows   "inv2 (fst tw + 1, snd tw)"
  using assms unfolding inv2_def  by (metis comp_apply snd_conv)

lemma inv_next_time0'':
  assumes "fst tw = 0"
  shows   "inv (fst tw + 1, snd tw)"
  unfolding inv_def  by (simp add: assms(1))

lemma init_sat_nand_inv_comb:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0 \<and> (\<forall>i. wline_of tw OUT i = wline_of tw OUT 0)) dflipflop (\<lambda>tw. inv tw \<and> inv2 tw)"
  unfolding dflipflop_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. inv (fst tw + 1, snd tw) \<and> inv2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF well_typed nonneg_delay], simp)
  unfolding wp3_fun.simps using inv_next_time inv2_next_time inv_next_time0 inv2_next_time0 inv_next_time0''
  by auto

lemma
  assumes "sim_fin2 w (i + 2) dflipflop tw'"
  assumes "\<forall>i. wline_of (0, w) OUT i = wline_of (0, w) OUT 0"
  assumes " conc_wt \<Gamma> dflipflop" and "wityping \<Gamma> w"
  shows "wline_of tw' OUT (i + 2) = (if is_posedge2 (snd tw') CLK (i + 1) then wline_of tw' D (i + 1) else wline_of tw' OUT (i + 1))"
  using grand_correctness2[OF assms(1) assms(4) conc_stmt_wf_mult conc_wt_mult nonneg_delay_conc_mult conc_sim2' assms(2) init_sat_nand_inv_comb]
  unfolding inv_def 
  by (metis (no_types, lifting) add.assoc add_diff_cancel_right' assms(1) discrete le_add2 one_add_one sim_fin2.cases world_maxtime_lt_fst_tres)
    
end