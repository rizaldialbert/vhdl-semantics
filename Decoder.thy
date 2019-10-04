(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Decoder
  imports VHDL_Hoare_Complete
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
    by (metis bexp_wt_cases(9))
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

abbreviation property :: "nat \<times> sig worldline_init \<Rightarrow> nat \<Rightarrow> bool" where
  "property tw i \<equiv> bl_to_bin (lof_wline tw OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline tw IN i))"

definition dec_inv :: "sig assn2" where
  "dec_inv \<equiv> \<lambda>tw. (\<forall>i < fst tw. property tw i)"

definition dec_inv2 :: "sig assn2" where
  "dec_inv2 \<equiv> \<lambda>tw. disjnt {IN} (event_of tw) \<longrightarrow>
                 (\<forall>i \<ge> fst tw.  bl_to_bin (lof_wline tw OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline tw IN (fst tw))))"

abbreviation "ntime tw \<equiv> next_time_world tw"

(*TODO: Move! *)
lemma invariant_cases_3:
  assumes "\<And>i. i < fst tw \<Longrightarrow> P i"
  assumes "\<And>i. fst tw \<le> i \<and> i < next_time_world tw - dly \<Longrightarrow> P i"
  assumes "\<And>i. next_time_world tw - dly \<le> i \<and> i < next_time_world tw \<Longrightarrow> P i"
  shows "\<forall>i. i < next_time_world tw \<longrightarrow> P i"
  using assms not_le_imp_less by blast

lemma invariant_cases_2:
  assumes "\<And>i. i < fst tw \<Longrightarrow> P i"
  assumes "\<And>i. fst tw \<le> i \<and> i < next_time_world tw  \<Longrightarrow> P i"
  shows "\<forall>i. i < next_time_world tw \<longrightarrow> P i"
  using assms not_le_imp_less by blast

lemma curr_time_does_not_change:
  fixes tw sig dly v
  defines "tw' \<equiv> tw [sig , dly :=\<^sub>2 v]"
  shows   "fst tw' = fst tw"
  using assms  by (simp add: worldline_upd2_def)

lemma wline_before_ntime_unchange:
  fixes tw sig dly v
  defines "tw' \<equiv> tw [sig , dly :=\<^sub>2 v]"
  shows "\<forall>i < fst tw'. wline_of tw' sig' i = wline_of tw sig' i"
  using assms by (metis curr_time_does_not_change trans_less_add1 worldline_upd2_before_dly)

lemma wline_before_ntime_unchange':
  fixes tw sig dly v
  defines "tw' \<equiv> tw [sig , dly :=\<^sub>2 v]"
  assumes "0 < dly"
  shows "\<forall>i \<le> fst tw'. wline_of tw' sig' i = wline_of tw sig' i"
  using assms  by (metis curr_time_does_not_change less_add_same_cancel1 order.not_eq_order_implies_strict
  wline_before_ntime_unchange worldline_upd2_before_dly)

lemma value_at_next_time_is_suc_time:
  fixes tw sig dly v
  defines "tw' \<equiv> tw [sig, 1 :=\<^sub>2 v]"
  shows   "wline_of tw' sig (ntime tw') = wline_of tw' sig (fst tw' + 1)"
  using assms
  by (smt Suc_eq_plus1 comp_def curr_time_does_not_change le_Suc_eq less_imp_le_nat
      next_time_world_at_least not_less snd_conv worldline_upd2_def worldline_upd_def)

lemma case0:
  assumes "dec_inv tw"
  assumes "beval_world_raw2 tw (Bsig IN) x" and "beval_world_raw2 tw (Bliteral Neu (to_bl (0 :: 2 word))) x"
  assumes "beval_world_raw2 tw (Bliteral Neu (to_bl (1 :: 4 word))) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "dec_inv (next_time_world tw', snd tw')"
proof -
  have "beval_world_raw (snd tw) (fst tw) (Bsig IN) x" and "beval_world_raw (snd tw) (fst tw) (Bliteral Neu (to_bl (0 :: 2 word))) x"
    using assms unfolding beval_world_raw2_def by auto
  hence "x = Lv Neu (to_bl (0 :: 2 word))"
    by auto
  have v_def: "v = Lv Neu (to_bl (1 :: 4 word))"
    using assms(4) unfolding beval_world_raw2_def by auto
  have "\<forall>i<ntime tw'. bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
  proof (rule invariant_cases_2[where P="\<lambda>i. bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"])
    fix i
    assume "i < fst tw'"
    hence  "i < fst tw"
      unfolding tw'_def curr_time_does_not_change by auto
    have "2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i)) =
          2 ^ nat (bl_to_bin (lof_wline (ntime tw , snd tw ) IN i))"
      by (metis \<open>i < get_time tw'\<close> comp_apply sndI tw'_def wline_before_ntime_unchange)
    moreover have "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) =
                   bl_to_bin (lof_wline (ntime tw , snd tw ) OUT (i + 1))"
      by (metis \<open>i < get_time tw'\<close> comp_apply discrete sndI tw'_def wline_before_ntime_unchange'
      zero_less_one)
    ultimately show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
      using assms(1) unfolding dec_inv_def by (smt \<open>i < get_time tw\<close> comp_apply snd_conv)
  next
    fix i
    assume "fst tw' \<le> i \<and> i < ntime tw'"
    hence "fst tw' \<le> i" and "i < ntime tw'"
      by auto
    have "i + 1 < ntime tw' \<or> i + 1 = ntime tw'"
      using \<open>get_time tw' \<le> i \<and> i < ntime tw'\<close> by linarith
    moreover
    { assume "i + 1 < ntime tw'"
      hence "lof_wline (ntime tw', snd tw') OUT (i + 1) =
             lof_wline (ntime tw', snd tw') OUT (fst tw' + 1)"
        using unchanged_until_next_time_world  \<open>fst tw' \<le> i\<close>
        by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by (simp add: tw'_def worldline_upd2_def)
      finally have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by auto }
    moreover
    { assume "i + 1 = ntime tw'"
      hence "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (ntime tw')"
        by auto
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw' + 1)"
        by (metis comp_def snd_conv value_at_next_time_is_suc_time tw'_def)
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by (simp add: tw'_def worldline_upd2_def)
      finally have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by auto }
    ultimately have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
      by auto
    also have "... = lval_of v"
      by (metis comp_def snd_conv tw'_def worldline_upd2_at_dly)
    also have "... = to_bl (1 :: 4 word)"
      using v_def by auto
    finally have "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 1"
      by auto

    have "lof_wline (ntime tw', snd tw') IN i = lof_wline (ntime tw', snd tw') IN (fst tw')"
      using unchanged_until_next_time_world
      by (metis \<open>get_time tw' \<le> i \<and> i < ntime tw'\<close> comp_apply snd_conv)
    also have "... = lof_wline (ntime tw', snd tw') IN (fst tw)"
      by (simp add: tw'_def worldline_upd2_def)
    also have "... = lof_wline tw IN (fst tw)"
      by (metis comp_apply less_add_one snd_conv tw'_def worldline_upd2_before_dly)
    also have "... = to_bl (0 :: 2 word)"
      by (metis \<open>beval_world_raw (snd tw) (get_time tw) (Bsig IN) x\<close> \<open>x = Lv Neu (to_bl 0)\<close>
      beval_cases(1) beval_world_raw_cases comp_apply state_of_world_def val.sel(3))
    finally have "bl_to_bin (lof_wline (ntime tw', snd tw') IN i) = 0"
      by auto
    show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
      using \<open>bl_to_bin (lof_wline (ntime tw', snd tw') IN i) = 0\<close> \<open>bl_to_bin (lof_wline (ntime tw',
      snd tw') OUT (i + 1)) = 1\<close> by auto
  qed
  thus ?thesis
    unfolding dec_inv_def by auto
qed

lemma case1:
  assumes "dec_inv tw"
  assumes "beval_world_raw2 tw (Bsig IN) x" and "beval_world_raw2 tw (Bliteral Neu (to_bl (1 :: 2 word))) x"
  assumes "beval_world_raw2 tw (Bliteral Neu (to_bl (2 :: 4 word))) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "dec_inv (next_time_world tw', snd tw')"
proof -
  have "beval_world_raw (snd tw) (fst tw) (Bsig IN) x" and "beval_world_raw (snd tw) (fst tw) (Bliteral Neu (to_bl (1 :: 2 word))) x"
    using assms unfolding beval_world_raw2_def by auto
  hence "x = Lv Neu (to_bl (1 :: 2 word))"
    by auto
  have v_def: "v = Lv Neu (to_bl (2 :: 4 word))"
    using assms(4) unfolding beval_world_raw2_def by auto
  have "\<forall>i<ntime tw'. bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
  proof (rule invariant_cases_2[where P="\<lambda>i. bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"])
    fix i
    assume "i < fst tw'"
    hence  "i < fst tw"
      unfolding tw'_def curr_time_does_not_change by auto
    have "2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i)) =
          2 ^ nat (bl_to_bin (lof_wline (ntime tw , snd tw ) IN i))"
      by (metis \<open>i < get_time tw'\<close> comp_apply sndI tw'_def wline_before_ntime_unchange)
    moreover have "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) =
                   bl_to_bin (lof_wline (ntime tw , snd tw ) OUT (i + 1))"
      by (metis \<open>i < get_time tw'\<close> comp_apply discrete sndI tw'_def wline_before_ntime_unchange'
      zero_less_one)
    ultimately show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
      using assms(1) unfolding dec_inv_def by (smt \<open>i < get_time tw\<close> comp_apply snd_conv)
  next
    fix i
    assume "fst tw' \<le> i \<and> i < ntime tw'"
    hence "fst tw' \<le> i" and "i < ntime tw'"
      by auto
    have "i + 1 < ntime tw' \<or> i + 1 = ntime tw'"
      using \<open>get_time tw' \<le> i \<and> i < ntime tw'\<close> by linarith
    moreover
    { assume "i + 1 < ntime tw'"
      hence "lof_wline (ntime tw', snd tw') OUT (i + 1) =
             lof_wline (ntime tw', snd tw') OUT (fst tw' + 1)"
        using unchanged_until_next_time_world  \<open>fst tw' \<le> i\<close>
        by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by (simp add: tw'_def worldline_upd2_def)
      finally have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by auto }
    moreover
    { assume "i + 1 = ntime tw'"
      hence "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (ntime tw')"
        by auto
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw' + 1)"
        by (metis comp_def snd_conv value_at_next_time_is_suc_time tw'_def)
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by (simp add: tw'_def worldline_upd2_def)
      finally have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by auto }
    ultimately have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
      by auto
    also have "... = lval_of v"
      by (metis comp_def snd_conv tw'_def worldline_upd2_at_dly)
    also have "... = to_bl (2 :: 4 word)"
      using v_def by auto
    finally have "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2"
      by auto eval

    have "lof_wline (ntime tw', snd tw') IN i = lof_wline (ntime tw', snd tw') IN (fst tw')"
      using unchanged_until_next_time_world
      by (metis \<open>get_time tw' \<le> i \<and> i < ntime tw'\<close> comp_apply snd_conv)
    also have "... = lof_wline (ntime tw', snd tw') IN (fst tw)"
      by (simp add: tw'_def worldline_upd2_def)
    also have "... = lof_wline tw IN (fst tw)"
      by (metis comp_apply less_add_one snd_conv tw'_def worldline_upd2_before_dly)
    also have "... = to_bl (1 :: 2 word)"
      by (metis \<open>beval_world_raw (snd tw) (get_time tw) (Bsig IN) x\<close> \<open>x = Lv Neu (to_bl 1)\<close>
      beval_cases(1) beval_world_raw_cases comp_apply state_of_world_def val.sel(3))
    finally have "bl_to_bin (lof_wline (ntime tw', snd tw') IN i) = 1"
      by auto
    show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
      using \<open>bl_to_bin (lof_wline (ntime tw', snd tw') IN i) = 1\<close> \<open>bl_to_bin (lof_wline (ntime tw',
      snd tw') OUT (i + 1)) = 2\<close> by auto
  qed
  thus ?thesis
    unfolding dec_inv_def by auto
qed

lemma case2:
  assumes "dec_inv tw"
  assumes "beval_world_raw2 tw (Bsig IN) x" and "beval_world_raw2 tw (Bliteral Neu (to_bl (2 :: 2 word))) x"
  assumes "beval_world_raw2 tw (Bliteral Neu (to_bl (4 :: 4 word))) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "dec_inv (next_time_world tw', snd tw')"
proof -
  have "beval_world_raw (snd tw) (fst tw) (Bsig IN) x" and "beval_world_raw (snd tw) (fst tw) (Bliteral Neu (to_bl (2 :: 2 word))) x"
    using assms unfolding beval_world_raw2_def by auto
  hence "x = Lv Neu (to_bl (2 :: 2 word))"
    by auto
  have v_def: "v = Lv Neu (to_bl (4 :: 4 word))"
    using assms(4) unfolding beval_world_raw2_def by auto
  have "\<forall>i<ntime tw'. bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
  proof (rule invariant_cases_2[where P="\<lambda>i. bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"])
    fix i
    assume "i < fst tw'"
    hence  "i < fst tw"
      unfolding tw'_def curr_time_does_not_change by auto
    have "2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i)) =
          2 ^ nat (bl_to_bin (lof_wline (ntime tw , snd tw ) IN i))"
      by (metis \<open>i < get_time tw'\<close> comp_apply sndI tw'_def wline_before_ntime_unchange)
    moreover have "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) =
                   bl_to_bin (lof_wline (ntime tw , snd tw ) OUT (i + 1))"
      by (metis \<open>i < get_time tw'\<close> comp_apply discrete sndI tw'_def wline_before_ntime_unchange'
      zero_less_one)
    ultimately show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
      using assms(1) unfolding dec_inv_def by (smt \<open>i < get_time tw\<close> comp_apply snd_conv)
  next
    fix i
    assume "fst tw' \<le> i \<and> i < ntime tw'"
    hence "fst tw' \<le> i" and "i < ntime tw'"
      by auto
    have "i + 1 < ntime tw' \<or> i + 1 = ntime tw'"
      using \<open>get_time tw' \<le> i \<and> i < ntime tw'\<close> by linarith
    moreover
    { assume "i + 1 < ntime tw'"
      hence "lof_wline (ntime tw', snd tw') OUT (i + 1) =
             lof_wline (ntime tw', snd tw') OUT (fst tw' + 1)"
        using unchanged_until_next_time_world  \<open>fst tw' \<le> i\<close>
        by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by (simp add: tw'_def worldline_upd2_def)
      finally have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by auto }
    moreover
    { assume "i + 1 = ntime tw'"
      hence "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (ntime tw')"
        by auto
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw' + 1)"
        by (metis comp_def snd_conv value_at_next_time_is_suc_time tw'_def)
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by (simp add: tw'_def worldline_upd2_def)
      finally have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by auto }
    ultimately have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
      by auto
    also have "... = lval_of v"
      by (metis comp_def snd_conv tw'_def worldline_upd2_at_dly)
    also have "... = to_bl (4 :: 4 word)"
      using v_def by auto
    finally have "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 4"
      by auto eval

    have "lof_wline (ntime tw', snd tw') IN i = lof_wline (ntime tw', snd tw') IN (fst tw')"
      using unchanged_until_next_time_world
      by (metis \<open>get_time tw' \<le> i \<and> i < ntime tw'\<close> comp_apply snd_conv)
    also have "... = lof_wline (ntime tw', snd tw') IN (fst tw)"
      by (simp add: tw'_def worldline_upd2_def)
    also have "... = lof_wline tw IN (fst tw)"
      by (metis comp_apply less_add_one snd_conv tw'_def worldline_upd2_before_dly)
    also have "... = to_bl (2 :: 2 word)"
      by (metis \<open>beval_world_raw (snd tw) (get_time tw) (Bsig IN) x\<close> \<open>x = Lv Neu (to_bl 2)\<close>
      beval_cases(1) beval_world_raw_cases comp_apply state_of_world_def val.sel(3))
    finally have "bl_to_bin (lof_wline (ntime tw', snd tw') IN i) = 2"
      by auto eval
    show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
      using \<open>bl_to_bin (lof_wline (ntime tw', snd tw') IN i) = 2\<close> \<open>bl_to_bin (lof_wline (ntime tw',
      snd tw') OUT (i + 1)) = 4\<close> by auto
  qed
  thus ?thesis
    unfolding dec_inv_def by auto
qed

lemma case3:
  assumes "dec_inv tw"
  assumes "beval_world_raw2 tw (Bsig IN) x" and "beval_world_raw2 tw (Bliteral Neu (to_bl (3 :: 2 word))) x"
  assumes "beval_world_raw2 tw (Bliteral Neu (to_bl (8 :: 4 word))) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "dec_inv (next_time_world tw', snd tw')"
proof -
  have "beval_world_raw (snd tw) (fst tw) (Bsig IN) x" and "beval_world_raw (snd tw) (fst tw) (Bliteral Neu (to_bl (3 :: 2 word))) x"
    using assms unfolding beval_world_raw2_def by auto
  hence "x = Lv Neu (to_bl (3 :: 2 word))"
    by auto
  have v_def: "v = Lv Neu (to_bl (8 :: 4 word))"
    using assms(4) unfolding beval_world_raw2_def by auto
  have "\<forall>i<ntime tw'. bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
  proof (rule invariant_cases_2[where P="\<lambda>i. bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"])
    fix i
    assume "i < fst tw'"
    hence  "i < fst tw"
      unfolding tw'_def curr_time_does_not_change by auto
    have "2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i)) =
          2 ^ nat (bl_to_bin (lof_wline (ntime tw , snd tw ) IN i))"
      by (metis \<open>i < get_time tw'\<close> comp_apply sndI tw'_def wline_before_ntime_unchange)
    moreover have "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) =
                   bl_to_bin (lof_wline (ntime tw , snd tw ) OUT (i + 1))"
      by (metis \<open>i < get_time tw'\<close> comp_apply discrete sndI tw'_def wline_before_ntime_unchange'
      zero_less_one)
    ultimately show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
      using assms(1) unfolding dec_inv_def by (smt \<open>i < get_time tw\<close> comp_apply snd_conv)
  next
    fix i
    assume "fst tw' \<le> i \<and> i < ntime tw'"
    hence "fst tw' \<le> i" and "i < ntime tw'"
      by auto
    have "i + 1 < ntime tw' \<or> i + 1 = ntime tw'"
      using \<open>get_time tw' \<le> i \<and> i < ntime tw'\<close> by linarith
    moreover
    { assume "i + 1 < ntime tw'"
      hence "lof_wline (ntime tw', snd tw') OUT (i + 1) =
             lof_wline (ntime tw', snd tw') OUT (fst tw' + 1)"
        using unchanged_until_next_time_world  \<open>fst tw' \<le> i\<close>
        by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by (simp add: tw'_def worldline_upd2_def)
      finally have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by auto }
    moreover
    { assume "i + 1 = ntime tw'"
      hence "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (ntime tw')"
        by auto
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw' + 1)"
        by (metis comp_def snd_conv value_at_next_time_is_suc_time tw'_def)
      also have "... = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by (simp add: tw'_def worldline_upd2_def)
      finally have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
        by auto }
    ultimately have "lof_wline (ntime tw', snd tw') OUT (i + 1) = lof_wline (ntime tw', snd tw') OUT (fst tw + 1)"
      by auto
    also have "... = lval_of v"
      by (metis comp_def snd_conv tw'_def worldline_upd2_at_dly)
    also have "... = to_bl (8 :: 4 word)"
      using v_def by auto
    finally have "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 8"
      by auto eval

    have "lof_wline (ntime tw', snd tw') IN i = lof_wline (ntime tw', snd tw') IN (fst tw')"
      using unchanged_until_next_time_world
      by (metis \<open>get_time tw' \<le> i \<and> i < ntime tw'\<close> comp_apply snd_conv)
    also have "... = lof_wline (ntime tw', snd tw') IN (fst tw)"
      by (simp add: tw'_def worldline_upd2_def)
    also have "... = lof_wline tw IN (fst tw)"
      by (metis comp_apply less_add_one snd_conv tw'_def worldline_upd2_before_dly)
    also have "... = to_bl (3 :: 2 word)"
      by (metis \<open>beval_world_raw (snd tw) (get_time tw) (Bsig IN) x\<close> \<open>x = Lv Neu (to_bl 3)\<close>
      beval_cases(1) beval_world_raw_cases comp_apply state_of_world_def val.sel(3))
    finally have "bl_to_bin (lof_wline (ntime tw', snd tw') IN i) = 3"
      by auto eval
    show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN i))"
      using \<open>bl_to_bin (lof_wline (ntime tw', snd tw') IN i) = 3\<close> \<open>bl_to_bin (lof_wline (ntime tw',
      snd tw') OUT (i + 1)) = 8\<close> by auto
  qed
  thus ?thesis
    unfolding dec_inv_def by auto
qed

lemma case_exhaustive:
  assumes "wityping \<Gamma> (snd tw)"
  assumes "\<Gamma> IN = Lty Neu 2"
  assumes "beval_world_raw2 tw (Bsig IN) x"
  shows   "x = Lv Neu [False, False] \<or> x = Lv Neu [False, True]  \<or> x = Lv Neu [True, False] \<or> x = Lv Neu [True, True]"
proof -
  have "beval_world_raw (snd tw) (fst tw) (Bsig IN) x"
    using assms(3) unfolding beval_world_raw2_def by auto
  have "type_of x = Lty Neu 2"
    by (metis (no_types, hide_lams) assms(1) assms(2) assms(3) beval_cases(1) beval_world_raw2_def
    beval_world_raw_cases state_of_world_def wityping_def wtyping_def)
  obtain xs where "x = Lv Neu xs" and "length xs = 2"
    by (metis \<open>type_of x = Lty Neu 2\<close> ty.distinct(1) ty.inject type_of.elims)
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
    by (simp add: \<open>x = Lv Neu xs\<close>)
qed

lemma dead_code:
  assumes "wityping \<Gamma> (snd tw) "
  assumes "\<Gamma> IN = Lty Neu 2"
  assumes "x \<noteq> x' "
  assumes "beval_world_raw2 tw (Bsig IN) x "
  assumes "beval_world_raw2 tw (Bliteral Neu [False, False]) x' "
  assumes "xa \<noteq> x'a "
  assumes "beval_world_raw2 tw (Bsig IN) xa "
  assumes "beval_world_raw2 tw (Bliteral Neu [False, True]) x'a "
  assumes "xb \<noteq> x'b "
  assumes "beval_world_raw2 tw (Bsig IN) xb "
  assumes "beval_world_raw2 tw (Bliteral Neu [True, False]) x'b "
  assumes "xc \<noteq> x'c "
  assumes "beval_world_raw2 tw (Bsig IN) xc "
  assumes "beval_world_raw2 tw (Bliteral Neu [True, True]) x'c"
  shows   "False"
  using case_exhaustive[OF assms(1-2)] assms beval_world_raw2_deterministic
  by (metis beval_cases(21) beval_world_raw2_def beval_world_raw_cases)

lemma one_encoding:
  "to_bl (1 :: 2 word) = [False, True]"
  by eval

theorem dec_inv_preserved_seq:
  assumes "seq_wt \<Gamma> (Bcase (Bsig IN) dec_list)"
  shows "\<turnstile> [\<lambda>tw. dec_inv tw \<and> wityping \<Gamma> (snd tw)]  Bcase (Bsig IN) dec_list [\<lambda>tw. dec_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. dec_inv (next_time_world tw, snd tw)", rotated])
  apply (rule wp_is_pre, simp, simp)
  unfolding wp_bcase_explicit wp_bcase_empty One_nat_def wp_trans[OF lessI]
  using case0 case1 case2 case3 dead_code potential_tyenv[OF assms] one_encoding
  by fastforce

lemma dec_inv_preserved_seq0:
  assumes "seq_wt \<Gamma> (Bcase (Bsig IN) dec_list)"
  shows   " \<turnstile> [\<lambda>tw. get_time tw = 0 \<and> wityping \<Gamma> (snd tw)] Bcase (Bsig IN) dec_list [\<lambda>tw. dec_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
  apply (rule Conseq2[where P="\<lambda>tw. dec_inv tw \<and> wityping \<Gamma> (snd tw)" and Q="\<lambda>tw. dec_inv (next_time_world tw, snd tw)"])
  using dec_inv_preserved_seq[OF assms] apply (simp add: dec_inv_def)
  apply (rule dec_inv_preserved_seq[OF assms])
   apply blast
  apply (rule strengthen_precondition2)
  apply (rule seq_stmt_preserve_wityping_hoare[OF assms])
  done

lemma case0_inv2:
  assumes "beval_world_raw2 tw (Bsig IN) x" and "beval_world_raw2 tw (Bliteral Neu (to_bl (0 :: 2 word))) x"
  assumes "beval_world_raw2 tw (Bliteral Neu (to_bl (1 :: 4 word))) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "dec_inv2 (next_time_world tw', snd tw')"
  unfolding dec_inv2_def
proof (rule)+
  fix i
  assume dis: "disjnt {IN} (event_of (ntime tw', snd tw'))"
  assume "fst (ntime tw', snd tw') \<le> i"
  hence "ntime tw' \<le> i"
    by auto
  have "fst tw < ntime tw'"
    by (metis curr_time_does_not_change next_time_world_at_least tw'_def)
  hence "0 < fst (ntime tw', snd tw')"
    by auto
  have "wline_of tw' IN (ntime tw') = wline_of tw' IN (ntime tw' - 1)"
    using dis using event_of_alt_def1[OF \<open>0 < fst (ntime tw', snd tw')\<close>] by auto
  also have "... = wline_of tw' IN (fst tw')"
    by (metis (mono_tags, hide_lams) Suc_eq_plus1 Suc_leI \<open>0 < get_time (ntime tw', snd tw')\<close>
    add_le_imp_le_diff diff_less fst_conv less_one next_time_world_at_least
    unchanged_until_next_time_world)
  also have "... = wline_of tw' IN (fst tw)"
    by (simp add: curr_time_does_not_change tw'_def)
  also have "... = wline_of tw IN (fst tw)"
    by (metis less_add_one tw'_def worldline_upd2_before_dly)
  also have "... = x"
    using assms(2) unfolding beval_world_raw2_def
    by (meson assms(1) beval_world_raw2_Bsig beval_world_raw2_deterministic)
  also have "... = Lv Neu (to_bl (0 :: 2 word))"
    using assms(2) unfolding beval_world_raw2_def by blast
  finally have 0: "bl_to_bin (lof_wline (ntime tw', snd tw') IN (get_time (ntime tw', snd tw'))) = 0"
    by auto

  have "wline_of tw' OUT (i + 1) = v"
    using `fst tw < ntime tw'`
    unfolding tw'_def worldline_upd2_def worldline_upd_def
    using \<open>get_time (ntime tw', snd tw') \<le> i\<close> \<open>get_time tw < ntime tw'\<close> by auto
  also have "... = Lv Neu (to_bl (1 :: 4 word))"
    using assms(3) unfolding beval_world_raw2_def by blast
  finally have 1: "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 1"
    by auto

  show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) =
        2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN (get_time (ntime tw', snd tw'))))"
    using "0" "1" by auto
qed

lemma case1_inv2:
  assumes "beval_world_raw2 tw (Bsig IN) x" and "beval_world_raw2 tw (Bliteral Neu (to_bl (1 :: 2 word))) x"
  assumes "beval_world_raw2 tw (Bliteral Neu (to_bl (2 :: 4 word))) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "dec_inv2 (next_time_world tw', snd tw')"
  unfolding dec_inv2_def
proof (rule)+
  fix i
  assume dis: "disjnt {IN} (event_of (ntime tw', snd tw'))"
  assume "fst (ntime tw', snd tw') \<le> i"
  hence "ntime tw' \<le> i"
    by auto
  have "fst tw < ntime tw'"
    by (metis curr_time_does_not_change next_time_world_at_least tw'_def)
  hence "0 < fst (ntime tw', snd tw')"
    by auto
  have "wline_of tw' IN (ntime tw') = wline_of tw' IN (ntime tw' - 1)"
    using dis using event_of_alt_def1[OF \<open>0 < fst (ntime tw', snd tw')\<close>] by auto
  also have "... = wline_of tw' IN (fst tw')"
    by (metis (mono_tags, hide_lams) Suc_eq_plus1 Suc_leI \<open>0 < get_time (ntime tw', snd tw')\<close>
    add_le_imp_le_diff diff_less fst_conv less_one next_time_world_at_least
    unchanged_until_next_time_world)
  also have "... = wline_of tw' IN (fst tw)"
    by (simp add: curr_time_does_not_change tw'_def)
  also have "... = wline_of tw IN (fst tw)"
    by (metis less_add_one tw'_def worldline_upd2_before_dly)
  also have "... = x"
    using assms(2) unfolding beval_world_raw2_def
    by (meson assms(1) beval_world_raw2_Bsig beval_world_raw2_deterministic)
  also have "... = Lv Neu (to_bl (1 :: 2 word))"
    using assms(2) unfolding beval_world_raw2_def by blast
  finally have 0: "bl_to_bin (lof_wline (ntime tw', snd tw') IN (get_time (ntime tw', snd tw'))) = 1"
    by auto

  have "wline_of tw' OUT (i + 1) = v"
    using `fst tw < ntime tw'`
    unfolding tw'_def worldline_upd2_def worldline_upd_def
    using \<open>get_time (ntime tw', snd tw') \<le> i\<close> \<open>get_time tw < ntime tw'\<close> by auto
  also have "... = Lv Neu (to_bl (2 :: 4 word))"
    using assms(3) unfolding beval_world_raw2_def by blast
  finally have 1: "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 2"
    by auto eval

  show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) =
        2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN (get_time (ntime tw', snd tw'))))"
    using "0" "1" by auto
qed

lemma case2_inv2:
  assumes "beval_world_raw2 tw (Bsig IN) x" and "beval_world_raw2 tw (Bliteral Neu (to_bl (2 :: 2 word))) x"
  assumes "beval_world_raw2 tw (Bliteral Neu (to_bl (4 :: 4 word))) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "dec_inv2 (next_time_world tw', snd tw')"
  unfolding dec_inv2_def
proof (rule)+
  fix i
  assume dis: "disjnt {IN} (event_of (ntime tw', snd tw'))"
  assume "fst (ntime tw', snd tw') \<le> i"
  hence "ntime tw' \<le> i"
    by auto
  have "fst tw < ntime tw'"
    by (metis curr_time_does_not_change next_time_world_at_least tw'_def)
  hence "0 < fst (ntime tw', snd tw')"
    by auto
  have "wline_of tw' IN (ntime tw') = wline_of tw' IN (ntime tw' - 1)"
    using dis using event_of_alt_def1[OF \<open>0 < fst (ntime tw', snd tw')\<close>] by auto
  also have "... = wline_of tw' IN (fst tw')"
    by (metis (mono_tags, hide_lams) Suc_eq_plus1 Suc_leI \<open>0 < get_time (ntime tw', snd tw')\<close>
    add_le_imp_le_diff diff_less fst_conv less_one next_time_world_at_least
    unchanged_until_next_time_world)
  also have "... = wline_of tw' IN (fst tw)"
    by (simp add: curr_time_does_not_change tw'_def)
  also have "... = wline_of tw IN (fst tw)"
    by (metis less_add_one tw'_def worldline_upd2_before_dly)
  also have "... = x"
    using assms(2) unfolding beval_world_raw2_def
    by (meson assms(1) beval_world_raw2_Bsig beval_world_raw2_deterministic)
  also have "... = Lv Neu (to_bl (2 :: 2 word))"
    using assms(2) unfolding beval_world_raw2_def by blast
  finally have 0: "bl_to_bin (lof_wline (ntime tw', snd tw') IN (get_time (ntime tw', snd tw'))) = 2"
    by auto eval

  have "wline_of tw' OUT (i + 1) = v"
    using `fst tw < ntime tw'`
    unfolding tw'_def worldline_upd2_def worldline_upd_def
    using \<open>get_time (ntime tw', snd tw') \<le> i\<close> \<open>get_time tw < ntime tw'\<close> by auto
  also have "... = Lv Neu (to_bl (4 :: 4 word))"
    using assms(3) unfolding beval_world_raw2_def by blast
  finally have 1: "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 4"
    by auto eval

  show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) =
        2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN (get_time (ntime tw', snd tw'))))"
    using "0" "1" by auto
qed

lemma case3_inv2:
  assumes "beval_world_raw2 tw (Bsig IN) x" and "beval_world_raw2 tw (Bliteral Neu (to_bl (3 :: 2 word))) x"
  assumes "beval_world_raw2 tw (Bliteral Neu (to_bl (8 :: 4 word))) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "dec_inv2 (next_time_world tw', snd tw')"
  unfolding dec_inv2_def
proof (rule)+
  fix i
  assume dis: "disjnt {IN} (event_of (ntime tw', snd tw'))"
  assume "fst (ntime tw', snd tw') \<le> i"
  hence "ntime tw' \<le> i"
    by auto
  have "fst tw < ntime tw'"
    by (metis curr_time_does_not_change next_time_world_at_least tw'_def)
  hence "0 < fst (ntime tw', snd tw')"
    by auto
  have "wline_of tw' IN (ntime tw') = wline_of tw' IN (ntime tw' - 1)"
    using dis using event_of_alt_def1[OF \<open>0 < fst (ntime tw', snd tw')\<close>] by auto
  also have "... = wline_of tw' IN (fst tw')"
    by (metis (mono_tags, hide_lams) Suc_eq_plus1 Suc_leI \<open>0 < get_time (ntime tw', snd tw')\<close>
    add_le_imp_le_diff diff_less fst_conv less_one next_time_world_at_least
    unchanged_until_next_time_world)
  also have "... = wline_of tw' IN (fst tw)"
    by (simp add: curr_time_does_not_change tw'_def)
  also have "... = wline_of tw IN (fst tw)"
    by (metis less_add_one tw'_def worldline_upd2_before_dly)
  also have "... = x"
    using assms(2) unfolding beval_world_raw2_def
    by (meson assms(1) beval_world_raw2_Bsig beval_world_raw2_deterministic)
  also have "... = Lv Neu (to_bl (3 :: 2 word))"
    using assms(2) unfolding beval_world_raw2_def by blast
  finally have 0: "bl_to_bin (lof_wline (ntime tw', snd tw') IN (get_time (ntime tw', snd tw'))) = 3"
    by auto eval

  have "wline_of tw' OUT (i + 1) = v"
    using `fst tw < ntime tw'`
    unfolding tw'_def worldline_upd2_def worldline_upd_def
    using \<open>get_time (ntime tw', snd tw') \<le> i\<close> \<open>get_time tw < ntime tw'\<close> by auto
  also have "... = Lv Neu (to_bl (8 :: 4 word))"
    using assms(3) unfolding beval_world_raw2_def by blast
  finally have 1: "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) = 8"
    by auto eval

  show "bl_to_bin (lof_wline (ntime tw', snd tw') OUT (i + 1)) =
        2 ^ nat (bl_to_bin (lof_wline (ntime tw', snd tw') IN (get_time (ntime tw', snd tw'))))"
    using "0" "1" by auto
qed

theorem dec_inv2_preserved_seq:
  assumes "seq_wt \<Gamma> (Bcase (Bsig IN) dec_list)"
  shows "\<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] Bcase (Bsig IN) dec_list [\<lambda>tw. dec_inv2 (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. dec_inv2 (next_time_world tw, snd tw)", rotated])
  apply (rule wp_is_pre, simp, simp)
  unfolding wp_bcase_explicit wp_bcase_empty One_nat_def wp_trans[OF lessI] if_split
  using case0_inv2 case1_inv2 case2_inv2 case3_inv2 dead_code potential_tyenv[OF assms] one_encoding
  by fastforce

lemma dec_inv_preserved_disjnt:
  " \<forall>tw. dec_inv tw \<and> dec_inv2 tw \<and> disjnt {IN} (event_of tw) \<longrightarrow> dec_inv (ntime tw, snd tw)"
proof (rule)+
  fix tw
  assume "dec_inv tw \<and> dec_inv2 tw \<and> disjnt {IN} (event_of tw)"
  hence "dec_inv tw" and "dec_inv2 tw" and "disjnt {IN} (event_of tw)"
    by auto
  { fix i
    assume "i < fst (ntime tw, snd tw)"
    hence "i < ntime tw"
      by auto
    have "fst tw < ntime tw"
      by (simp add: next_time_world_at_least)
    have "i < fst tw \<or> fst tw \<le> i"
      by auto
    moreover
    { assume "i < fst tw"
      hence "property (ntime tw, snd tw) i"
        using \<open>dec_inv tw\<close> unfolding dec_inv_def by auto }
    moreover
    { assume "fst tw \<le> i"
      have "wline_of (ntime tw, snd tw) IN i = wline_of (ntime tw, snd tw) IN (fst tw)"
        by (metis \<open>get_time tw \<le> i\<close> \<open>i < ntime tw\<close> comp_apply snd_conv unchanged_until_next_time_world)
      moreover have "bl_to_bin (lof_wline tw OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline tw IN (get_time tw)))"
        using \<open>dec_inv2 tw\<close> \<open>disjnt {IN} (event_of tw)\<close> unfolding dec_inv2_def using \<open>get_time tw \<le> i\<close>
        by blast
      ultimately have "property (ntime tw, snd tw) i"
        by simp }
    ultimately have "property (ntime tw, snd tw) i"
      by auto }
  thus "dec_inv (ntime tw, snd tw)"
    unfolding dec_inv_def by auto
qed

lemma dec_inv2_preserved_disjnt:
  "\<forall>tw. dec_inv tw \<and> dec_inv2 tw \<and> disjnt {IN} (event_of tw) \<longrightarrow> dec_inv2 (ntime tw, snd tw)"
proof (rule)+
  fix tw
  assume "dec_inv tw \<and> dec_inv2 tw \<and> disjnt {IN} (event_of tw)"
  hence "dec_inv tw" and "dec_inv2 tw" and "disjnt {IN} (event_of tw)"
    by auto
  { fix i
    assume dis: "disjnt {IN} (event_of (ntime tw, snd tw))"
    assume "i \<ge> ntime tw"
    have "fst tw < ntime tw"
      using next_time_world_at_least by blast
    hence *: "0 < fst (ntime tw, snd tw)"
      by auto
    have "wline_of tw IN (ntime tw) = wline_of tw IN (ntime tw - 1)"
      using dis unfolding event_of_alt_def1[OF *] by auto
    also have "... = wline_of tw IN (fst tw)"
      by (metis (mono_tags, lifting) Suc_diff_1 \<open>get_time tw < ntime tw\<close> diff_le_self diff_less
      dual_order.strict_implies_order dual_order.strict_trans1 le_Suc_eq not_less_iff_gr_or_eq
      unchanged_until_next_time_world zero_less_diff zero_less_one)
    finally have "wline_of tw IN (ntime tw) = wline_of tw IN (fst tw)"
      by auto

    have "bl_to_bin (lof_wline tw OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline tw IN (fst tw)))"
      using \<open>dec_inv2 tw\<close> \<open>fst tw < ntime tw\<close> \<open>ntime tw \<le> i\<close> \<open>disjnt {IN} (event_of tw)\<close>
      unfolding dec_inv2_def by auto
    hence "bl_to_bin (lof_wline tw OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline tw IN (ntime tw)))"
      using \<open>wline_of tw IN (ntime tw) = wline_of tw IN (get_time tw)\<close> by auto }
  thus "dec_inv2 (ntime tw, snd tw)"
    unfolding dec_inv2_def by auto
qed

theorem conc_hoare_next_time:
  assumes "conc_wt \<Gamma> dec"
  shows
  "\<turnstile> \<lbrace>\<lambda>tw. (dec_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> (dec_inv2 tw \<and> wityping \<Gamma> (snd tw)) \<rbrace>
        dec
     \<lbrace>\<lambda>tw. dec_inv  (next_time_world tw, snd tw)  \<and> dec_inv2  (next_time_world tw, snd tw)\<rbrace>"
  unfolding dec_def
  apply (rule Single)
   apply (rule Conj)
    apply (rule strengthen_precondition)
    apply (rule strengthen_precondition)
  using dec_inv_preserved_seq  assms unfolding dec_def apply (meson conc_wt_cases(1))
   apply (rule strengthen_precondition)
   apply (rule strengthen_precondition2)+
  using dec_inv2_preserved_seq  assms unfolding dec_def apply (meson conc_wt_cases(1))
  using dec_inv_preserved_disjnt dec_inv2_preserved_disjnt
  by auto

theorem conc_hoare_next_time':
  assumes "conc_wt \<Gamma> dec"
  shows
  "\<turnstile> \<lbrace>\<lambda>tw. (dec_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> (dec_inv2 tw \<and> wityping \<Gamma> (snd tw)) \<rbrace>
        dec
     \<lbrace>\<lambda>tw.  (dec_inv (next_time_world tw, snd tw) \<and> (wityping \<Gamma> (snd tw)))
         \<and>  (dec_inv2  (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw))\<rbrace>"
  apply (rule Conj2)
   apply (rule Conj2)
    apply (rule weaken_post_conc_hoare[rotated])
     apply (rule conc_hoare_next_time[OF assms])
    apply blast
   apply (rule strengthen_pre_conc_hoare[rotated])
  apply (unfold dec_def, rule single_conc_stmt_preserve_wityping_hoare)
  using assms  apply (metis conc_wt_cases(1) dec_def)
   apply blast
  apply (rule Conj2)
   apply (rule weaken_post_conc_hoare[rotated])
    apply (fold dec_def, rule conc_hoare_next_time[OF assms])
  apply blast
  apply (rule strengthen_pre_conc_hoare[rotated])
   apply (unfold dec_def, rule single_conc_stmt_preserve_wityping_hoare)
  using assms  apply (metis conc_wt_cases(1) dec_def)
  by blast

theorem dec_sim:
  assumes "conc_wt \<Gamma> dec"
  shows
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (dec_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> (dec_inv2 tw \<and> wityping \<Gamma> (snd tw)) \<rbrace>
        dec
      \<lbrace>\<lambda>tw. (dec_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> (dec_inv2 tw \<and> wityping \<Gamma> (snd tw))\<rbrace>"
  apply (rule While)
  unfolding snd_conv by (rule conc_hoare_next_time'[OF assms])

lemma init_sat_dec_inv:
  assumes "seq_wt \<Gamma> (Bcase (Bsig IN) dec_list)"
  shows "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) dec (\<lambda>tw. dec_inv tw \<and> wityping \<Gamma> (snd tw))"
  unfolding dec_def
  apply (rule AssignI)
  apply (rule SingleI)
  unfolding snd_conv apply(rule dec_inv_preserved_seq0[OF assms])
  done

lemma init_sat_dec_inv2:
  assumes "seq_wt \<Gamma> (Bcase (Bsig IN) dec_list)"
  shows "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) dec (\<lambda>tw. dec_inv2 tw \<and> wityping \<Gamma> (snd tw))"
  unfolding dec_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule Conj)
   apply (rule dec_inv2_preserved_seq[OF assms])
  unfolding snd_conv
  apply (rule seq_stmt_preserve_wityping_hoare[OF assms])
  done

lemma init_sat_dec_inv_comb:
  assumes "seq_wt \<Gamma> (Bcase (Bsig IN) dec_list)"
  shows "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) dec (\<lambda>tw. (dec_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> (dec_inv2 tw \<and> wityping \<Gamma> (snd tw)))"
  apply (rule ConjI_sim)
  apply (rule init_sat_dec_inv[OF assms])
  apply (rule ConseqI_sim[where P="\<lambda>tw. wityping \<Gamma> (snd tw)" and Q="\<lambda>tw. (dec_inv2 tw \<and> wityping \<Gamma> (snd tw))", rotated])
  apply (rule init_sat_dec_inv2[OF assms])
  by blast+

theorem
  assumes "sim_fin w (i + 1) dec tw'" and "wityping \<Gamma> w" and "conc_wt \<Gamma> dec"
  shows "bl_to_bin (lof_wline tw' OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline tw' IN i))"
proof -
  obtain tw where "init_sim (0, w) dec tw" and  "tw, i + 1, dec \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 < fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf dec"
    unfolding conc_stmt_wf_def dec_def by auto
  moreover have "nonneg_delay_conc dec"
    unfolding dec_def by auto
  moreover have "seq_wt \<Gamma> (Bcase (Bsig IN) dec_list)"
    using assms(3)  by (metis conc_wt_cases(1) dec_def)
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) dec (\<lambda>tw. (dec_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> (dec_inv2 tw \<and> wityping \<Gamma> (snd tw)))"
    using init_sim_hoare_soundness[OF init_sat_dec_inv_comb] by auto
  hence "(dec_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> (dec_inv2 tw \<and> wityping \<Gamma> (snd tw))"
    using \<open>init_sim (0, w) dec tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis snd_conv)
  hence "(dec_inv tw \<and> wityping \<Gamma> (snd tw))" and "(dec_inv2 tw \<and> wityping \<Gamma> (snd tw))"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (dec_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> (dec_inv2 tw \<and> wityping \<Gamma> (snd tw))\<rbrace> dec \<lbrace>\<lambda>tw. (dec_inv tw \<and> wityping \<Gamma> (snd tw))\<rbrace>"
    using conc_sim_soundness \<open>conc_stmt_wf dec\<close> \<open>nonneg_delay_conc dec\<close>
    by (metis (no_types, lifting) assms(3) dec_sim sim_hoare_valid_def)
  ultimately have "(dec_inv tw' \<and> wityping \<Gamma> (snd tw'))"
    using \<open>tw, i + 1, dec \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'. bl_to_bin (lof_wline tw' OUT (i + 1)) = 2 ^ nat (bl_to_bin (lof_wline tw' IN i))"
    unfolding dec_inv_def by auto
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed

end