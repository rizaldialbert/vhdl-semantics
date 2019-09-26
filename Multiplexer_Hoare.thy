(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Multiplexer_Hoare
  imports VHDL_Hoare_Complete
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

definition mux2_inv :: "sig assn2" where
  "mux2_inv \<equiv> \<lambda>tw. (\<forall>i < fst tw. wline_of tw OUT (i + 1) =
                   (if bval_of_wline tw SEL i then wline_of tw IN1 i else wline_of tw IN0 i))"

definition mux2_inv' :: "sig assn2" where
  "mux2_inv' \<equiv> (\<lambda>tw. disjnt {IN0, IN1, SEL} (event_of tw) \<longrightarrow>
                  (\<forall>i\<ge>fst tw. wline_of tw OUT (i + 1) =
                  (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw IN0 (fst tw))))"

subsection \<open>Proving that the sequential component preserves @{term "mux2_inv"}\<close>

lemma mux2_inv_next_time:
  assumes "mux2_inv tw" and "beval_world_raw2 tw (Bsig SEL) (Bv True)"
  assumes "beval_world_raw2 tw (Bsig IN1) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "mux2_inv (next_time_world tw', snd tw')"
proof -
  let ?t' = "next_time_world tw'"
  have assms2: "beval_world_raw (snd tw) (fst tw) (Bsig SEL) (Bv True)"
    using assms(2) unfolding beval_world_raw2_def by auto
  have "bval_of_wline tw SEL (fst tw)"
    by (rule beval_world_raw_cases[OF assms2], erule beval_cases)
       (metis comp_def state_of_world_def val.sel(1))
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  have 0: "bval_of_wline tw' SEL (fst tw)= bval_of_wline tw SEL (fst tw)" and 1: "wline_of tw IN1 (fst tw) = wline_of tw' IN1 (fst tw)"
   and 2: "wline_of tw IN0 (fst tw) =  wline_of tw' IN0 (fst tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by simp+
  have "\<forall>i < ?t'. wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
  proof (rule, rule)
    fix i
    assume "i < ?t'"
    have "i < fst tw \<or> fst tw \<le> i \<and> i < ?t' - 1 \<or> i = ?t' - 1"
      using next_time_world_at_least \<open>i < next_time_world tw'\<close> not_less by linarith
    moreover
    { assume "i < fst tw"
      hence "wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL i then wline_of tw IN1 i else wline_of tw IN0 i)"
        using assms(1) unfolding mux2_inv_def by auto
      moreover have "wline_of tw OUT (i + 1) = wline_of tw' OUT (i + 1)" and "wline_of tw IN1 i = wline_of tw' IN1 i" and "wline_of tw IN0 i = wline_of tw' IN0 i"
        unfolding tw'_def worldline_upd2_def worldline_upd_def  by (simp add: \<open>i < get_time tw\<close>)+
      ultimately have "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
        by (metis \<open>i < get_time tw\<close> add.right_neutral add_mono_thms_linordered_field(5) tw'_def
        worldline_upd2_before_dly zero_less_one) }
    moreover
    { assume "fst tw \<le> i \<and> i < ?t' - 1"
      hence "wline_of tw' OUT (i + 1) = wline_of tw' OUT (fst tw + 1)"
        using unchanged_until_next_time_world
        by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
        le_less_trans less_diff_conv)
      moreover have "wline_of tw' IN1 i = wline_of tw' IN1 (fst tw)" and "wline_of tw' IN0 i = wline_of tw' IN0 (fst tw)"
          and "wline_of tw' SEL i = wline_of tw' SEL (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i < next_time_world tw' - 1\<close>
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < next_time_world tw'\<close>)+
      moreover have "wline_of tw' OUT (fst tw + 1) =
                      (if bval_of_wline tw' SEL (fst tw) then wline_of tw' IN1 (fst tw) else wline_of tw' IN0 (fst tw))"
      proof -
        have "wline_of tw' OUT (fst tw + 1) = v"
          using \<open>fst tw \<le> i \<and> i < ?t' - 1\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def
          by auto
        also have "... = wline_of tw IN1 (fst tw)"
          by (rule beval_world_raw_cases[OF assms2], erule beval_cases)
             (metis assms(3) beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)
        also have " ... = (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw IN0 (fst tw))"
          using \<open>bval_of_wline tw SEL (fst tw)\<close> by auto
        \<comment> \<open>notice the change from @{term "tw"} to @{term "tw'"}\<close>
        also have "... = (if bval_of_wline tw' SEL (fst tw) then wline_of tw' IN1 (fst tw) else wline_of tw' IN0 (fst tw))"
          using 0 1 2 by auto
        thus "wline_of tw' OUT (fst tw + 1) = (if bval_of_wline tw' SEL (fst tw) then wline_of tw' IN1 (fst tw) else wline_of tw' IN0 (fst tw))"
          using \<open>bval_of_wline tw SEL (get_time tw)\<close> \<open>v = wline_of tw IN1 (get_time tw)\<close> \<open>wline_of
          tw' OUT (get_time tw + 1) = v\<close> by auto
      qed
      ultimately have "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
        by auto }
    moreover
    { assume "i = ?t' - 1"
      hence "wline_of tw' OUT (i + 1) = wline_of tw' OUT ?t'"
        using \<open>i < ?t'\<close> by auto
      also have "... = wline_of tw' OUT (fst tw + 1)"
        using \<open>fst tw < ?t'\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... = (if bval_of_wline tw' SEL (fst tw) then wline_of tw' IN1 (fst tw) else wline_of tw' IN0 (fst tw))"
      proof -
        have "wline_of tw' OUT (fst tw + 1) = wline_of tw IN1 (fst tw)"
          unfolding tw'_def
          by (rule beval_world_raw_cases[OF assms2], erule beval_cases)
             (metis assms(3) beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic worldline_upd2_at_dly)
        \<comment> \<open>notice that we use @{term "tw'"} on the else part; no point of using @{term "tw"}\<close>
        also have "... = (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw' IN0 (fst tw))"
          using \<open>bval_of_wline tw SEL (fst tw)\<close> by auto
        also have "... = (if bval_of_wline tw' SEL (fst tw) then wline_of tw' IN1 (fst tw) else wline_of tw' IN0 (fst tw))"
          using 0 1 by auto
        finally show ?thesis by auto
      qed
      also have "... = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
        by (metis (no_types, hide_lams) \<open>get_time tw = get_time tw'\<close> \<open>i < get_time tw \<Longrightarrow> wline_of tw'
        OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)\<close>
        \<open>i < next_time_world tw'\<close> calculation not_le unchanged_until_next_time_world)
      finally have "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
        by auto }
    ultimately show "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
      by auto
  qed
  thus ?thesis
    unfolding mux2_inv_def by auto
qed

lemma mux2_inv_next_time':
  assumes "mux2_inv tw" and "beval_world_raw2 tw (Bsig SEL) (Bv False)"
  assumes "beval_world_raw2 tw (Bsig IN0) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "mux2_inv (next_time_world tw', snd tw')"
proof -
  let ?t' = "next_time_world tw'"
  have assms2: "beval_world_raw (snd tw) (fst tw) (Bsig SEL) (Bv False)"
    using assms(2) unfolding beval_world_raw2_def by auto
  have "\<not> bval_of_wline tw SEL (fst tw)"
    by (rule beval_world_raw_cases[OF assms2], erule beval_cases)
       (metis comp_def state_of_world_def val.sel(1))
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  have 0: "bval_of_wline tw' SEL (fst tw)= bval_of_wline tw SEL (fst tw)" and 1: "wline_of tw IN1 (fst tw) = wline_of tw' IN1 (fst tw)"
   and 2: "wline_of tw IN0 (fst tw) = wline_of tw' IN0 (fst tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by simp+
  have "\<forall>i < ?t'. wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
  proof (rule, rule)
    fix i
    assume "i < ?t'"
    have "i < fst tw \<or> fst tw \<le> i \<and> i < ?t' - 1 \<or> i = ?t' - 1"
      using next_time_world_at_least \<open>i < next_time_world tw'\<close> not_less by linarith
    moreover
    { assume "i < fst tw"
      hence "wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL i then wline_of tw IN1 i else wline_of tw IN0 i)"
        using assms(1) unfolding mux2_inv_def by auto
      moreover have "wline_of tw OUT (i + 1) = wline_of tw' OUT (i + 1)" and "wline_of tw IN1 i = wline_of tw' IN1 i" and "wline_of tw IN0 i = wline_of tw' IN0 i"
        unfolding tw'_def worldline_upd2_def worldline_upd_def  by (simp add: \<open>i < get_time tw\<close>)+
      ultimately have "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
        by (metis \<open>i < get_time tw\<close> add.right_neutral add_mono_thms_linordered_field(5) tw'_def
        worldline_upd2_before_dly zero_less_one) }
    moreover
    { assume "fst tw \<le> i \<and> i < ?t' - 1"
      hence "wline_of tw' OUT (i + 1) = wline_of tw' OUT (fst tw + 1)"
        using unchanged_until_next_time_world
        by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
        le_less_trans less_diff_conv)
      moreover have "wline_of tw' IN1 i = wline_of tw' IN1 (fst tw)" and "wline_of tw' IN0 i = wline_of tw' IN0 (fst tw)"
          and "bval_of_wline tw' SEL i \<longleftrightarrow> bval_of_wline tw' SEL (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i < next_time_world tw' - 1\<close>
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < next_time_world tw'\<close>)+
      moreover have "wline_of tw' OUT (fst tw + 1) =
                      (if bval_of_wline tw' SEL (fst tw) then wline_of tw' IN1 (fst tw) else wline_of tw' IN0 (fst tw))"
      proof -
        have "wline_of tw' OUT (fst tw + 1) = v"
          using \<open>fst tw \<le> i \<and> i < ?t' - 1\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def
          by auto
        have " ... = wline_of tw IN0 (fst tw)"
          by (rule beval_world_raw_cases[OF assms2], erule beval_cases)
             (metis assms(3) beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)
        also have "... = (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw IN0 (fst tw))"
          using \<open>\<not> bval_of_wline tw SEL (fst tw)\<close> by auto
        \<comment> \<open>notice the change from @{term "tw"} to @{term "tw'"}\<close>
        also have "... = (if bval_of_wline tw' SEL (fst tw) then wline_of tw' IN1 (fst tw) else wline_of tw' IN0 (fst tw))"
          using 0 1 2 by auto
        finally show "wline_of tw' OUT (fst tw + 1) = (if bval_of_wline tw' SEL (fst tw) then wline_of tw' IN1 (fst tw) else wline_of tw' IN0 (fst tw))"
          using \<open>wline_of tw' OUT (get_time tw + 1) = v\<close> by blast
      qed
      ultimately have "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
        by auto }
    moreover
    { assume "i = ?t' - 1"
      hence "wline_of tw' OUT (i + 1) = wline_of tw' OUT ?t'"
        using \<open>i < ?t'\<close> by auto
      also have "... = wline_of tw' OUT (fst tw + 1)"
        using \<open>fst tw < ?t'\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... = (if bval_of_wline tw' SEL (fst tw) then wline_of tw' IN1 (fst tw) else wline_of tw' IN0 (fst tw))"
      proof -
        have "wline_of tw' OUT (fst tw + 1) = wline_of tw IN0 (fst tw)"
          by (rule beval_world_raw_cases[OF assms2], erule beval_cases)
             (metis assms(3) beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic tw'_def worldline_upd2_at_dly)
        \<comment> \<open>notice that we use @{term "tw'"} on the else part; no point of using @{term "tw"}\<close>
        have " ... = (if bval_of_wline tw SEL (fst tw) then wline_of tw' IN1 (fst tw) else wline_of tw IN0 (fst tw))"
          using \<open>\<not> bval_of_wline tw SEL (fst tw)\<close> by auto
        also have "... = (if bval_of_wline tw' SEL (fst tw) then wline_of tw' IN1 (fst tw) else wline_of tw' IN0 (fst tw))"
          using 0 2 by auto
        finally show ?thesis
          using \<open>wline_of tw' OUT (get_time tw + 1) = wline_of tw IN0 (get_time tw)\<close> by auto
      qed
      also have "... = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < get_time tw \<Longrightarrow> wline_of tw' OUT (i + 1) = (if
        bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)\<close> \<open>i <
        next_time_world tw'\<close> calculation not_le unchanged_until_next_time_world)
      finally have "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
        by auto }
    ultimately show "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
      by auto
  qed
  thus ?thesis
    unfolding mux2_inv_def by auto
qed

lemma mux2_seq_hoare_next_time_if:
  "\<turnstile> [\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> beval_world_raw2 tw (Bsig SEL) (Bv True)] Bassign_trans OUT (Bsig IN1) 1 [\<lambda>tw. mux2_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using mux2_inv_next_time by blast+

lemma mux2_seq_hoare_next_time_else:
  "\<turnstile> [\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> beval_world_raw2 tw (Bsig SEL) (Bv False)] Bassign_trans OUT (Bsig IN0) 1 [\<lambda>tw. mux2_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using mux2_inv_next_time' by blast+

theorem mux2_seq_hoare_next_time:
  "\<turnstile> [\<lambda>tw. mux2_inv tw \<and> wityping \<Gamma> (snd tw)]
        Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1)
     [\<lambda>tw. mux2_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv (next_time_world tw, snd tw)" and P = "\<lambda>tw. mux2_inv tw \<and> wityping \<Gamma> (snd tw)", rotated 1], rule If2)
     apply (rule mux2_seq_hoare_next_time_if)
    apply (rule mux2_seq_hoare_next_time_else)
  apply simp+
  done

theorem mux2_seq_hoare_next_time_wityping:
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  shows"
   \<turnstile> [\<lambda>tw. mux2_inv tw \<and> wityping \<Gamma> (snd tw)]
        Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1)
     [\<lambda>tw. mux2_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
   apply (rule mux2_seq_hoare_next_time)
  apply (rule strengthen_precondition2)
  apply (rule seq_stmt_preserve_wityping_hoare)
  apply (rule assms)
  done

theorem mux2_seq_hoare_next_time0:
  "\<turnstile> [\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)]
        Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1)
     [\<lambda>tw. mux2_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where P="\<lambda>tw. mux2_inv tw \<and> wityping \<Gamma> (snd tw)" and Q="\<lambda>tw. mux2_inv (next_time_world tw, snd tw)"])
  using mux2_seq_hoare_next_time unfolding mux2_inv_def by auto

theorem mux2_seq_hoare_next_time0_wityping:
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  shows
  "\<turnstile> [\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)]
        Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1)
     [\<lambda>tw. mux2_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
   apply (rule mux2_seq_hoare_next_time0)
  apply (rule strengthen_precondition2)
  apply (rule seq_stmt_preserve_wityping_hoare)
  apply (rule assms)
  done

subsection \<open>Proving that the sequential component preserves @{term "mux2_inv'"}\<close>

lemma input_signals_unchanged:
  fixes tw any
  assumes "beval_world_raw2 tw (Bsig any) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  defines "t' \<equiv> next_time_world tw'"
  assumes "disjnt {IN0, IN1, SEL} (event_of (t', snd tw'))"
  shows "\<And>s. s \<in> {IN0, IN1, SEL} \<Longrightarrow> wline_of tw' s t' = wline_of tw s (fst tw)"
proof -
  fix s
  assume "s \<in> {IN0, IN1, SEL}"
  have "fst tw' < t'"
    using next_time_world_at_least unfolding t'_def by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def unfolding worldline_upd2_def by auto
  ultimately have "fst tw < t'"
    by auto
  have "wline_of tw' s t' = wline_of tw s t'"
    using \<open>s \<in> {IN0, IN1, SEL}\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = wline_of tw s (t' - 1)"
    using \<open>disjnt {IN0, IN1, SEL} (event_of (t', snd tw'))\<close> \<open>fst tw < t'\<close>
    unfolding event_of_alt_def
    by (smt \<open>s \<in> {IN0, IN1, SEL}\<close> comp_apply disjnt_insert1 fst_conv gr_implies_not_zero insert_iff
    mem_Collect_eq sig.distinct(12) sig.distinct(5) sig.distinct(9) singletonD snd_conv tw'_def
    worldline_upd2_def worldline_upd_def)
  also have "... = wline_of tw s (fst tw)"
  proof -
    have "fst tw' \<le> t' - 1" and "t' - 1 < t'"
      using \<open>fst tw' < t'\<close> by auto
    hence "wline_of tw' s (t' - 1) = wline_of tw' s (fst tw')"
      using unchanged_until_next_time_world[where tw="tw'"] unfolding t'_def by blast
    moreover have "wline_of tw' s (t' - 1) = wline_of tw s (t' - 1)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def  using \<open>s \<in> {IN0, IN1, SEL}\<close> by auto
    moreover have "wline_of tw' s (fst tw') = wline_of tw s (fst tw')"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    ultimately show ?thesis
      using \<open>fst tw = fst tw'\<close> by auto
  qed
  finally show "wline_of tw' s t' = wline_of tw s (fst tw)"
    by auto
qed

lemma mux2_inv'_next_time:
  assumes "beval_world_raw2 tw (Bsig SEL) (Bv True)"
  assumes "beval_world_raw2 tw (Bsig IN1) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "mux2_inv' (next_time_world tw', snd tw')"
proof -
  let ?t' = "next_time_world tw'"
  have assms1: "beval_world_raw (snd tw) (fst tw) (Bsig SEL) (Bv True)"
    using assms(1) unfolding beval_world_raw2_def by auto
  have "bval_of_wline tw SEL (fst tw)"
    apply (rule beval_world_raw_cases[OF assms1], erule beval_cases)
    by (metis comp_def state_of_world_def val.sel(1))
  { assume "disjnt {IN0, IN1, SEL} (event_of (?t', snd tw'))"
    have "fst tw' < ?t'"
      using next_time_world_at_least by blast
    moreover have "fst tw = fst tw'"
      unfolding tw'_def unfolding worldline_upd2_def by auto
    ultimately have "fst tw < ?t'"
      by auto
    have *: "\<And>s. s \<in> {IN0, IN1, SEL} \<Longrightarrow> wline_of tw' s ?t' = wline_of tw s (fst tw)"
      using \<open>disjnt {IN0, IN1, SEL} (event_of (next_time_world tw', snd tw'))\<close>
      input_signals_unchanged tw'_def  assms(2) assms(3) by blast
    have "\<And>i. ?t' \<le> i \<Longrightarrow> wline_of tw' OUT (i + 1) =
       (if bval_of_wline tw' SEL ?t' then wline_of tw' IN1 ?t' else wline_of tw' IN0 ?t')"
    proof -
      fix i
      assume "?t' \<le> i"
      have assms2: "beval_world_raw (snd tw) (fst tw) (Bsig IN1) v"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "wline_of tw' OUT (i + 1) = wline_of tw IN1 (fst tw)"
        apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
        using `?t' \<le> i` `fst tw < ?t'` unfolding tw'_def worldline_upd2_def worldline_upd_def
        by (simp add: state_of_world_def)
      also have "... = (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw' IN0 ?t')"
        using \<open>bval_of_wline tw SEL (fst tw)\<close>  by (simp add: state_of_world_def)
      also have "... = (if bval_of_wline tw' SEL ?t' then wline_of tw' IN1 ?t' else wline_of tw' IN0 ?t')"
        using * by auto
      finally show "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL ?t' then wline_of tw' IN1 ?t' else wline_of tw' IN0 ?t')"
        by auto
    qed }
  thus ?thesis
    unfolding mux2_inv'_def by auto
qed

lemma mux2_inv'_next_time2:
  assumes "beval_world_raw2 tw (Bsig SEL) (Bv False)"
  assumes "beval_world_raw2 tw (Bsig IN0) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  shows   "mux2_inv' (next_time_world tw', snd tw')"
proof -
  let ?t' = "next_time_world tw'"
  have assms1: "beval_world_raw (snd tw) (fst tw) (Bsig SEL) (Bv False)"
    using assms(1) unfolding beval_world_raw2_def by auto
  have "\<not> bval_of_wline tw SEL (fst tw)"
    by (rule beval_world_raw_cases[OF assms1], erule beval_cases)
       (metis comp_def state_of_world_def val.sel(1))
  { assume "disjnt {IN0, IN1, SEL} (event_of (?t', snd tw'))"
    have "fst tw' < ?t'"
      using next_time_world_at_least by blast
    moreover have "fst tw = fst tw'"
      unfolding tw'_def unfolding worldline_upd2_def by auto
    ultimately have "fst tw < ?t'"
      by auto
    have *: "\<And>s. s \<in> {IN0, IN1, SEL} \<Longrightarrow> wline_of tw' s ?t' = wline_of tw s (fst tw)"
      using \<open>disjnt {IN0, IN1, SEL} (event_of (next_time_world tw', snd tw'))\<close>
      input_signals_unchanged tw'_def assms(2) assms(3) by auto
    have "\<And>i. ?t' \<le> i \<Longrightarrow> wline_of tw' OUT (i + 1) =
                                     (if bval_of_wline tw' SEL ?t' then wline_of tw' IN1 ?t' else wline_of tw' IN0 ?t')"
    proof -
      fix i
      assume "?t' \<le> i"
      have assms2: "beval_world_raw (snd tw) (fst tw) (Bsig IN0) v"
        using assms(2) unfolding beval_world_raw2_def by auto
      have "wline_of tw' OUT (i + 1) = wline_of tw IN0 (fst tw)"
        apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
        using `fst tw < ?t'` and `?t' \<le> i` unfolding tw'_def worldline_upd2_def worldline_upd_def
        state_of_world_def by auto
      also have "... = (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw IN0 (fst tw))"
        using \<open>\<not> bval_of_wline tw SEL (fst tw)\<close> by (simp add: state_of_world_def)
      also have "... = (if bval_of_wline tw' SEL ?t' then wline_of tw' IN1 ?t' else wline_of tw' IN0 ?t')"
        using * by auto
      finally show "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL ?t' then wline_of tw' IN1 ?t' else wline_of tw' IN0 ?t')"
        by auto
    qed }
  thus ?thesis
    unfolding mux2_inv'_def by auto
qed

lemma mux2_seq_hoare_next_time_if':
  "\<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw) \<and> beval_world_raw2 tw (Bsig SEL) (Bv True)] Bassign_trans OUT (Bsig IN1) 1 [\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using mux2_inv'_next_time  by blast+

lemma mux2_seq_hoare_next_time_else':
  " \<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw) \<and> beval_world_raw2 tw (Bsig SEL) (Bv False)] Bassign_trans OUT (Bsig IN0) 1 [\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using mux2_inv'_next_time2  by blast+

theorem mux2_seq_hoare_next_time':
  "\<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1) [\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)" and P = "\<lambda>tw. wityping \<Gamma> (snd tw)", rotated 1], rule If2)
  unfolding simp_thms(22)
     apply (rule mux2_seq_hoare_next_time_if')
    apply (rule mux2_seq_hoare_next_time_else')
   apply simp+
  done

theorem mux2_seq_hoare_next_time'_wityping:
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  shows
  "\<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)]
        Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1)
     [\<lambda>tw. mux2_inv' (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
   apply (rule mux2_seq_hoare_next_time')
  apply (rule seq_stmt_preserve_wityping_hoare)
  apply (rule assms)
  done

subsection \<open>Proving that the concurrent component\<close>

lemma mux2_inv_conc_hoare:
  "\<And>tw. mux2_inv tw \<and> mux2_inv' tw \<and> disjnt {IN0, IN1, SEL} (event_of tw) \<Longrightarrow> mux2_inv (next_time_world tw, snd tw)"
proof -
  fix tw
  assume "mux2_inv tw \<and> mux2_inv' tw \<and> disjnt {IN0, IN1, SEL} (event_of tw)"
  hence "mux2_inv tw" and "mux2_inv' tw" and "disjnt {IN0, IN1, SEL} (event_of tw)"
    by auto
  hence *: "\<forall>i < fst tw. wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL i then wline_of tw IN1 i else wline_of tw IN0 i)"
    unfolding mux2_inv_def by auto
  have **: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. wline_of tw s i = wline_of tw s (fst tw))"
    using unchanged_until_next_time_world by blast
  have ***: "(\<forall>i\<ge> fst tw. wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw IN0 (fst tw)))"
    using \<open>mux2_inv' tw\<close> \<open>disjnt {IN0, IN1, SEL} (event_of tw)\<close> unfolding mux2_inv'_def by auto

  \<comment> \<open>obtain the value of A and B at time fst tw\<close>
  have  "wline_of tw SEL (fst tw) = wline_of tw SEL (fst tw - 1)" and "wline_of tw IN0 (fst tw) = wline_of tw IN0 (fst tw - 1)"
    and "wline_of tw IN1 (fst tw) = wline_of tw IN1 (fst tw - 1)"
    using \<open>disjnt {IN0, IN1, SEL} (event_of tw)\<close> unfolding event_of_alt_def
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+
 { fix i
    assume "i < next_time_world tw"
    have "i < fst tw \<or> fst tw \<le> i"
      by auto
    moreover
    { assume "i < fst tw"
      hence "wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL i then wline_of tw IN1 i else wline_of tw IN0 i)"
        using * by auto }
    moreover
    { assume "fst tw \<le> i"
      hence "wline_of tw OUT (i + 1) = wline_of tw OUT (fst tw + 1)"
        using *** by auto
      also have "... = (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw IN0 (fst tw))"
        using *** \<open>fst tw \<le> i\<close> by auto
      also have "... = (if bval_of_wline tw SEL i then wline_of tw IN1 i else wline_of tw IN0 i)"
        using ** \<open>i < next_time_world tw\<close> \<open>fst tw \<le> i\<close> less_imp_le_nat by presburger
      finally have "wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL i then wline_of tw IN1 i else wline_of tw IN0 i)"
        by auto }
    ultimately have "wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL i then wline_of tw IN1 i else wline_of tw IN0 i)"
      by auto }
  hence "\<And>i. i < next_time_world tw \<Longrightarrow> wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL i then wline_of tw IN1 i else wline_of tw IN0 i)"
    by auto
  thus "mux2_inv (next_time_world tw, snd tw)"
    unfolding mux2_inv_def by auto
qed

lemma mux2_inv'_conc_hoare:
  "\<And>tw. mux2_inv tw \<and> mux2_inv' tw \<and> disjnt {IN0, IN1, SEL} (event_of tw) \<Longrightarrow> mux2_inv' (next_time_world tw, snd tw)"
proof -
  fix tw
  assume "mux2_inv tw \<and> mux2_inv' tw \<and> disjnt {IN0, IN1, SEL} (event_of tw)"
  hence "mux2_inv tw" and "mux2_inv' tw" and "disjnt {IN0, IN1, SEL} (event_of tw)"
    by auto
  hence 0: "(\<forall>i\<ge>fst tw. wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL (get_time tw) then wline_of tw IN1 (get_time tw) else wline_of tw IN0 (get_time tw)))"
    unfolding mux2_inv'_def by auto
  have 1: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. wline_of tw s i = wline_of tw s (fst tw))"
    using unchanged_until_next_time_world by blast
  let ?t' = "next_time_world tw"
  { assume "disjnt {IN0, IN1, SEL} (event_of (next_time_world tw, snd tw))"
    hence *: "wline_of tw IN0 ?t' = wline_of tw IN0 (?t' - 1)" and **: "wline_of tw IN1 ?t' = wline_of tw IN1 (?t' - 1)"
        and ***: "wline_of tw SEL ?t' = wline_of tw SEL (?t' - 1)"
      unfolding event_of_alt_def
      by (smt comp_apply diff_is_0_eq' disjnt_insert1 fst_conv le_numeral_extra(1) mem_Collect_eq snd_conv)+
    have "fst tw < next_time_world tw"
      by (simp add: next_time_world_at_least)
    { fix i
      assume "?t' \<le> i"
      hence "wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL (fst tw) then wline_of tw IN1 (fst tw) else wline_of tw IN0 (fst tw))"
        using 0 \<open>fst tw < ?t'\<close> by auto
      moreover have "wline_of tw IN0 (fst tw) = wline_of tw IN0 (?t' - 1)" and "wline_of tw IN1 (fst tw) = wline_of tw IN1 (?t' - 1)"
        and "wline_of tw SEL (fst tw) = wline_of tw SEL (?t' - 1)"
        using 1
        by (metis (no_types, lifting) One_nat_def Suc_leI \<open>get_time tw < next_time_world tw\<close>
        add_le_cancel_right diff_add diff_less discrete gr_implies_not_zero neq0_conv zero_less_one)+
      ultimately have "wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL ?t' then wline_of tw IN1 ?t' else wline_of tw IN0 ?t')"
        using * ** *** by auto
    }
    hence "(\<forall>i\<ge>?t'. wline_of tw OUT (i + 1) = (if bval_of_wline tw SEL ?t' then wline_of tw IN1 ?t' else wline_of tw IN0 ?t'))"
      by auto }
  thus "mux2_inv' (next_time_world tw, snd tw)"
    unfolding mux2_inv'_def by auto
qed

lemma mux2_conc_hoare_without:
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  shows
  "\<turnstile> \<lbrace>\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> mux2_inv' tw\<rbrace>
        mux2
     \<lbrace>\<lambda>tw. mux2_inv  (next_time_world tw, snd tw)  \<and> mux2_inv' (next_time_world tw, snd tw)\<rbrace>"
  unfolding mux2_def
  apply (rule Single)
  apply (rule Conj)
    apply (rule strengthen_precondition)
    apply (rule strengthen_precondition)
    apply (rule mux2_seq_hoare_next_time)
   apply (rule strengthen_precondition)
   apply (rule strengthen_precondition)
   apply (rule strengthen_precondition2)
   apply (rule mux2_seq_hoare_next_time')
  using mux2_inv_conc_hoare mux2_inv'_conc_hoare by blast

lemma mux2_conc_hoare:
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  shows
  "\<turnstile> \<lbrace>\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> mux2_inv' tw\<rbrace>
        mux2
     \<lbrace>\<lambda>tw. (mux2_inv  (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)) \<and> mux2_inv' (next_time_world tw, snd tw)\<rbrace>"
  apply (rule Conj2)
   apply (rule Conj2)
  apply (rule weaken_post_conc_hoare[OF _ mux2_conc_hoare_without], blast)
    apply(rule assms)
   apply (rule strengthen_pre_conc_hoare[rotated])
  unfolding mux2_def apply (rule single_conc_stmt_preserve_wityping_hoare)
    apply (rule assms)
   apply blast
  apply (fold mux2_def)
  apply (rule weaken_post_conc_hoare[OF _ mux2_conc_hoare_without])
   apply blast
  apply (rule assms)
  done

subsection \<open>Simulation preserves the invariant\<close>

lemma mux2_conc_sim:
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  shows
    "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> mux2_inv' tw\<rbrace> mux2 \<lbrace>\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> mux2_inv' tw\<rbrace>"
  apply (rule While)
  apply (unfold snd_conv, rule mux2_conc_hoare)
  apply (rule assms)
  done

lemma mux2_conc_sim':
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  shows "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> mux2_inv' tw\<rbrace> mux2 \<lbrace>mux2_inv'\<rbrace>"
  apply (rule Conseq_sim[where Q="\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> mux2_inv' tw" and
                               P="\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> mux2_inv' tw"])
  by (blast intro: mux2_conc_sim[OF assms])+

subsection \<open>Initialisation preserves the invariant\<close>

lemma init_sat_mux2_inv:
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  shows "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) mux2 (mux2_inv)"
  unfolding mux2_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule weaken_postcondition[OF mux2_seq_hoare_next_time0_wityping[OF assms]])
  done

lemma init_sat_mux_inv':
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  shows "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) mux2 mux2_inv'"
  unfolding mux2_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule weaken_postcondition[OF mux2_seq_hoare_next_time'_wityping[OF assms]])
  done

lemma init_sat_nand_mux_inv_comb:
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  shows "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) mux2 (\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw)"
  apply (rule ConjI_sim)
   apply (rule init_sat_mux2_inv)
  apply (rule assms)
  apply (rule ConseqI_sim[where P="\<lambda>tw. wityping \<Gamma> (snd tw)"])
  apply (simp, rule init_sat_mux_inv'[OF assms], simp)
  done

lemma init_sat_nand_mux_inv_comb_wityping:
  assumes "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
  shows "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) mux2 (\<lambda>tw. (mux2_inv tw \<and> mux2_inv' tw) \<and> wityping \<Gamma> (snd tw))"
  apply (rule ConjI_sim)
   apply (rule ConseqI_sim[rotated])
     apply (rule init_sat_nand_mux_inv_comb)
     apply (rule assms)
    apply simp
   apply simp
  apply (rule strengthen_precondition_init_sim_hoare[rotated])
  unfolding mux2_def apply (rule single_conc_stmt_preserve_wityping_init_sim_hoare)
   apply (rule assms)
  apply blast
  done

lemma mux2_correctness:
  assumes "sim_fin w (i + 1) mux2 tw'" and "wityping \<Gamma> w"
  assumes "conc_wt \<Gamma> mux2"
  shows "wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
proof -
  obtain tw where "init_sim (0, w) mux2 tw" and  "tw, i + 1, mux2 \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 < fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf mux2"
    unfolding conc_stmt_wf_def mux2_def by auto
  moreover have "nonneg_delay_conc mux2"
    unfolding mux2_def by auto
  moreover have "seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))"
    using assms(3) by (metis conc_wt_cases(1) mux2_def)
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) mux2 (\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw \<and> wityping \<Gamma> (snd tw))"
    using init_sim_hoare_soundness[OF init_sat_nand_mux_inv_comb_wityping]  by auto
  hence "mux2_inv tw \<and> mux2_inv' tw \<and> wityping \<Gamma> (snd tw)"
    using \<open>init_sim (0, w) mux2 tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis (full_types) snd_conv)
  hence "mux2_inv tw" and "mux2_inv' tw" and "wityping \<Gamma> (snd tw)"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> mux2_inv' tw\<rbrace> mux2 \<lbrace>\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> mux2_inv' tw\<rbrace>"
    using conc_sim_soundness[OF mux2_conc_sim] \<open>conc_stmt_wf mux2\<close> \<open>nonneg_delay_conc mux2\<close>
    using \<open>seq_wt \<Gamma> (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1))\<close>
    by simp
  ultimately have "mux2_inv tw'"
    using \<open>tw, i + 1, mux2 \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'. wline_of tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then wline_of tw' IN1 i else wline_of tw' IN0 i)"
    unfolding mux2_inv_def by auto
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed

end