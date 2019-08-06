(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Double_Inverter
  imports VHDL_Hoare_Complete
begin

text \<open>datatypes for all signals\<close>

datatype sig = IN | TEMP | OUT

\<comment> \<open>VHDL program for double inverter\<close>
definition two_inverter :: "sig conc_stmt" where
  "two_inverter \<equiv>  (process {IN} : Bassign_trans TEMP (Bsig IN) 1)
                || (process {TEMP} : Bassign_trans OUT (Bsig TEMP) 1)"

\<comment> \<open>the first invariant for double inverter\<close>
definition inv_first :: "sig assn2" where
  "inv_first \<equiv> (\<lambda>tw. \<forall>i < fst tw. snd tw TEMP (i + 1) \<longleftrightarrow> snd tw IN i)"

\<comment> \<open>the second invariant for double inverter\<close>
definition inv_second :: "sig assn2" where
  "inv_second \<equiv> (\<lambda>tw. \<forall>i < fst tw. snd tw OUT (i + 1) \<longleftrightarrow> snd tw TEMP i)"

definition inv_first_hold :: "sig assn2" where  
  "inv_first_hold \<equiv> (\<lambda>tw. disjnt {IN} (event_of tw) \<longrightarrow> 
                                         (\<forall>i \<ge> fst tw. snd tw TEMP (i + 1) \<longleftrightarrow> snd tw IN (fst tw)))"

definition inv_second_hold :: "sig assn2" where
  "inv_second_hold \<equiv> (\<lambda>tw. disjnt {TEMP} (event_of tw) \<longrightarrow> 
                                         (\<forall>i \<ge> fst tw. snd tw OUT (i + 1) \<longleftrightarrow> snd tw TEMP (fst tw)))"

subsection \<open>First invariant hold at the next time\<close>

lemma inv_first_next_time:
  assumes "inv_first tw"
  defines "tw' \<equiv> tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)]"
  shows  "inv_first (next_time_world tw', snd tw')"
proof -
  let ?t' = "next_time_world tw'"
  have "fst tw' < ?t'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < ?t'"
    by auto
  have "\<forall>i<?t'. snd tw' TEMP (i + 1) \<longleftrightarrow> snd tw' IN i"
  proof (rule, rule)
    fix i
    assume "i < ?t'"
    have "i < fst tw \<or> fst tw \<le> i \<and> i < ?t' - 1 \<or> i = ?t' - 1"
      using next_time_world_at_least \<open>i < next_time_world tw'\<close> not_less by linarith
    moreover
    { assume "i < fst tw"
      hence "snd tw TEMP (i + 1) \<longleftrightarrow> snd tw IN i"
        using assms(1) unfolding inv_first_def by auto
      moreover have "snd tw TEMP (i + 1) \<longleftrightarrow> snd tw' TEMP (i + 1)" and "snd tw IN i \<longleftrightarrow> snd tw' IN i"
        using worldline_upd2_before_dly \<open>i < fst tw\<close> unfolding tw'_def
        by (simp add: worldline_upd2_before_dly)+
      ultimately have "snd tw' TEMP (i + 1) \<longleftrightarrow> snd tw' IN i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < ?t' - 1"
      hence "snd tw' TEMP (i + 1) \<longleftrightarrow> snd tw' TEMP (fst tw + 1)" 
        using unchanged_until_next_time_world 
        by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
            le_less_trans less_diff_conv)
      have "snd tw' IN i \<longleftrightarrow> snd tw' IN (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i < ?t' - 1\<close>
        by (simp add: unchanged_until_next_time_world \<open>get_time tw = get_time tw'\<close> \<open>i < next_time_world tw'\<close>)+
      hence "snd tw' TEMP  (fst tw + 1) \<longleftrightarrow> snd tw' IN (fst tw)"
        by (metis beval_world_raw2_Bsig less_add_one tw'_def worldline_upd2_at_dly worldline_upd2_before_dly)
      hence "snd tw' TEMP (i + 1) \<longleftrightarrow> snd tw' IN i"
        using \<open>snd tw' IN i = snd tw' IN (get_time tw)\<close> \<open>snd tw' TEMP (i + 1) = snd tw' TEMP (get_time tw + 1)\<close> 
        by blast }
    moreover
    { assume "i = ?t' - 1"
      hence "snd tw' TEMP (i + 1) \<longleftrightarrow> snd tw' TEMP ?t'"
        using \<open>i < ?t'\<close> by auto
      also have "... \<longleftrightarrow> snd tw' TEMP (fst tw + 1)"
        using \<open>fst tw < ?t'\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... \<longleftrightarrow> snd tw' IN (fst tw)"
        by (metis beval_world_raw2_Bsig less_add_one tw'_def worldline_upd2_at_dly  worldline_upd2_before_dly)
      also have "... \<longleftrightarrow> snd tw' IN i"
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < get_time tw \<Longrightarrow> snd tw' TEMP (i + 1) = snd tw' IN i\<close> 
            \<open>i < next_time_world tw'\<close> calculation not_less unchanged_until_next_time_world)
      finally have "snd tw' TEMP (i + 1) \<longleftrightarrow> snd tw' IN i"
        by auto }
    ultimately show "snd tw' TEMP (i + 1) \<longleftrightarrow> snd tw' IN i"
      by auto
  qed
  thus ?thesis
    unfolding inv_first_def by auto
qed

lemma seq_part_when_not_disjnt:
  " \<turnstile> [\<lambda>tw. (inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)] 
        Bassign_trans TEMP (Bsig IN) 1
      [\<lambda>tw. inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) 
          \<and> inv_first (next_time_world tw, snd tw) 
          \<and> inv_second tw 
          \<and> inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) 
          \<and> inv_first_hold (next_time_world tw, snd tw) \<and> inv_second_hold tw]"
proof -
  {
  fix tw
  assume "(inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)"
  hence "inv_first tw" and "inv_second tw" and "inv_first_hold tw" and "inv_second_hold tw" and "\<not> disjnt {IN} (event_of tw)"
    by auto
  define tw1 where "tw1 = tw [TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)]"
  define tw2 where "tw2 = tw1[OUT, 1 :=\<^sub>2 beval_world_raw2 tw1 (Bsig TEMP)]"
  define t' where "t' = next_time_world tw1"
  
  \<comment> \<open>general results outside of each proof obligation\<close>
  have "fst tw < t'"
    unfolding t'_def   by (metis fst_conv next_time_world_at_least tw1_def worldline_upd2_def)
  have "fst tw = fst tw1"
    by (simp add: tw1_def worldline_upd2_def)
  also have "... = fst tw2"
    by (simp add: tw1_def tw2_def worldline_upd2_def)
  also have "... < next_time_world tw2"
    using next_time_world_at_least by  metis
  finally have "fst tw < next_time_world tw2"
    by auto
  have "fst tw1 < next_time_world tw2"
    by (simp add: \<open>get_time tw1 = get_time tw2\<close> \<open>get_time tw2 < next_time_world tw2\<close>)

  have 0: "inv_second tw1" \<comment> \<open>unaffected invariant\<close>
    unfolding inv_second_def
  proof (rule, rule)
    fix i 
    assume "i < fst tw1"
    hence "i < fst tw"
      using \<open>fst tw = fst tw1\<close> by auto
    have "snd tw1 OUT (i + 1) = snd tw OUT (i + 1)"
      unfolding tw1_def  by (simp add: \<open>i < get_time tw\<close> worldline_upd2_before_dly)
    also have "... = snd tw TEMP i"
      using \<open>inv_second tw\<close> \<open>i < fst tw\<close> unfolding inv_second_def by auto
    also have "... = snd tw1 TEMP i"
      unfolding tw1_def using \<open>i < fst tw\<close> by (auto simp add: worldline_upd2_before_dly)
    finally show "snd tw1 OUT (i + 1) = snd tw1 TEMP i"
      by auto
  qed

  \<comment> \<open>second unaffected invariant\<close>
  have 1: "inv_second_hold tw1"
    unfolding inv_second_hold_def
  proof (rule, rule, rule)
    fix i
    assume "disjnt {TEMP} (event_of tw1)"
    hence "disjnt {TEMP} (event_of tw)"
      using \<open>fst tw = fst tw1\<close> unfolding tw1_def 
      by (smt discrete disjnt_iff event_of_alt_def le_add1 less_diff_conv mem_Collect_eq nat_neq_iff
      not_less snd_conv worldline_upd2_def worldline_upd_def)
    assume "fst tw1 \<le> i"
    hence "fst tw \<le> i"
      using \<open>fst tw = fst tw1\<close> by auto
    hence "snd tw OUT (i + 1) = snd tw TEMP (fst tw)"
      using `inv_second_hold tw` \<open>disjnt {TEMP} (event_of tw)\<close> unfolding inv_second_hold_def
      by auto
    moreover have "snd tw OUT (i + 1) = snd tw1 OUT (i + 1)" and "snd tw TEMP (fst tw) = snd tw1 TEMP (fst tw)"
      by (simp add: tw1_def worldline_upd2_def worldline_upd_def)+
    ultimately show "snd tw1 OUT (i + 1) = snd tw1 TEMP (get_time tw1)"
      using \<open>fst tw = fst tw1\<close> by auto
  qed

  have 2: "inv_first (next_time_world tw2, snd tw2)"
    unfolding inv_first_def
  proof (rule, rule)
    fix i
    assume "i < fst (next_time_world tw2, snd tw2)"
    hence "i < next_time_world tw2"
      by auto
    with \<open>fst tw < next_time_world tw2\<close> 
    have "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw2 - 1 \<or> i = next_time_world tw2 - 1"
      by auto
    moreover
    { assume "i < fst tw"
      have "snd tw2 TEMP (i + 1) = snd tw TEMP (i + 1)"
        by (metis \<open>get_time tw = get_time tw1\<close> \<open>i < get_time tw\<close> add_mono1 tw1_def tw2_def
        worldline_upd2_before_dly)
      also have "... = snd tw IN i"
        using \<open>inv_first tw\<close> \<open>i < fst tw\<close> unfolding inv_first_def by auto
      also have "... = snd tw2 IN i"
        by (metis \<open>get_time tw = get_time tw1\<close> \<open>i < get_time tw\<close> add.right_neutral
        add_mono_thms_linordered_field(5) tw1_def tw2_def worldline_upd2_before_dly zero_less_one)
      finally have "snd tw2 TEMP (i + 1) = snd tw2 IN i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < next_time_world tw2 - 1"
      hence "fst tw2 \<le> i \<and> i < next_time_world tw2 - 1"
        by (simp add: \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 = get_time tw2\<close>)
      hence "snd tw2 TEMP (i + 1) = snd tw2 TEMP (fst tw2 + 1)"
        by (metis (no_types, lifting) One_nat_def Suc_less_eq \<open>get_time tw2 < next_time_world tw2\<close>
        add.right_neutral add_Suc_right le_Suc_eq less_diff_conv not_less
        unchanged_until_next_time_world)
      also have "... = snd tw1 TEMP (fst tw2 + 1)"
        by (metis \<open>get_time tw1 = get_time tw2\<close> sig.distinct(6) tw2_def worldline_upd2_at_dly_nonsig)
      also have "... = snd tw1 TEMP (fst tw + 1)"
        by (simp add: \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 = get_time tw2\<close>)
      also have "... = snd tw IN (fst tw) "
        unfolding tw1_def   by (metis worldline_upd2_at_dly beval_world_raw2_Bsig)
      also have "... = snd tw1 IN (fst tw1)"
        by (simp add: \<open>get_time tw = get_time tw1\<close> tw1_def worldline_upd2_before_dly)
      also have "... = snd tw2 IN (fst tw2)"
        by (simp add: \<open>get_time tw1 = get_time tw2\<close> tw2_def worldline_upd2_before_dly)
      also have "... = snd tw2 IN i"
        using \<open>get_time tw2 \<le> i \<and> i < next_time_world tw2 - 1\<close> \<open>i < next_time_world tw2\<close>
        unchanged_until_next_time_world by blast
      finally have "snd tw2 TEMP (i + 1) = snd tw2 IN i"
        by auto }
    moreover
    { assume "i = next_time_world tw2 - 1"
      hence "snd tw2 TEMP (i + 1) = snd tw2 TEMP (next_time_world tw2)"
        using \<open>i < next_time_world tw2\<close> by force
      also have "... = snd tw2 TEMP (fst tw2 + 1)"
        unfolding tw2_def 
        by (metis \<open>get_time tw < next_time_world tw2\<close> \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 =
        get_time tw2\<close> discrete less_add_one not_less snd_conv tw1_def tw2_def worldline_upd2_def
        worldline_upd_def)
      also have "... = snd tw2 TEMP (fst tw1 + 1)"
        by (simp add: \<open>get_time tw1 = get_time tw2\<close>)
      also have "... = snd tw1 TEMP (fst tw1 + 1)"
        unfolding tw2_def by (metis sig.distinct(6) worldline_upd2_at_dly_nonsig)
      also have "... = snd tw IN (fst tw)"
        unfolding tw1_def 
        by (metis \<open>get_time tw = get_time tw1\<close> beval_world_raw2_Bsig tw1_def worldline_upd2_at_dly)
      also have "... = snd tw1 IN (fst tw)"
        by (simp add: tw1_def worldline_upd2_before_dly)
      also have "... = snd tw2 IN (fst tw2)"
        by (simp add: \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 = get_time tw2\<close> tw2_def worldline_upd2_before_dly)
      also have "... = snd tw2 IN i"
        by (metis \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 = get_time tw2\<close> \<open>i < get_time tw \<Longrightarrow> snd
        tw2 TEMP (i + 1) = snd tw2 IN i\<close> \<open>i < next_time_world tw2\<close> calculation not_less
        unchanged_until_next_time_world)
      finally have "snd tw2 TEMP (i + 1) = snd tw2 IN i"
        by auto }
    ultimately have "snd tw2 TEMP (i + 1) = snd tw2 IN i"
      by auto
    thus " snd (next_time_world tw2, snd tw2) TEMP (i + 1) = snd (next_time_world tw2, snd tw2) IN i"
      by auto
  qed

  have 3: "inv_first_hold (next_time_world tw2, snd tw2)"
    unfolding inv_first_hold_def
  proof (rule, rule, rule)
    fix i
    assume "disjnt {IN} (event_of (next_time_world tw2, snd tw2))"
    assume "fst (next_time_world tw2, snd tw2) \<le> i"
    hence "next_time_world tw2 \<le> i" and "fst tw1 < i"
      using \<open>fst tw1 < next_time_world tw2\<close>  by auto
    hence "snd tw2 TEMP (i + 1) = snd tw1 TEMP (i + 1)"
      by (simp add: tw2_def worldline_upd2_def worldline_upd_def)
    also have "... = snd tw IN (fst tw)"
      unfolding tw1_def
      by (metis \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 < i\<close> add.commute fst_conv less_imp_le_nat
      nat_add_left_cancel_less not_less snd_swap swap_simp worldline_upd2_def worldline_upd_def beval_world_raw2_Bsig)
    also have "... = snd tw2 IN (fst tw2)"
      by (metis \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 = get_time tw2\<close> less_add_one tw1_def tw2_def worldline_upd2_before_dly)
    also have "... = snd tw2 IN (next_time_world tw2 - 1)"
      using unchanged_until_next_time_world 
      by (metis Suc_diff_1 \<open>get_time tw2 < next_time_world tw2\<close> diff_less gr_implies_not_zero le_Suc_eq less_imp_le_nat nat_neq_iff zero_less_one)
    also have "... = snd tw2 IN (next_time_world tw2)"
      using \<open>disjnt {IN} (event_of (next_time_world tw2, snd tw2))\<close>
      unfolding event_of_alt_def  using \<open>get_time tw2 < next_time_world tw2\<close> by auto
    finally have "snd tw2 TEMP (i + 1) = snd tw2 IN (next_time_world tw2)"
      by auto
    thus "snd (next_time_world tw2, snd tw2) TEMP (i + 1) = 
          snd (next_time_world tw2, snd tw2) IN (get_time (next_time_world tw2, snd tw2))"
      by auto
  qed

  have 4: "inv_first (t', snd tw1)"
    unfolding inv_first_def
  proof (rule, rule)
    fix i
    assume "i < fst (t', snd tw1)"
    hence "i < t'" 
      by auto
    hence "i < fst tw \<or> fst tw \<le> i \<and> i < t' - 1 \<or> i = t' - 1"
      using \<open>fst tw < t'\<close> by linarith
    moreover
    { assume "i < fst tw"
      hence "snd tw1 TEMP (i + 1) =  snd tw TEMP (i + 1)"
        unfolding tw1_def by (auto simp add : worldline_upd2_before_dly)
      also have "... = snd tw IN i"
        using \<open>inv_first tw\<close> \<open>i < fst tw\<close> unfolding inv_first_def by auto
      also have "... = snd tw1 IN i"
        unfolding tw1_def  by (metis \<open>i < get_time tw\<close> add.right_neutral add_mono_thms_linordered_field(5)
        worldline_upd2_before_dly zero_less_one)
      finally have "snd tw1 TEMP (i + 1) = snd tw1 IN i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < t' - 1"
      hence "snd tw1 TEMP (i + 1) = snd tw1 TEMP (fst tw + 1)"
        using unchanged_until_next_time_world 
        unfolding `fst tw = fst tw1`  t'_def 
        by (metis (no_types, lifting) One_nat_def Suc_lessI Suc_less_eq \<open>get_time tw < t'\<close> \<open>get_time
        tw = get_time tw1\<close> add.right_neutral add_Suc_right diff_is_0_eq' le_Suc_eq le_add1
        less_diff_conv t'_def zero_less_diff)
      also have "... = snd tw IN (fst tw)"
        unfolding tw1_def  by (meson beval_world_raw2_Bsig worldline_upd2_at_dly)
      also have "... = snd tw1 IN (fst tw)"
        unfolding tw1_def  by (simp add: worldline_upd2_before_dly)
      also have "... = snd tw1 IN i"
        using unchanged_until_next_time_world 
        unfolding `fst tw = fst tw1`  t'_def 
        by (metis \<open>get_time tw = get_time tw1\<close> \<open>get_time tw \<le> i \<and> i < t' - 1\<close> \<open>i < t'\<close> t'_def)
      finally have "snd tw1 TEMP (i + 1) = snd tw1 IN i"
        by auto }
    moreover
    { assume "i = t' - 1"
      hence "snd tw1 TEMP (i + 1) = snd tw1 TEMP t'"
        using \<open>i < t'\<close> by force
      also have "... = snd tw1 TEMP (fst tw + 1)"
        unfolding t'_def using \<open>fst tw < t'\<close> 
        by (simp add: t'_def tw1_def worldline_upd2_def worldline_upd_def)
      also have "... = snd tw IN (fst tw)"
        unfolding tw1_def by (meson beval_world_raw2_Bsig worldline_upd2_at_dly)
      also have "... = snd tw1 IN (fst tw)"
        unfolding tw1_def by (simp add: worldline_upd2_before_dly)
      also have "... = snd tw1 IN i"
        by (metis \<open>get_time tw = get_time tw1\<close> \<open>i < get_time tw \<Longrightarrow> snd tw1 TEMP (i + 1) = snd tw1 IN
        i\<close> \<open>i < t'\<close> calculation not_less t'_def unchanged_until_next_time_world)
      finally have "snd tw1 TEMP (i + 1) = snd tw1 IN i"
        by auto }
    ultimately have "snd tw1 TEMP (i + 1) = snd tw1 IN i"
      by auto
    thus "snd (t', snd tw1) TEMP (i + 1) = snd (t', snd tw1) IN i"
      by auto
  qed

  have 5: "inv_first_hold (t', snd tw1)"
    unfolding inv_first_hold_def
  proof (rule, rule, rule)
    fix i
    assume "disjnt {IN} (event_of (t', snd tw1))"
    assume "fst (t', snd tw1) \<le> i"
    hence "t' \<le> i"
      by auto
    hence "snd tw1 TEMP (i + 1) = snd tw IN (fst tw)"
      using `fst tw < t'` unfolding tw1_def worldline_upd2_def worldline_upd_def beval_world_raw2_def
      beval_world_raw_def state_of_world_def by auto
    also have "... = snd tw1 IN (fst tw)"
      by (simp add: tw1_def worldline_upd2_before_dly)
    also have "... = snd tw1 IN (t' - 1)"
      unfolding t'_def `fst tw < t'` using unchanged_until_next_time_world 
      by (metis Suc_diff_1 \<open>get_time tw < t'\<close> \<open>get_time tw = get_time tw1\<close> diff_less
      gr_implies_not_zero le_Suc_eq less_imp_le_nat nat_neq_iff t'_def zero_less_one)
    also have "... = snd tw1 IN t'"
      using \<open>disjnt {IN} (event_of (t', snd tw1))\<close> unfolding event_of_alt_def
      using \<open>get_time tw < t'\<close> by auto
    finally show "snd (t', snd tw1) TEMP (i + 1) = snd (t', snd tw1) IN (get_time (t', snd tw1))"
      by auto
  qed

  have "inv_first (next_time_world tw2, snd tw2) \<and> inv_first (next_time_world tw1, snd tw1) \<and> 
         inv_second tw1 \<and> inv_first_hold (next_time_world tw2, snd tw2) \<and> 
         inv_first_hold (next_time_world tw1, snd tw1) \<and> inv_second_hold tw1"
    using 0 1 2 3 4 5 unfolding t'_def by auto }
  thus ?thesis
    by (intro Assign2_altI) auto
qed

lemma inv_first_disjnt_next_time_no_process_later:
  assumes "inv_first tw" and "inv_first_hold tw" and "disjnt {IN} (event_of tw)"
  shows "inv_first (next_time_world tw, snd tw)"
  unfolding inv_first_def
proof (rule, rule)
  fix i
  assume " i < get_time (next_time_world tw, snd tw)"
  hence "i < next_time_world tw"
    by auto
  hence "i < fst tw \<or> fst tw \<le> i"
    by auto
  moreover
  { assume "i < fst tw"
    hence "snd tw TEMP (i + 1) \<longleftrightarrow> snd tw IN i"
      using assms(1) unfolding inv_first_def by auto }
  moreover
  { assume "fst tw \<le> i"
    moreover have "(\<forall>i \<ge> fst tw. snd tw TEMP (i + 1) \<longleftrightarrow> snd tw IN (fst tw))"
      using assms(2-3) unfolding inv_first_hold_def by auto
    ultimately have "snd tw TEMP (i + 1) \<longleftrightarrow> snd tw IN (fst tw)"
      by auto
    also have "... \<longleftrightarrow> snd tw IN i"
      by (simp add: \<open>get_time tw \<le> i\<close> \<open>i < next_time_world tw\<close> unchanged_until_next_time_world)
    finally have "snd tw TEMP (i + 1) \<longleftrightarrow> snd tw IN i"
      by auto }
  ultimately have "snd tw TEMP (i + 1) \<longleftrightarrow> snd tw IN i"
    by auto
  thus "snd (next_time_world tw, snd tw) TEMP (i + 1) = snd (next_time_world tw, snd tw) IN i"
    by auto
qed

lemma inv_first_disjnt_next_time:
  assumes "inv_first tw" and "inv_first_hold tw" and "disjnt {IN} (event_of tw)"
  shows " inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])"
  unfolding inv_first_def
proof (rule, rule)
  fix i
  assume "i < fst (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])"
  hence "i < next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]"
    by auto
  let ?tw = "tw[OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]"
  have "fst ?tw < next_time_world ?tw"
    using next_time_world_at_least by metis
  moreover have "fst ?tw = fst tw"
    by (simp add: worldline_upd2_def)
  finally have "fst tw < next_time_world ?tw"
    by auto
  have "i < fst tw \<or> fst tw \<le> i"
    by auto
  moreover
  { assume "i < fst tw"
    hence "snd ?tw TEMP (i + 1) = snd tw TEMP (i + 1)"
      by (simp add: worldline_upd2_before_dly)
    also have "... = snd tw IN i"
      using assms(1) unfolding inv_first_def using \<open>i < get_time tw\<close> by blast
    also have "... = snd ?tw IN i"
      by (metis \<open>i < get_time tw\<close> add.right_neutral add_mono_thms_linordered_field(5)
      worldline_upd2_before_dly zero_less_one)
    finally have "snd ?tw TEMP (i + 1) = snd ?tw IN i"
      by auto }
  moreover
  { assume "fst tw \<le> i"
    have "snd ?tw TEMP (i + 1) = snd tw TEMP (i + 1)"
      using \<open>i < next_time_world ?tw\<close> \<open>fst tw < next_time_world ?tw\<close> 
      by (simp add: worldline_upd2_def worldline_upd_def)
    also have "... = snd tw IN i"
      using assms(2-3) unfolding inv_first_hold_def
      by (metis \<open>get_time tw \<le> i\<close> \<open>get_time tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)] =
      get_time tw\<close> \<open>i < next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]\<close>
      sig.distinct(3) snd_conv unchanged_until_next_time_world worldline_upd2_def worldline_upd_def)
    also have "... = snd ?tw IN i"
      by (simp add: worldline_upd2_def worldline_upd_def)
    finally have "snd ?tw TEMP (i + 1) = snd ?tw IN i"
      by auto }
  ultimately have "snd ?tw TEMP (i + 1) = snd ?tw IN i"
    by auto
  thus "snd (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) TEMP (i + 1) =
         snd (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) IN i"
    by auto
qed

lemma inv_first_hold_disjnt_next_time_no_process_later: 
  assumes "inv_first_hold tw" and "disjnt {IN} (event_of tw)"
  shows "inv_first_hold (next_time_world tw, snd tw)"
  unfolding inv_first_hold_def
proof (rule, rule, rule)
  fix i
  assume "disjnt {IN} (event_of (next_time_world tw, snd tw))"
  assume "fst (next_time_world tw, snd tw) \<le> i"
  hence "next_time_world tw \<le> i"
    by auto
  moreover have "fst tw < next_time_world tw"
    using next_time_world_at_least by metis
  ultimately have "fst tw \<le> i"
    by auto
  moreover have "(\<forall>i \<ge> fst tw. snd tw TEMP (i + 1) \<longleftrightarrow> snd tw IN (fst tw))"
    using assms unfolding inv_first_hold_def by auto
  ultimately have "snd tw TEMP (i + 1) \<longleftrightarrow> snd tw IN (fst tw)"
    by auto
  also have "... \<longleftrightarrow> snd tw IN (next_time_world tw - 1)"
    using unchanged_until_next_time_world 
    by (metis Suc_diff_1 Suc_leI \<open>get_time tw < next_time_world tw\<close> diff_less le_0_eq
    less_imp_le_nat not_less zero_less_one)
  also have "... \<longleftrightarrow> snd tw IN (next_time_world tw)"
    using \<open>disjnt {IN} (event_of (next_time_world tw, snd tw))\<close>
    unfolding event_of_alt_def  using \<open>get_time tw < next_time_world tw\<close> by auto
  finally have "snd tw TEMP (i + 1) \<longleftrightarrow> snd tw IN (next_time_world tw)"
    by auto
  thus "snd (next_time_world tw, snd tw) TEMP (i + 1) = 
                        snd (next_time_world tw, snd tw) IN (get_time (next_time_world tw, snd tw))"
    by auto
qed

lemma inv_first_hold_disjnt_next_time:
  assumes "inv_first_hold tw" and "disjnt {IN} (event_of tw)"
  shows "inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])"
  unfolding inv_first_hold_def
proof (rule, rule, rule)
  let ?tw = "tw[OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]"
  fix i
  assume "disjnt {IN} (event_of (next_time_world ?tw, snd ?tw))"
  assume "fst (next_time_world ?tw, snd ?tw) \<le> i"
  hence "next_time_world ?tw \<le> i"
    by auto
  moreover have "fst ?tw < next_time_world ?tw"
    using next_time_world_at_least by metis
  moreover have "fst tw = fst ?tw"
    by (simp add: worldline_upd2_def)
  ultimately have "fst tw < next_time_world ?tw"
    by auto
  have "snd ?tw TEMP (i + 1) = snd tw TEMP (i + 1)"
    by (simp add: worldline_upd2_def worldline_upd_def)
  also have "... = snd tw IN (fst tw)"
    using assms(1-2) \<open>fst tw < next_time_world ?tw\<close> \<open>next_time_world ?tw \<le> i\<close>
    unfolding inv_first_hold_def by auto
  also have "... = snd ?tw IN (fst tw)"
    by (simp add: worldline_upd2_before_dly)
  also have "... = snd ?tw IN (fst ?tw)"
    by (simp add: \<open>get_time tw = get_time tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]\<close>)
  also have "... = snd ?tw IN (next_time_world ?tw - 1)"
    using unchanged_until_next_time_world 
    by (smt \<open>get_time tw < next_time_world ?tw\<close> \<open>get_time tw = get_time ?tw\<close> diff_add diff_is_0_eq'
    discrete le_0_eq le_numeral_extra(4) less_le not_less)
  also have "... = snd ?tw IN (next_time_world ?tw)"
    using \<open>disjnt {IN} (event_of (next_time_world ?tw, snd ?tw))\<close>
    unfolding event_of_alt_def 
    using \<open>get_time tw < next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]\<close> by auto
  finally have "snd ?tw TEMP (i + 1) = snd ?tw IN (next_time_world ?tw)"
    by auto
  thus " snd (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) TEMP (i + 1) =
         snd (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) IN
          (get_time (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]))"
    by auto
qed

lemma conc_next_time:
  "\<turnstile> \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw\<rbrace>  
        process {IN} : Bassign_trans TEMP (Bsig IN) 1
     \<lbrace>\<lambda>tw. inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) 
         \<and> inv_first (next_time_world tw, snd tw) 
         \<and> inv_second tw 
         \<and> inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) 
         \<and> inv_first_hold (next_time_world tw, snd tw) \<and> inv_second_hold tw\<rbrace>"
  apply (rule Single)
   apply (rule seq_part_when_not_disjnt)
  using inv_first_disjnt_next_time inv_first_hold_disjnt_next_time 
    inv_first_disjnt_next_time_no_process_later inv_first_hold_disjnt_next_time_no_process_later
  by auto

lemma snd_seq_part_when_not_disjnt:
  "\<turnstile> [\<lambda>tw. (inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) \<and>
              inv_first (next_time_world tw, snd tw) \<and>
              inv_second tw \<and>
              inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) \<and>
              inv_first_hold (next_time_world tw, snd tw) \<and> inv_second_hold tw) \<and>
             \<not> disjnt {TEMP} (event_of tw)]
       Bassign_trans OUT (Bsig TEMP) 1
       [\<lambda>tw. inv_first (next_time_world tw, snd tw) \<and>
             inv_second (next_time_world tw, snd tw) \<and> inv_first_hold (next_time_world tw, snd tw) \<and> inv_second_hold (next_time_world tw, snd tw)]"
proof (rule Assign2_altI, rule, rule)
  fix tw
  define tw' where "tw' = tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]"
  define t' where "t' = next_time_world tw'"
  assume "(inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) \<and>
           inv_first (next_time_world tw, snd tw) \<and>
           inv_second tw \<and>
           inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) \<and>
           inv_first_hold (next_time_world tw, snd tw) \<and> inv_second_hold tw) \<and>
          \<not> disjnt {TEMP} (event_of tw)"
  hence 0: "inv_first (t', snd tw')" and "inv_second tw" and 1: "inv_first_hold (t', snd tw')" and "inv_second_hold tw"
    and "\<not> disjnt {TEMP} (event_of tw)"
    unfolding t'_def tw'_def by auto

  \<comment> \<open>general facts\<close>
  have "fst tw' < t'"
    using next_time_world_at_least unfolding t'_def by metis
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < t'"
    by auto

  have 2: "inv_second (t', snd tw')"
    unfolding inv_second_def
  proof (rule, rule)
    fix i
    assume "i < fst (t', snd tw')"
    hence "i < t'"
      by auto
    have "i < fst tw \<or> fst tw \<le> i \<or> i < t' - 1 \<or> i = t' - 1"
      using \<open>fst tw < t'\<close> by linarith
    moreover
    { assume "i < fst tw"
      hence "snd tw' OUT (i + 1) = snd tw OUT (i + 1)"
        by (simp add: tw'_def worldline_upd2_before_dly)
      also have "... = snd tw TEMP i"
        using \<open>inv_second tw\<close> \<open>i < fst tw\<close> unfolding inv_second_def by auto
      also have "... = snd tw' TEMP i"
        by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
      finally have "snd tw' OUT (i + 1) = snd tw' TEMP i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < t' - 1"
      hence "fst tw' \<le> i \<and> i < t' - 1"
        by (simp add: \<open>get_time tw = get_time tw'\<close>)
      hence "snd tw' OUT (i + 1) = snd tw' OUT (fst tw' + 1)"
        by (metis (no_types, lifting) One_nat_def Suc_less_eq \<open>get_time tw' < t'\<close> add.right_neutral
        add_Suc_right le_Suc_eq less_diff_conv not_less t'_def unchanged_until_next_time_world)
      also have "... = snd tw' OUT (fst tw + 1)"
        using \<open>get_time tw = get_time tw'\<close> by auto
      also have "... = snd tw TEMP (fst tw) "
        unfolding tw'_def by (meson beval_world_raw2_Bsig worldline_upd2_at_dly)
      also have "... = snd tw' TEMP (fst tw')"
        by (simp add: \<open>get_time tw = get_time tw'\<close> tw'_def worldline_upd2_before_dly)
      also have "... = snd tw' TEMP i"
        using \<open>get_time tw' \<le> i \<and> i < t' - 1\<close> \<open>i < t'\<close> t'_def unchanged_until_next_time_world by blast
      finally have "snd tw' OUT (i + 1) = snd tw' TEMP i"
        by auto }
    moreover
    { assume "i = t' - 1"
      hence "snd tw' OUT (i + 1) = snd tw' OUT t'"
        using \<open>i < t'\<close> by auto
      also have "... = snd tw TEMP (fst tw)"
        unfolding tw'_def using \<open>fst tw < t'\<close> 
        by (simp add: beval_world_raw2_Bsig worldline_upd2_def worldline_upd_def)
      also have "... = snd tw' TEMP (fst tw')"
        by (simp add: \<open>get_time tw = get_time tw'\<close> tw'_def worldline_upd2_before_dly)
      also have "... = snd tw' TEMP i"
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < get_time tw \<Longrightarrow> snd tw' OUT (i + 1) = snd tw' TEMP
        i\<close> \<open>i < t'\<close> calculation not_less t'_def unchanged_until_next_time_world)
      finally have "snd tw' OUT (i + 1) = snd tw' TEMP i"
        by auto }
    ultimately have "snd tw' OUT (i + 1) = snd tw' TEMP i"
      using \<open>i < t'\<close> by fastforce
    thus "snd (t', snd tw') OUT (i + 1) = snd (t', snd tw') TEMP i"
      by auto
  qed

  have 3: "inv_second_hold (t', snd tw')"
    unfolding inv_second_hold_def
  proof (rule, rule, rule)
    fix i
    assume "disjnt {TEMP} (event_of (t', snd tw'))"
    assume "fst (t', snd tw') \<le> i"
    hence "t' \<le> i"
      by auto
    hence "snd tw' OUT (i + 1) = beval_world_raw2 tw (Bsig TEMP)"
      using `fst tw < t'` unfolding tw'_def worldline_upd2_def worldline_upd_def
      by auto
    also have "... = snd tw TEMP (fst tw)"
      by (simp add: beval_world_raw2_Bsig)
    also have "... = snd tw' TEMP (fst tw')"
      by (simp add: \<open>get_time tw = get_time tw'\<close> tw'_def worldline_upd2_before_dly)
    also have "... = snd tw' TEMP (t' - 1)"
      using unchanged_until_next_time_world \<open>fst tw < t'\<close> 
      by (metis Suc_diff_1 \<open>get_time tw = get_time tw'\<close> diff_less gr_implies_not_zero le_Suc_eq
      less_imp_le_nat nat_neq_iff t'_def zero_less_one)
    also have "... = snd tw' TEMP t'"
      using \<open>disjnt {TEMP} (event_of (t', snd tw'))\<close> unfolding event_of_alt_def
      using \<open>get_time tw < t'\<close> by auto
    finally have "snd tw' OUT (i + 1) = snd tw' TEMP t'"
      by auto
    thus "snd (t', snd tw') OUT (i + 1) = snd (t', snd tw') TEMP (get_time (t', snd tw'))"
      by auto
  qed

  show "inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) \<and>
          inv_second (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) \<and>
          inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) \<and>
          inv_second_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])"
    using 0 1 2 3 unfolding t'_def tw'_def by auto
qed

lemma inv_second_next_time_world:
  assumes "inv_second tw" and "inv_second_hold tw" and " disjnt {TEMP} (event_of tw)"
  shows "inv_second (next_time_world tw, snd tw)"
  unfolding inv_second_def
proof (rule, rule)
  have *: "(\<forall>i \<ge> fst tw. snd tw OUT (i + 1) \<longleftrightarrow> snd tw TEMP (fst tw))"
    using assms(2-3) unfolding inv_second_hold_def by auto
  fix i 
  assume "i < fst (next_time_world tw, snd tw)"
  hence "i < next_time_world tw"
    by auto
  hence "i < fst tw \<or> fst tw \<le> i"
    by auto
  moreover
  { assume "i < fst tw"
    hence "snd tw OUT (i + 1) \<longleftrightarrow> snd tw TEMP i"
      using assms(1) unfolding inv_second_def by auto }
  moreover
  { assume "fst tw \<le> i"
    with * have "snd tw OUT (i + 1) \<longleftrightarrow> snd tw TEMP (fst tw)"
      by blast
    also have "... \<longleftrightarrow> snd tw TEMP i"
      using \<open>i < next_time_world tw\<close> unchanged_until_next_time_world 
      using \<open>get_time tw \<le> i\<close> by blast
    finally have "snd tw OUT (i + 1) \<longleftrightarrow> snd tw TEMP i"
      by auto }
  ultimately have "snd tw OUT (i + 1) \<longleftrightarrow> snd tw TEMP i"
    by auto
  thus " snd (next_time_world tw, snd tw) OUT (i + 1) = snd (next_time_world tw, snd tw) TEMP i"
    by auto
qed

lemma inv_second_hold_next_time_world:
  assumes "inv_second_hold tw" and "disjnt {TEMP} (event_of tw)"
  shows " inv_second_hold (next_time_world tw, snd tw)"
  unfolding inv_second_hold_def
proof (rule, rule, rule)
  have *: "(\<forall>i \<ge> fst tw. snd tw OUT (i + 1) \<longleftrightarrow> snd tw TEMP (fst tw))"
    using assms(1-2) unfolding inv_second_hold_def by auto
  fix i
  assume "disjnt {TEMP} (event_of (next_time_world tw, snd tw))"
  assume "get_time (next_time_world tw, snd tw) \<le> i"
  hence "next_time_world tw \<le> i"
    by auto
  hence "fst tw \<le> i"
    using next_time_world_at_least  by (metis dual_order.trans order.strict_iff_order)
  hence "snd tw OUT (i + 1) \<longleftrightarrow> snd tw TEMP (fst tw)"
    using * by blast
  also have "... \<longleftrightarrow> snd tw TEMP (next_time_world tw - 1)"
    using unchanged_until_next_time_world 
    by (metis Suc_diff_1 diff_less le_0_eq le_Suc_eq next_time_world_at_least not_less
    order.strict_iff_order zero_less_one)
  also have "... \<longleftrightarrow> snd tw TEMP (next_time_world tw)"
    using \<open>disjnt {TEMP} (event_of (next_time_world tw, snd tw))\<close>
    unfolding event_of_alt_def 
    by (smt diff_is_0_eq' disjnt_insert1 fst_conv le_numeral_extra(1) mem_Collect_eq snd_conv)
  finally have "snd tw OUT (i + 1) \<longleftrightarrow> snd tw TEMP (next_time_world tw)"
    by auto
  thus "snd (next_time_world tw, snd tw) OUT (i + 1) = snd (next_time_world tw, snd tw) TEMP (get_time (next_time_world tw, snd tw))"
    by auto
qed

lemma conc_next_time_second:
  "\<turnstile> \<lbrace>\<lambda>tw. inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) \<and>
            inv_first (next_time_world tw, snd tw) \<and>
            inv_second tw \<and>
            inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) \<and>
            inv_first_hold (next_time_world tw, snd tw) \<and> inv_second_hold tw\<rbrace>
        process {TEMP} : Bassign_trans OUT (Bsig TEMP) 1
       \<lbrace>\<lambda>tw. inv_first (next_time_world tw, snd tw) \<and>
             inv_second (next_time_world tw, snd tw) \<and> inv_first_hold (next_time_world tw, snd tw) \<and> inv_second_hold (next_time_world tw, snd tw)\<rbrace>"
  apply (rule Single)
  apply (rule snd_seq_part_when_not_disjnt)
  using inv_second_hold_next_time_world inv_second_next_time_world
  by auto

lemma conc_next_time_combined:
  "\<turnstile> \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw\<rbrace> 
        two_inverter
     \<lbrace>\<lambda>tw. inv_first (next_time_world tw, snd tw)  \<and> inv_second (next_time_world tw, snd tw) 
         \<and> inv_first_hold (next_time_world tw, snd tw)  \<and> inv_second_hold (next_time_world tw, snd tw)\<rbrace>"
  unfolding two_inverter_def
  apply (rule Parallel[where R="\<lambda>tw. inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd  tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])
                                   \<and> inv_first (next_time_world tw, snd tw) 
                                   \<and> inv_second tw 
                                   \<and> inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd  tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])
                                   \<and> inv_first_hold (next_time_world tw, snd tw)
                                   \<and> inv_second_hold tw"])
  apply (rule conc_next_time)
  apply (rule conc_next_time_second)
  by (auto simp add: conc_stmt_wf_def)

theorem sim_correctness_two_inverter:
  " \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw\<rbrace> 
        two_inverter 
      \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw\<rbrace>"
  apply (rule While)
  apply (rule conc_next_time_combined)
  done

corollary sim_correctness_two_inverter2:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw\<rbrace> 
        two_inverter 
      \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw\<rbrace>"
  apply (rule Conseq_sim[rotated 1])
    apply (rule sim_correctness_two_inverter)
   apply simp+
  done

subsection \<open>Initialisation satisfies invariants\<close>

lemma init_hoare1:
  " \<turnstile>\<^sub>I \<lbrace>\<lambda>tw. get_time tw = 0\<rbrace>  
          process {IN} : Bassign_trans TEMP (Bsig IN) 1
       \<lbrace>\<lambda>tw. inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])\<rbrace>"
proof (rule SingleI, rule Assign2_altI, rule, rule)
  fix tw :: "nat \<times> (sig \<Rightarrow> nat \<Rightarrow> bool)"
  assume "fst tw = 0"
  define tw1 where "tw1 = tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw  (Bsig IN)]"
  define tw2 where "tw2 = tw1[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw1 (Bsig TEMP)]"
  define t' where "t' = next_time_world tw1"

  have "fst tw1 < next_time_world tw1"
    using next_time_world_at_least by metis
  moreover have "fst tw1 = fst tw"
    unfolding tw1_def worldline_upd2_def by auto
  ultimately have "fst tw < next_time_world tw1"
    by auto

  have "inv_first (next_time_world tw2, snd tw2)"
    unfolding inv_first_def
  proof (rule, rule)
    fix i
    assume "i < fst (next_time_world tw2, snd tw2)"
    hence "i < next_time_world tw2"
      by auto
    have "fst tw < next_time_world tw2"
      using next_time_world_at_least  by (metis \<open>get_time tw = 0\<close> neq0_conv not_less0)
    have "fst tw1 < next_time_world tw2"
      using next_time_world_at_least 
      by (simp add: \<open>get_time tw < next_time_world tw2\<close> \<open>get_time tw1 = get_time tw\<close>)
    have "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw2 - 1 \<or> i = next_time_world tw2 - 1"
      using \<open>i < next_time_world tw2\<close> by linarith
    moreover
    { assume "i < fst tw"
      hence "False"
        using \<open>fst tw = 0\<close> by auto
      hence " snd tw2 TEMP (i + 1) = snd tw2 IN i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < next_time_world tw2 - 1"
      hence "snd tw2 TEMP (i + 1) = snd tw1 TEMP (i + 1)"
        unfolding tw2_def by (simp add: worldline_upd2_def worldline_upd_def)
      also have "... = beval_world_raw2 tw (Bsig IN)"
        unfolding tw1_def using \<open>fst tw \<le> i \<and> i < next_time_world tw2 - 1\<close> 
        by (simp add: \<open>get_time tw = 0\<close> worldline_upd2_def worldline_upd_def)
      also have "... = snd tw IN (fst tw)"
        by (simp add: beval_world_raw2_Bsig)
      also have "... = snd tw1 IN (fst tw1)"
        by (metis \<open>get_time tw1 = get_time tw\<close> less_add_one tw1_def worldline_upd2_before_dly)
      also have "... = snd tw2 IN (fst tw2)"
        by (simp add: tw2_def worldline_upd2_def worldline_upd_def)
      also have "... = snd tw2 IN i"
        by (metis \<open>get_time tw = 0\<close> \<open>get_time tw1 = get_time tw\<close> \<open>i < next_time_world tw2\<close> snd_conv
        snd_swap swap_simp tw2_def unchanged_until_next_time_world worldline_upd2_def zero_le)
      finally have "snd tw2 TEMP (i + 1) = snd tw2 IN i"
        by auto }
    moreover
    { assume "i = next_time_world tw2 - 1"
      hence "snd tw2 TEMP (i + 1) = snd tw2 TEMP (next_time_world tw2)"
        using \<open>get_time tw < next_time_world tw2\<close> by force
      also have "... = snd tw1 TEMP (next_time_world tw2)"
        unfolding tw2_def  by (simp add: worldline_upd2_def worldline_upd_def)
      also have "... = snd tw1 IN (fst tw)"
        unfolding tw1_def using \<open>fst tw < next_time_world tw2\<close> 
        by (metis One_nat_def Suc_diff_1 Suc_eq_plus1 \<open>get_time tw = 0\<close> beval_world_raw2_Bsig
        not_add_less2 snd_conv worldline_upd2_def worldline_upd_def)
      also have "... = snd tw2 IN (fst tw2)"
        by (simp add: \<open>get_time tw1 = get_time tw\<close> tw2_def worldline_upd2_def worldline_upd_def)
      also have "... = snd tw2 IN i"
        by (metis \<open>get_time tw = 0\<close> \<open>get_time tw1 = get_time tw\<close> \<open>i < next_time_world tw2\<close> fst_swap
        not_less not_less_zero snd_conv swap_simp tw2_def unchanged_until_next_time_world
        worldline_upd2_def)
      finally have "snd tw2 TEMP (i + 1) = snd tw2 IN i"
        by auto }
    ultimately have "snd tw2 TEMP (i + 1) = snd tw2 IN i"
      by auto
    thus "snd (next_time_world tw2, snd tw2) TEMP (i + 1) = snd (next_time_world tw2, snd tw2) IN i"
      by auto
  qed

  thus "inv_first
           (next_time_world tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)][ OUT, 1 :=\<^sub>2 beval_world_raw2 tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)] (Bsig TEMP)],
            snd tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)][ OUT, 1 :=\<^sub>2 beval_world_raw2 tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)] (Bsig TEMP)])"
    unfolding t'_def tw1_def tw2_def by auto
qed

lemma init_hoare2:
  "\<turnstile>\<^sub>I \<lbrace>\<lambda>tw. inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])\<rbrace>
          process {TEMP} : Bassign_trans OUT (Bsig TEMP) 1 \<lbrace>\<lambda>tw. inv_first (next_time_world tw, snd tw)\<rbrace>"
  apply (rule SingleI, rule Assign2_altI, rule, rule, assumption)
  done

theorem init_preserves_inv_first:
  " init_sim_hoare (\<lambda>tw. fst tw = 0) two_inverter inv_first"
  unfolding two_inverter_def
  apply (rule AssignI)
  apply (rule ParallelI[where R="\<lambda>tw. inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd  tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])"])
    apply (rule init_hoare1)
   apply (rule init_hoare2)
  by (auto simp add: conc_stmt_wf_def)

lemma init_hoare3:
  "\<turnstile>\<^sub>I \<lbrace>\<lambda>tw. get_time tw = 0\<rbrace>  process {IN} : Bassign_trans TEMP (Bsig IN) 1 \<lbrace>inv_second\<rbrace>"
proof (rule SingleI, rule Assign2_altI, rule, rule)
  fix tw :: "nat \<times> (sig \<Rightarrow> nat \<Rightarrow> bool)"
  assume "fst tw = 0"
  let ?tw = "tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)]"
  have "fst tw = fst ?tw"
    unfolding worldline_upd2_def worldline_upd_def by auto
  thus "inv_second tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)]"
    using \<open>fst tw = 0\<close> unfolding inv_second_def by auto
qed

lemma init_hoare4:
  "\<turnstile>\<^sub>I \<lbrace>inv_second\<rbrace>  
        process {TEMP} : Bassign_trans OUT (Bsig TEMP) 1 
      \<lbrace>\<lambda>tw. inv_second (next_time_world tw, snd tw)\<rbrace>"
  apply (rule SingleI)
  apply (rule Assign2_altI)
proof (rule)+
  fix tw
  assume "inv_second tw"
  define tw' where "tw' = tw [OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]"
  have "fst tw < next_time_world tw'"
    using next_time_world_at_least 
    by (metis fst_conv tw'_def worldline_upd2_def)
  have "inv_second (next_time_world tw', snd tw')"
    unfolding inv_second_def
  proof (rule, rule)
    fix i
    assume "i < fst (next_time_world tw', snd tw')"
    hence "i < next_time_world tw'"
      by auto
    hence "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw' - 1 \<or> i = next_time_world tw' - 1"
      by linarith
    moreover
    { assume "i < fst tw"
      hence "snd tw' OUT (i + 1) = snd tw OUT (i + 1)"
        unfolding tw'_def  by (simp add: worldline_upd2_before_dly)
      also have "... = snd tw TEMP i"
        using \<open>inv_second tw\<close> \<open>i < fst tw\<close> unfolding inv_second_def by auto
      also have "... = snd tw' TEMP i"
        unfolding tw'_def  by (simp add: worldline_upd2_def worldline_upd_def)
      finally have "snd tw' OUT (i + 1) = snd tw' TEMP i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < next_time_world tw' - 1"
      hence "snd tw' OUT (i + 1) = snd tw TEMP (fst tw)"
        unfolding tw'_def 
        by (metis Suc_eq_plus1 Suc_less_eq beval_world_raw2_Bsig diff_is_0_eq' less_numeral_extra(3)
        snd_conv worldline_upd2_def worldline_upd_def zero_less_diff)
      also have "... = snd tw' TEMP (fst tw')"
        by (metis less_add_one prod.sel(1) tw'_def worldline_upd2_before_dly worldline_upd2_def)
      also have "... = snd tw' TEMP i"
        by (metis \<open>get_time tw \<le> i \<and> i < next_time_world tw' - 1\<close> \<open>i < next_time_world tw'\<close> snd_conv
        snd_swap swap_simp tw'_def unchanged_until_next_time_world worldline_upd2_def)
      finally have "snd tw' OUT (i + 1) = snd tw' TEMP i"
        by auto }
    moreover
    { assume "i = next_time_world tw' - 1"
      hence "snd tw' OUT (i + 1) = snd tw' OUT (next_time_world tw')"
        using \<open>i < next_time_world tw'\<close> by force
      also have "... = snd tw TEMP (fst tw)"
        unfolding tw'_def using \<open>fst tw < next_time_world tw'\<close> 
        by (simp add: beval_world_raw2_Bsig tw'_def worldline_upd2_def worldline_upd_def)
      also have "... = snd tw' TEMP (fst tw')"
        unfolding tw'_def  by (simp add: worldline_upd2_def worldline_upd_def)   
      also have "... = snd tw' TEMP i"
        by (metis One_nat_def Pair_inject Suc_lessI \<open>get_time tw < next_time_world tw'\<close> \<open>i <
        next_time_world tw'\<close> \<open>i = next_time_world tw' - 1\<close> add.right_neutral add_Suc_right
        less_diff_conv less_or_eq_imp_le not_less prod.collapse tw'_def
        unchanged_until_next_time_world worldline_upd2_def)
      finally have "snd tw' OUT (i + 1) = snd tw' TEMP i"
        by auto }
    ultimately have "snd tw' OUT (i + 1) = snd tw' TEMP i"
      by auto
    thus "snd (next_time_world tw', snd tw') OUT (i + 1) = snd (next_time_world tw', snd tw') TEMP i "
      by auto
  qed
  thus "inv_second (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)]) "
    unfolding tw'_def by auto
qed
   
theorem init_preserves_inv_second:
  " init_sim_hoare (\<lambda>tw. fst tw = 0) two_inverter inv_second"
  unfolding two_inverter_def
  apply (rule AssignI)
  apply (rule ParallelI[where R="inv_second"])
  apply (rule init_hoare3)
  apply (rule init_hoare4)
  unfolding conc_stmt_wf_def by auto

lemma init_hoare5:
  "\<turnstile>\<^sub>I \<lbrace>\<lambda>tw. True\<rbrace>  
          process {IN} : Bassign_trans TEMP (Bsig IN) 1
      \<lbrace>\<lambda>tw. inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])\<rbrace>"
  apply (rule SingleI)
  apply (rule Assign2_altI)
proof (rule, rule)
  fix tw
  define tw1 where "tw1 = tw [ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw  (Bsig IN)]"
  define tw2 where "tw2 = tw1[ OUT,  1 :=\<^sub>2 beval_world_raw2 tw1 (Bsig TEMP)]"
  define t' where "t' = next_time_world tw2"
  have "inv_first_hold (t', snd tw2)"
    unfolding inv_first_hold_def
  proof (rule, rule, rule)
    have "fst tw < t'"
      unfolding t'_def using next_time_world_at_least 
      by (metis prod.sel(1) tw1_def tw2_def worldline_upd2_def)
    fix i
    assume "disjnt {IN} (event_of (t', snd tw2))"
    assume "fst (t', snd tw2) \<le> i"
    hence "t' \<le> i"
      by auto
    have "snd tw2 TEMP (i + 1) = snd tw1 TEMP (i + 1)"
      unfolding tw2_def  by (simp add: worldline_upd2_def worldline_upd_def)
    also have "... = snd tw IN (fst tw)"
      unfolding tw1_def using \<open>fst tw < t'\<close> \<open>t' \<le> i\<close> 
      by (metis (no_types, lifting) Suc_eq_plus1 beval_world_raw2_Bsig discrete le_Suc_eq
      less_le_trans not_less snd_conv worldline_upd2_def worldline_upd_def)
    also have "... = snd tw2 IN (fst tw2)"
      by (metis fst_conv less_add_one tw1_def tw2_def worldline_upd2_before_dly worldline_upd2_def)
    also have "... = snd tw2 IN (t' - 1)"
      unfolding t'_def  using unchanged_until_next_time_world 
      by (metis Suc_diff_1 diff_less gr_implies_not_zero less_Suc_eq_le nat_neq_iff
      next_time_world_at_least zero_less_one)
    also have "... = snd tw2 IN t'"
      using \<open>disjnt {IN} (event_of (t', snd tw2))\<close> unfolding event_of_alt_def 
      using \<open>get_time tw < t'\<close> by auto
    finally have "snd tw2 TEMP (i + 1) = snd tw2 IN t'"
      by auto
    thus "snd (t', snd tw2) TEMP (i + 1) = snd (t', snd tw2) IN (get_time (t', snd tw2))"
      by auto
  qed
  thus "inv_first_hold
           (next_time_world tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)][ OUT, 1 :=\<^sub>2 beval_world_raw2 tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)] (Bsig TEMP)],
            snd tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)][ OUT, 1 :=\<^sub>2 beval_world_raw2 tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)] (Bsig TEMP)])"
    unfolding t'_def tw2_def tw1_def by auto
qed

lemma init_hoare6:
  "\<turnstile>\<^sub>I \<lbrace>\<lambda>tw. inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])\<rbrace>
          process {TEMP} : Bassign_trans OUT (Bsig TEMP) 1 
      \<lbrace>\<lambda>tw. inv_first_hold (next_time_world tw, snd tw)\<rbrace>"
  apply (rule SingleI)
  apply (rule Assign2_altI)
  apply simp
  done
  
theorem init_preserves_inv_first_hold:
  "init_sim_hoare (\<lambda>tw. True) two_inverter inv_first_hold"
  unfolding two_inverter_def
  apply (rule AssignI)
  apply (rule ParallelI[where R="\<lambda>tw. inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd  tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])"])
    apply (rule init_hoare5)
   apply (rule init_hoare6)
  unfolding conc_stmt_wf_def by (auto)

lemma init_hoare7:
  " \<turnstile>\<^sub>I \<lbrace>\<lambda>tw. True\<rbrace>  
          process {IN} : Bassign_trans TEMP (Bsig IN) 1
       \<lbrace>\<lambda>tw. inv_second_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])\<rbrace>"
proof (rule SingleI, rule Assign2_altI, rule, rule)
  fix tw
  define tw1 where "tw1 = tw [ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)]"
  define tw2 where "tw2 = tw1[ OUT,  1 :=\<^sub>2 beval_world_raw2 tw1 (Bsig TEMP)]"
  define t' where "t' = next_time_world tw2"
  have "inv_second_hold (t', snd tw2)"
    unfolding inv_second_hold_def
  proof (rule, rule, rule)
    fix i
    assume "disjnt {TEMP} (event_of (t', snd tw2))"
    assume "fst (t', snd tw2) \<le> i"
    hence "t' \<le> i"
      by auto
    moreover have "fst tw < t'"
      unfolding t'_def using next_time_world_at_least 
      by (metis fst_conv tw1_def tw2_def worldline_upd2_def)
    ultimately have "fst tw < i + 1"
      by auto
    hence "snd tw2 OUT (i + 1) = snd tw1 TEMP (fst tw1)"
      unfolding tw2_def 
      by (simp add: beval_world_raw2_Bsig tw1_def worldline_upd2_def worldline_upd_def)
    also have "... = snd tw2 TEMP (fst tw2)"
      by (simp add: tw2_def worldline_upd2_def worldline_upd_def)
    also have "... = snd tw2 TEMP (t' - 1)"
      using unchanged_until_next_time_world 
      by (metis Pair_inject Suc_diff_1 \<open>get_time tw < t'\<close> diff_less gr_implies_not_zero le_Suc_eq
      less_imp_le_nat nat_neq_iff prod.collapse t'_def tw1_def tw2_def worldline_upd2_def
      zero_less_one)
    also have "... = snd tw2 TEMP t'"
      using \<open>disjnt {TEMP} (event_of (t', snd tw2))\<close> unfolding event_of_alt_def 
      using \<open>get_time tw < t'\<close> by auto
    finally have "snd tw2 OUT (i + 1) \<longleftrightarrow> snd tw2 TEMP t'"
      by auto
    thus "snd (t', snd tw2) OUT (i + 1) = snd (t', snd tw2) TEMP (get_time (t', snd tw2))"
      by auto
  qed
  thus "inv_second_hold
           (next_time_world tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)][ OUT, 1 :=\<^sub>2 beval_world_raw2 tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)] (Bsig TEMP)],
            snd tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)][ OUT, 1 :=\<^sub>2 beval_world_raw2 tw[ TEMP, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN)] (Bsig TEMP)])"
    unfolding tw1_def tw2_def t'_def by auto
qed

lemma init_hoare8:
  "\<turnstile>\<^sub>I \<lbrace>\<lambda>tw. inv_second_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])\<rbrace>
          process {TEMP} : Bassign_trans OUT (Bsig TEMP) 1 
      \<lbrace>\<lambda>tw. inv_second_hold (next_time_world tw, snd tw)\<rbrace>"
  apply (rule SingleI)
  apply (rule Assign2_altI)
  by auto

theorem init_preserves_inv_second_hold:
  "init_sim_hoare (\<lambda>tw. True) two_inverter inv_second_hold"
  unfolding two_inverter_def
  apply (rule AssignI)
  apply (rule ParallelI[where R="\<lambda>tw. inv_second_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)], snd  tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig TEMP)])"])
    apply (rule init_hoare7)
   apply (rule init_hoare8)
  unfolding conc_stmt_wf_def by auto

corollary init_preserves_invs:
  "init_sim_hoare (\<lambda>tw. fst tw = 0) two_inverter (\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw)"
  by (auto intro!: ConjI_sim 
         simp add: init_preserves_inv_first init_preserves_inv_second 
                   ConseqI_sim[OF _ init_preserves_inv_first_hold] 
                   ConseqI_sim[OF _ init_preserves_inv_second_hold])

lemma 
  assumes "sim_fin w (i + 1) two_inverter tw'"
  shows "snd tw' TEMP (i + 1) \<longleftrightarrow> snd tw' IN i"
proof -
  obtain tw where "init_sim (0, w) two_inverter = tw" and  "tw, i + 1, two_inverter \<Rightarrow>\<^sub>S tw'" 
    using premises_sim_fin_obt[OF assms] by auto
  hence "i + 1 < fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf two_inverter"
    unfolding conc_stmt_wf_def two_inverter_def by auto
  moreover have "nonneg_delay_conc two_inverter"
    unfolding two_inverter_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0) two_inverter (\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw)"
    using init_sim_hoare_soundness[OF init_preserves_invs] by auto
  hence "inv_first tw" and "inv_first_hold tw" and "inv_second tw" and "inv_second_hold tw"
    using \<open>init_sim (0, w) two_inverter = tw\<close> fst_conv unfolding init_sim_valid_def 
    by fastforce+ 
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw\<rbrace> two_inverter \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw\<rbrace>"
    using conc_sim_soundness[OF sim_correctness_two_inverter2] \<open>conc_stmt_wf two_inverter\<close> \<open>nonneg_delay_conc two_inverter\<close>
    by auto                               
  ultimately have "inv_first tw'"
    using \<open>tw, i + 1, two_inverter \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'.  snd tw' TEMP (i + 1) \<longleftrightarrow> snd tw' IN i"
    unfolding inv_first_def by auto
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed

lemma 
  assumes "sim_fin w (i + 1) two_inverter tw'"
  shows "snd tw' OUT (i + 1) \<longleftrightarrow> snd tw' TEMP i"
proof -
  obtain tw where "init_sim (0, w) two_inverter = tw" and  "tw, i + 1, two_inverter \<Rightarrow>\<^sub>S tw'" 
    using premises_sim_fin_obt[OF assms] by auto
  hence "i + 1 < fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf two_inverter"
    unfolding conc_stmt_wf_def two_inverter_def by auto
  moreover have "nonneg_delay_conc two_inverter"
    unfolding two_inverter_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0) two_inverter (\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw)"
    using init_sim_hoare_soundness[OF init_preserves_invs] by auto
  hence "inv_first tw" and "inv_first_hold tw" and "inv_second tw" and "inv_second_hold tw"
    using \<open>init_sim (0, w) two_inverter = tw\<close> fst_conv unfolding init_sim_valid_def 
    by fastforce+ 
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw\<rbrace> two_inverter \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw\<rbrace>"
    using conc_sim_soundness[OF sim_correctness_two_inverter2] \<open>conc_stmt_wf two_inverter\<close> \<open>nonneg_delay_conc two_inverter\<close>
    by auto                               
  ultimately have "inv_second tw'"
    using \<open>tw, i + 1, two_inverter \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'.  snd tw' OUT (i + 1) \<longleftrightarrow> snd tw' TEMP i"
    unfolding inv_second_def by auto
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed

end