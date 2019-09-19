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

lemma potential_tyenv:
  assumes "conc_wt \<Gamma> two_inverter"
  shows "\<exists>ki len. \<Gamma> IN = Bty \<and> \<Gamma> TEMP = Bty \<and> \<Gamma> OUT = Bty
            \<or> \<Gamma> IN = Lty ki len \<and> \<Gamma> TEMP = Lty ki len \<and> \<Gamma> OUT = Lty ki len"
  using assms unfolding two_inverter_def
proof (rule conc_wt_cases(2))
  assume "conc_wt \<Gamma> ( process {IN} : Bassign_trans TEMP (Bsig IN) 1)"
  hence "seq_wt \<Gamma> (Bassign_trans TEMP (Bsig IN) 1)"
    by blast
  hence "bexp_wt \<Gamma> (Bsig IN) (\<Gamma> TEMP)"
    by blast
  hence "\<Gamma> TEMP = \<Gamma> IN"
    by (rule bexp_wt_cases_all) auto
  assume "conc_wt \<Gamma> ( process {TEMP} : Bassign_trans OUT (Bsig TEMP) 1)"
  hence "seq_wt \<Gamma> (Bassign_trans OUT (Bsig TEMP) 1)"
    by blast
  hence "bexp_wt \<Gamma> (Bsig TEMP) (\<Gamma> OUT)"
    by blast
  hence "\<Gamma> OUT = \<Gamma> TEMP"
    by (rule bexp_wt_cases_all) auto
  obtain ki len where "\<Gamma> TEMP = Bty \<or> \<Gamma> TEMP = Lty ki len"
    using ty.exhaust by meson
  thus ?thesis
    using \<open>\<Gamma> OUT = \<Gamma> TEMP\<close> \<open>\<Gamma> TEMP = \<Gamma> IN\<close> by auto
qed

\<comment> \<open>the first invariant for double inverter\<close>
definition inv_first :: "sig assn2" where
  "inv_first \<equiv> (\<lambda>tw. \<forall>i < fst tw. wline_of tw TEMP (i + 1) = wline_of tw IN i)"

\<comment> \<open>the second invariant for double inverter\<close>
definition inv_second :: "sig assn2" where
  "inv_second \<equiv> (\<lambda>tw. \<forall>i < fst tw. wline_of tw OUT (i + 1) = wline_of tw TEMP i)"

definition inv_first_hold :: "sig assn2" where
  "inv_first_hold \<equiv> (\<lambda>tw. disjnt {IN} (event_of tw) \<longrightarrow>
                                         (\<forall>i \<ge> fst tw. wline_of tw TEMP (i + 1) = wline_of tw IN (fst tw)))"

definition inv_second_hold :: "sig assn2" where
  "inv_second_hold \<equiv> (\<lambda>tw. disjnt {TEMP} (event_of tw) \<longrightarrow>
                                         (\<forall>i \<ge> fst tw. wline_of tw OUT (i + 1) = wline_of tw TEMP (fst tw)))"

subsection \<open>First invariant hold at the next time\<close>

lemma inv_first_next_time:
  assumes "inv_first tw"
  defines "tw' \<equiv> tw[ TEMP, 1 :=\<^sub>2 wline_of tw IN (fst tw)]"
  shows  "inv_first (next_time_world tw', snd tw')"
proof -
  let ?t' = "next_time_world tw'"
  define v where "v = wline_of tw IN (fst tw)"
  have assms2: "beval_world_raw (snd tw) (fst tw) (Bsig IN) v"
    using assms(2) unfolding beval_world_raw2_def v_def
    by (metis beval_world_raw2_Bsig beval_world_raw2_def)
  have "fst tw' < ?t'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < ?t'"
    by auto
  have "\<forall>i<?t'. wline_of tw' TEMP (i + 1) = wline_of tw' IN i"
  proof (rule, rule)
    fix i
    assume "i < ?t'"
    have "i < fst tw \<or> fst tw \<le> i \<and> i < ?t' - 1 \<or> i = ?t' - 1"
      using next_time_world_at_least \<open>i < next_time_world tw'\<close> not_less by linarith
    moreover
    { assume "i < fst tw"
      hence "wline_of tw TEMP (i + 1) = wline_of tw IN i"
        using assms(1) unfolding inv_first_def by auto
      moreover have "wline_of tw TEMP (i + 1) = wline_of tw' TEMP (i + 1)" and "wline_of tw IN i = wline_of tw' IN i"
        using worldline_upd2_before_dly \<open>i < fst tw\<close> unfolding tw'_def
        by (metis add_mono1 trans_less_add1)+
      ultimately have "wline_of tw' TEMP (i + 1) = wline_of tw' IN i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < ?t' - 1"
      hence "wline_of tw' TEMP (i + 1) = wline_of tw' TEMP (fst tw + 1)"
        using unchanged_until_next_time_world
        by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
            le_less_trans less_diff_conv)
      have "wline_of tw' IN i = wline_of tw' IN (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i < ?t' - 1\<close>
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < next_time_world tw'\<close>)
      hence "wline_of tw' TEMP  (fst tw + 1) = wline_of tw' IN (fst tw)"
        by (metis assms2 beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic
        less_add_one tw'_def worldline_upd2_at_dly worldline_upd2_before_dly)
      hence "wline_of tw' TEMP (i + 1) = wline_of tw' IN i"
        using \<open>wline_of tw' IN i = wline_of tw' IN (get_time tw)\<close> \<open>wline_of tw' TEMP (i + 1) = wline_of tw' TEMP (get_time tw + 1)\<close>
        by simp }
    moreover
    { assume "i = ?t' - 1"
      hence "wline_of tw' TEMP (i + 1) = wline_of tw' TEMP ?t'"
        using \<open>i < ?t'\<close> by auto
      also have "... = wline_of tw' TEMP (fst tw + 1)"
        using \<open>fst tw < ?t'\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... = wline_of tw' IN (fst tw)"
        by (metis assms2 beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic
        less_add_one tw'_def worldline_upd2_at_dly worldline_upd2_before_dly)
      also have "... = wline_of tw' IN i"
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < get_time tw \<Longrightarrow> wline_of tw' TEMP (i + 1) = wline_of tw' IN i\<close>
            \<open>i < next_time_world tw'\<close> calculation not_less unchanged_until_next_time_world)
      finally have "wline_of tw' TEMP (i + 1) = wline_of tw' IN i"
        by auto }
    ultimately show "wline_of tw' TEMP (i + 1) = wline_of tw' IN i"
      by auto
  qed
  thus ?thesis
    unfolding inv_first_def by auto
qed

lemma seq_part_when_not_disjnt1:
  "\<turnstile> [\<lambda>tw. (inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)]
        Bassign_trans TEMP (Bsig IN) 1
     [inv_second]"
proof (intro Assign2_altI, rule, rule, rule)
  fix tw v
  assume "((inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)) \<and> beval_world_raw2 tw (Bsig IN) v"
  hence "inv_first tw" and "inv_second tw" and "inv_first_hold tw" and "inv_second_hold tw" and "\<not> disjnt {IN} (event_of tw)"
    and " beval_world_raw2 tw (Bsig IN) v"
    by auto
  define tw1 where "tw1 = tw [TEMP, 1 :=\<^sub>2 v]"
  define t' where "t' = next_time_world tw1"

  have "fst tw < t'"
    unfolding t'_def   by (metis fst_conv next_time_world_at_least tw1_def worldline_upd2_def)
  have "fst tw = fst tw1"
    by (simp add: tw1_def worldline_upd2_def)
  also have "... < next_time_world tw1"
    using next_time_world_at_least by  metis
  finally have "fst tw < next_time_world tw1"
    by auto

  have 0: "inv_second tw1" \<comment> \<open>unaffected invariant\<close>
    unfolding inv_second_def
  proof (rule, rule)
    fix i
    assume "i < fst tw1"
    hence "i < fst tw"
      using \<open>fst tw = fst tw1\<close> by auto
    have "wline_of tw1 OUT (i + 1) = wline_of tw OUT (i + 1)"
      unfolding tw1_def  by (meson \<open>i < get_time tw\<close> add_mono1 worldline_upd2_before_dly)
    also have "... = wline_of tw TEMP i"
      using \<open>inv_second tw\<close> \<open>i < fst tw\<close> unfolding inv_second_def by auto
    also have "... = wline_of tw1 TEMP i"
      unfolding tw1_def using \<open>i < fst tw\<close> by (metis trans_less_add1 worldline_upd2_before_dly)
    finally show "wline_of tw1 OUT (i + 1) = wline_of tw1 TEMP i"
      by auto
  qed
  thus "inv_second tw[ TEMP, 1 :=\<^sub>2 v] "
    unfolding tw1_def by auto
qed

lemma seq_part_when_not_disjnt2:
  "\<turnstile> [\<lambda>tw. (inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)]
        Bassign_trans TEMP (Bsig IN) 1
     [\<lambda>tw.  inv_first (next_time_world tw, snd tw)]"
proof (intro Assign2_altI, rule, rule, rule)
  fix tw v
  assume "((inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)) \<and> beval_world_raw2 tw (Bsig IN) v"
  hence "inv_first tw" and "inv_second tw" and "inv_first_hold tw" and "inv_second_hold tw" and "\<not> disjnt {IN} (event_of tw)"
    and " beval_world_raw2 tw (Bsig IN) v"
    by auto
  define tw1 where "tw1 = tw [TEMP, 1 :=\<^sub>2 v]"
  then obtain v' where "beval_world_raw2 tw1 (Bsig TEMP) v'"
    by (meson beval_world_raw2_Bsig)
  define tw2 where "tw2 = tw1[OUT, 1 :=\<^sub>2 v']"
  define t' where "t' = next_time_world tw1"

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
      hence "wline_of tw1 TEMP (i + 1) =  wline_of tw TEMP (i + 1)"
        unfolding tw1_def  by (meson add_mono1 worldline_upd2_before_dly)
      also have "... = wline_of tw IN i"
        using \<open>inv_first tw\<close> \<open>i < fst tw\<close> unfolding inv_first_def by auto
      also have "... = wline_of tw1 IN i"
        unfolding tw1_def  by (metis \<open>i < get_time tw\<close> add.right_neutral add_mono_thms_linordered_field(5)
        worldline_upd2_before_dly zero_less_one)
      finally have "wline_of tw1 TEMP (i + 1) = wline_of tw1 IN i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < t' - 1"
      hence "wline_of tw1 TEMP (i + 1) = wline_of tw1 TEMP (fst tw + 1)"
        using unchanged_until_next_time_world
        unfolding `fst tw = fst tw1`  t'_def
        by (metis (no_types, lifting) One_nat_def Suc_lessI Suc_less_eq \<open>get_time tw < t'\<close> \<open>get_time
        tw = get_time tw1\<close> add.right_neutral add_Suc_right diff_is_0_eq' le_Suc_eq le_add1
        less_diff_conv t'_def zero_less_diff)
      also have "... = wline_of tw IN (fst tw)"
        unfolding tw1_def
        by (metis \<open>beval_world_raw2 tw (Bsig IN) v\<close> beval_world_raw2_Bsig beval_world_raw2_def
        beval_world_raw_deterministic worldline_upd2_at_dly)
      also have "... = wline_of tw1 IN (fst tw)"
        unfolding tw1_def by (metis less_add_one worldline_upd2_before_dly)
      also have "... = wline_of tw1 IN i"
        using unchanged_until_next_time_world
        unfolding `fst tw = fst tw1`  t'_def
        by (metis \<open>get_time tw = get_time tw1\<close> \<open>get_time tw \<le> i \<and> i < t' - 1\<close> \<open>i < t'\<close> t'_def)
      finally have "wline_of tw1 TEMP (i + 1) = wline_of tw1 IN i"
        by auto }
    moreover
    { assume "i = t' - 1"
      hence "wline_of tw1 TEMP (i + 1) = wline_of tw1 TEMP t'"
        using \<open>i < t'\<close> by force
      also have "... = wline_of tw1 TEMP (fst tw + 1)"
        unfolding t'_def using \<open>fst tw < t'\<close>
        by (simp add: t'_def tw1_def worldline_upd2_def worldline_upd_def)
      also have "... = wline_of tw IN (fst tw)"
        unfolding tw1_def
        by (metis \<open>beval_world_raw2 tw (Bsig IN) v\<close> beval_world_raw2_Bsig beval_world_raw2_def
        beval_world_raw_deterministic worldline_upd2_at_dly)
      also have "... = wline_of tw1 IN (fst tw)"
        unfolding tw1_def  by (metis less_add_one worldline_upd2_before_dly)
      also have "... = wline_of tw1 IN i"
        by (metis \<open>get_time tw = get_time tw1\<close> \<open>i < get_time tw \<Longrightarrow> wline_of tw1 TEMP (i + 1) =
        wline_of tw1 IN i\<close> \<open>i < t'\<close> calculation not_less t'_def unchanged_until_next_time_world)
      finally have "wline_of tw1 TEMP (i + 1) = wline_of tw1 IN i"
        by auto }
    ultimately have "wline_of tw1 TEMP (i + 1) = wline_of tw1 IN i"
      by auto
    thus "wline_of (t', snd tw1) TEMP (i + 1) = wline_of (t', snd tw1) IN i"
      by auto
  qed
  thus " inv_first (next_time_world tw[ TEMP, 1 :=\<^sub>2 v], snd tw[ TEMP, 1 :=\<^sub>2 v])"
    unfolding tw1_def tw2_def t'_def by auto
qed

lemma seq_part_when_not_disjnt3:
  "\<turnstile> [\<lambda>tw. (inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)]
        Bassign_trans TEMP (Bsig IN) 1
     [inv_second_hold]"
proof (intro Assign2_altI, rule, rule, rule)
  fix tw v
  assume "((inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)) \<and> beval_world_raw2 tw (Bsig IN) v"
  hence "inv_first tw" and "inv_second tw" and "inv_first_hold tw" and "inv_second_hold tw" and "\<not> disjnt {IN} (event_of tw)"
    and " beval_world_raw2 tw (Bsig IN) v"
    by auto
  define tw1 where "tw1 = tw [TEMP, 1 :=\<^sub>2 v]"
  then obtain v' where "beval_world_raw2 tw1 (Bsig TEMP) v'"
    by (meson beval_world_raw2_Bsig)
  define tw2 where "tw2 = tw1[OUT, 1 :=\<^sub>2 v']"
  define t' where "t' = next_time_world tw1"

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

  have "beval_world_raw (snd tw1) (fst tw1) (Bsig TEMP) v'"
    using \<open>beval_world_raw2 tw1 (Bsig TEMP) v'\<close> unfolding beval_world_raw2_def by auto

  \<comment> \<open>second unaffected invariant\<close>
  have 1: "inv_second_hold tw1"
    unfolding inv_second_hold_def
  proof (rule, rule, rule)
    fix i
    have "get_time tw = get_time tw[ TEMP, 1 :=\<^sub>2 v]"
      using \<open>fst tw = fst tw1\<close>  unfolding tw1_def by auto
    assume "disjnt {TEMP} (event_of tw1)"
    hence "disjnt {TEMP} (event_of tw)"
      unfolding tw1_def  event_of_alt_def sym[OF \<open>get_time tw = get_time tw[ TEMP, 1 :=\<^sub>2 v]\<close>]
      worldline_upd2_def worldline_upd_def by auto
    assume "fst tw1 \<le> i"
    hence "fst tw \<le> i"
      using \<open>fst tw = fst tw1\<close> by auto
    hence "wline_of tw OUT (i + 1) = wline_of tw TEMP (fst tw)"
      using `inv_second_hold tw` \<open>disjnt {TEMP} (event_of tw)\<close> unfolding inv_second_hold_def
      by auto
    moreover have "wline_of tw OUT (i + 1) = wline_of tw1 OUT (i + 1)" and "wline_of tw TEMP (fst tw) = wline_of tw1 TEMP (fst tw)"
      by (simp add: tw1_def worldline_upd2_def worldline_upd_def)+
    ultimately show "wline_of tw1 OUT (i + 1) = wline_of tw1 TEMP (get_time tw1)"
      using \<open>fst tw = fst tw1\<close> by auto
  qed

  thus "inv_second_hold tw[ TEMP, 1 :=\<^sub>2 v]"
    unfolding tw1_def by auto
qed

lemma seq_part_when_not_disjnt4:
  "\<turnstile> [\<lambda>tw. (inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)]
        Bassign_trans TEMP (Bsig IN) 1
     [\<lambda>tw. inv_first_hold (next_time_world tw, snd tw)]"
proof (intro Assign2_altI, rule, rule, rule)
  fix tw v
  assume "((inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)) \<and> beval_world_raw2 tw (Bsig IN) v"
  hence "inv_first tw" and "inv_second tw" and "inv_first_hold tw" and "inv_second_hold tw" and "\<not> disjnt {IN} (event_of tw)"
    and " beval_world_raw2 tw (Bsig IN) v"
    by auto
  define tw1 where "tw1 = tw [TEMP, 1 :=\<^sub>2 v]"
  then obtain v' where "beval_world_raw2 tw1 (Bsig TEMP) v'"
    by (meson beval_world_raw2_Bsig)
  define tw2 where "tw2 = tw1[OUT, 1 :=\<^sub>2 v']"
  define t' where "t' = next_time_world tw1"

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

  have 5: "inv_first_hold (t', snd tw1)"
    unfolding inv_first_hold_def
  proof (rule, rule, rule)
    fix i
    assume "disjnt {IN} (event_of (t', snd tw1))"
    assume "fst (t', snd tw1) \<le> i"
    hence "t' \<le> i"
      by auto
    hence "wline_of tw1 TEMP (i + 1) = wline_of tw IN (fst tw)"
      using `fst tw < t'`
      by (smt \<open>beval_world_raw2 tw (Bsig IN) v\<close> add_less_cancel_right beval_world_raw2_Bsig
      beval_world_raw2_def beval_world_raw_deterministic less_le_trans o_apply order.asym snd_conv
      tw1_def worldline_upd2_def worldline_upd_def)
    also have "... = wline_of tw1 IN (fst tw)"
      by (metis less_add_one tw1_def worldline_upd2_before_dly)
    also have "... = wline_of tw1 IN (t' - 1)"
      unfolding t'_def `fst tw < t'` using unchanged_until_next_time_world
      by (metis Suc_diff_1 \<open>get_time tw < t'\<close> \<open>get_time tw = get_time tw1\<close> diff_less
      gr_implies_not_zero le_Suc_eq less_imp_le_nat nat_neq_iff t'_def zero_less_one)
    also have "... = wline_of tw1 IN t'"
      using \<open>disjnt {IN} (event_of (t', snd tw1))\<close> unfolding event_of_alt_def
      using \<open>get_time tw < t'\<close> by auto
    finally show "wline_of (t', snd tw1) TEMP (i + 1) = wline_of (t', snd tw1) IN (get_time (t', snd tw1))"
      by auto
  qed
  thus " inv_first_hold (next_time_world tw[ TEMP, 1 :=\<^sub>2 v], snd tw[ TEMP, 1 :=\<^sub>2 v])"
    unfolding tw1_def t'_def by auto
qed

lemma seq_part_when_not_disjnt5:
  "\<turnstile> [\<lambda>tw. (inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)]
        Bassign_trans TEMP (Bsig IN) 1
     [\<lambda>tw.  let x = wline_of tw TEMP (fst tw) in inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 x],  snd tw[ OUT, 1 :=\<^sub>2 x])]"
proof (intro Assign2_altI, rule, rule, rule)
  fix tw v
  assume "((inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)) \<and> beval_world_raw2 tw (Bsig IN) v"
  hence "inv_first tw" and "inv_second tw" and "inv_first_hold tw" and "inv_second_hold tw" and "\<not> disjnt {IN} (event_of tw)"
    and " beval_world_raw2 tw (Bsig IN) v"
    by auto
  define tw1 where "tw1 = tw [TEMP, 1 :=\<^sub>2 v]"
  then obtain v' where "beval_world_raw2 tw1 (Bsig TEMP) v'"
    by (meson beval_world_raw2_Bsig)
  define tw2 where "tw2 = tw1[OUT, 1 :=\<^sub>2 v']"
  define t' where "t' = next_time_world tw1"
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
      have "wline_of tw2 TEMP (i + 1) = wline_of tw TEMP (i + 1)"
        by (metis \<open>get_time tw = get_time tw1\<close> \<open>i < get_time tw\<close> add_mono1 tw1_def tw2_def
        worldline_upd2_before_dly)
      also have "... = wline_of tw IN i"
        using \<open>inv_first tw\<close> \<open>i < fst tw\<close> unfolding inv_first_def by auto
      also have "... = wline_of tw2 IN i"
        by (metis \<open>get_time tw = get_time tw1\<close> \<open>i < get_time tw\<close> add.right_neutral
        add_mono_thms_linordered_field(5) tw1_def tw2_def worldline_upd2_before_dly zero_less_one)
      finally have "wline_of tw2 TEMP (i + 1) = wline_of tw2 IN i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < next_time_world tw2 - 1"
      hence "fst tw2 \<le> i \<and> i < next_time_world tw2 - 1"
        by (simp add: \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 = get_time tw2\<close>)
      hence "wline_of tw2 TEMP (i + 1) = wline_of tw2 TEMP (fst tw2 + 1)"
        by (metis (no_types, lifting) One_nat_def Suc_less_eq \<open>get_time tw2 < next_time_world tw2\<close>
        add.right_neutral add_Suc_right le_Suc_eq less_diff_conv not_less
        unchanged_until_next_time_world)
      also have "... = wline_of tw1 TEMP (fst tw2 + 1)"
        by (metis \<open>get_time tw1 = get_time tw2\<close> sig.distinct(6) tw2_def worldline_upd2_at_dly_nonsig)
      also have "... = wline_of tw1 TEMP (fst tw + 1)"
        by (simp add: \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 = get_time tw2\<close>)
      also have "... = wline_of tw IN (fst tw) "
        unfolding tw1_def
        by (metis \<open>beval_world_raw2 tw (Bsig IN) v\<close> beval_world_raw2_Bsig beval_world_raw2_def
        beval_world_raw_deterministic worldline_upd2_at_dly)
      also have "... = wline_of tw1 IN (fst tw1)"
        by (metis \<open>get_time tw = get_time tw1\<close> less_add_one tw1_def worldline_upd2_before_dly)
      also have "... = wline_of tw2 IN (fst tw2)"
        by (metis \<open>get_time tw1 = get_time tw2\<close> less_add_one tw2_def worldline_upd2_before_dly)
      also have "... = wline_of tw2 IN i"
        using \<open>get_time tw2 \<le> i \<and> i < next_time_world tw2 - 1\<close> \<open>i < next_time_world tw2\<close>
        unchanged_until_next_time_world by metis
      finally have "wline_of tw2 TEMP (i + 1) = wline_of tw2 IN i"
        by auto }
    moreover
    { assume "i = next_time_world tw2 - 1"
      hence "wline_of tw2 TEMP (i + 1) = wline_of tw2 TEMP (next_time_world tw2)"
        using \<open>i < next_time_world tw2\<close> by force
      also have "... = wline_of tw2 TEMP (fst tw2 + 1)"
        unfolding tw2_def
        by (smt \<open>get_time tw < next_time_world tw2\<close> \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 =
        get_time tw2\<close> comp_apply discrete leD less_imp_le_nat snd_conv tw1_def tw2_def
        worldline_upd2_def worldline_upd_def)
      also have "... = wline_of tw2 TEMP (fst tw1 + 1)"
        by (simp add: \<open>get_time tw1 = get_time tw2\<close>)
      also have "... = wline_of tw1 TEMP (fst tw1 + 1)"
        unfolding tw2_def by (metis sig.distinct(6) worldline_upd2_at_dly_nonsig)
      also have "... = wline_of tw IN (fst tw)"
        unfolding tw1_def
        by (metis \<open>beval_world_raw2 tw (Bsig IN) v\<close> \<open>get_time tw = get_time tw1\<close>
        beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic tw1_def
        worldline_upd2_at_dly)
      also have "... = wline_of tw1 IN (fst tw)"
        by (metis less_add_one tw1_def worldline_upd2_before_dly)
      also have "... = wline_of tw2 IN (fst tw2)"
        by (metis \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 = get_time tw2\<close> less_add_one tw2_def
        worldline_upd2_before_dly)
      also have "... = wline_of tw2 IN i"
        by (metis \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 = get_time tw2\<close> \<open>i < get_time tw \<Longrightarrow>
        wline_of tw2 TEMP (i + 1) = wline_of tw2 IN i\<close> \<open>i < next_time_world tw2\<close> calculation
        not_less unchanged_until_next_time_world)
      finally have "wline_of tw2 TEMP (i + 1) = wline_of tw2 IN i"
        by auto }
    ultimately have "wline_of tw2 TEMP (i + 1) = wline_of tw2 IN i"
      by auto
    thus " wline_of (next_time_world tw2, snd tw2) TEMP (i + 1) = wline_of (next_time_world tw2, snd tw2) IN i"
      by auto
  qed
  thus "let xa = wline_of tw[ TEMP, 1 :=\<^sub>2 v] TEMP (get_time tw[ TEMP, 1 :=\<^sub>2 v])
       in inv_first (next_time_world tw[ TEMP, 1 :=\<^sub>2 v][ OUT, 1 :=\<^sub>2 xa], snd tw[ TEMP, 1 :=\<^sub>2 v][ OUT, 1 :=\<^sub>2 xa])"
    unfolding tw2_def tw1_def using \<open>beval_world_raw2 tw1 (Bsig TEMP) v'\<close> tw1_def
    by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)
qed

lemma seq_part_when_not_disjnt6:
  "\<turnstile> [\<lambda>tw. (inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)]
        Bassign_trans TEMP (Bsig IN) 1
     [\<lambda>tw. let x = wline_of tw TEMP (fst tw) in
                         inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 x],  snd tw[ OUT, 1 :=\<^sub>2 x])]"
proof (intro Assign2_altI, rule, rule, rule)
  fix tw v
  assume "((inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)) \<and> beval_world_raw2 tw (Bsig IN) v"
  hence "inv_first tw" and "inv_second tw" and "inv_first_hold tw" and "inv_second_hold tw" and "\<not> disjnt {IN} (event_of tw)"
    and " beval_world_raw2 tw (Bsig IN) v"
    by auto
  define tw1 where "tw1 = tw [TEMP, 1 :=\<^sub>2 v]"
  then obtain v' where "beval_world_raw2 tw1 (Bsig TEMP) v'"
    by (meson beval_world_raw2_Bsig)
  define tw2 where "tw2 = tw1[OUT, 1 :=\<^sub>2 v']"
  define t' where "t' = next_time_world tw1"
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

  have 3: "inv_first_hold (next_time_world tw2, snd tw2)"
    unfolding inv_first_hold_def
  proof (rule, rule, rule)
    fix i
    assume "disjnt {IN} (event_of (next_time_world tw2, snd tw2))"
    assume "fst (next_time_world tw2, snd tw2) \<le> i"
    hence "next_time_world tw2 \<le> i" and "fst tw1 < i"
      using \<open>fst tw1 < next_time_world tw2\<close>  by auto
    hence "wline_of tw2 TEMP (i + 1) = wline_of tw1 TEMP (i + 1)"
      by (simp add: tw2_def worldline_upd2_def worldline_upd_def)
    also have "... = wline_of tw IN (fst tw)"
        unfolding tw1_def
        by (smt \<open>beval_world_raw2 tw (Bsig IN) v\<close> \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 < i\<close>
        beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic discrete
        dual_order.strict_trans2 less_add_one o_apply order.asym snd_conv worldline_upd2_def
        worldline_upd_def)
    also have "... = wline_of tw2 IN (fst tw2)"
      by (metis \<open>get_time tw = get_time tw1\<close> \<open>get_time tw1 = get_time tw2\<close> less_add_one tw1_def tw2_def worldline_upd2_before_dly)
    also have "... = wline_of tw2 IN (next_time_world tw2 - 1)"
      using unchanged_until_next_time_world
      by (metis Suc_diff_1 \<open>get_time tw2 < next_time_world tw2\<close> diff_less gr_implies_not_zero le_Suc_eq less_imp_le_nat nat_neq_iff zero_less_one)
    also have "... = wline_of tw2 IN (next_time_world tw2)"
      using \<open>disjnt {IN} (event_of (next_time_world tw2, snd tw2))\<close>
      unfolding event_of_alt_def  using \<open>get_time tw2 < next_time_world tw2\<close> by auto
    finally have "wline_of tw2 TEMP (i + 1) = wline_of tw2 IN (next_time_world tw2)"
      by auto
    thus "wline_of (next_time_world tw2, snd tw2) TEMP (i + 1) =
          wline_of (next_time_world tw2, snd tw2) IN (get_time (next_time_world tw2, snd tw2))"
      by auto
  qed
  thus " let xa = wline_of tw[ TEMP, 1 :=\<^sub>2 v] TEMP (get_time tw[ TEMP, 1 :=\<^sub>2 v])
       in inv_first_hold (next_time_world tw[ TEMP, 1 :=\<^sub>2 v][ OUT, 1 :=\<^sub>2 xa], snd tw[ TEMP, 1 :=\<^sub>2 v][ OUT, 1 :=\<^sub>2 xa])"
    using \<open>beval_world_raw2 tw1 (Bsig TEMP) v'\<close> unfolding tw1_def tw2_def
    by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)
qed

lemma seq_part_when_not_disjnt:
  " \<turnstile> [\<lambda>tw. (inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw) \<and> \<not> disjnt {IN} (event_of tw)]
        Bassign_trans TEMP (Bsig IN) 1
      [\<lambda>tw. (let x = wline_of tw TEMP (fst tw) in inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 x], snd tw[ OUT, 1 :=\<^sub>2 x]))
          \<and> inv_first (next_time_world tw, snd tw)
          \<and> inv_second tw
          \<and> (let x = wline_of tw TEMP (fst tw) in inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 x], snd tw[ OUT, 1 :=\<^sub>2 x]))
          \<and> inv_first_hold (next_time_world tw, snd tw)
          \<and> inv_second_hold tw]"
  using seq_part_when_not_disjnt1 seq_part_when_not_disjnt2 seq_part_when_not_disjnt3
        seq_part_when_not_disjnt4 seq_part_when_not_disjnt5 seq_part_when_not_disjnt6
  by (intro Conj)

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
    hence "wline_of tw TEMP (i + 1) = wline_of tw IN i"
      using assms(1) unfolding inv_first_def by auto }
  moreover
  { assume "fst tw \<le> i"
    moreover have "(\<forall>i \<ge> fst tw. wline_of tw TEMP (i + 1) = wline_of tw IN (fst tw))"
      using assms(2-3) unfolding inv_first_hold_def by auto
    ultimately have "wline_of tw TEMP (i + 1) = wline_of tw IN (fst tw)"
      by auto
    also have "... = wline_of tw IN i"
      by (metis \<open>get_time tw \<le> i\<close> \<open>i < next_time_world tw\<close> unchanged_until_next_time_world)
    finally have "wline_of tw TEMP (i + 1) = wline_of tw IN i"
      by auto }
  ultimately have "wline_of tw TEMP (i + 1) = wline_of tw IN i"
    by auto
  thus "wline_of (next_time_world tw, snd tw) TEMP (i + 1) = wline_of (next_time_world tw, snd tw) IN i"
    by auto
qed

lemma inv_first_disjnt_next_time:
  assumes "inv_first tw" and "inv_first_hold tw" and "disjnt {IN} (event_of tw)"
  shows "let v = wline_of tw TEMP (fst tw) in inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])"
  unfolding inv_first_def Let_def
proof (rule, rule)
  fix i
  define v where "v = wline_of tw TEMP (fst tw)"
  assume "i<get_time (next_time_world tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)], snd tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)])"
  hence "i < next_time_world tw[ OUT, 1 :=\<^sub>2 v]"
    unfolding v_def by auto
  let ?tw = "tw[OUT, 1 :=\<^sub>2 v]"
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
    hence "wline_of ?tw TEMP (i + 1) = wline_of tw TEMP (i + 1)"
      by (meson add_mono1 worldline_upd2_before_dly)
    also have "... = wline_of tw IN i"
      using assms(1) unfolding inv_first_def using \<open>i < get_time tw\<close> by blast
    also have "... = wline_of ?tw IN i"
      by (metis \<open>i < get_time tw\<close> add.right_neutral add_mono_thms_linordered_field(5)
      worldline_upd2_before_dly zero_less_one)
    finally have "wline_of ?tw TEMP (i + 1) = wline_of ?tw IN i"
      by auto }
  moreover
  { assume "fst tw \<le> i"
    have "wline_of ?tw TEMP (i + 1) = wline_of tw TEMP (i + 1)"
      using \<open>i < next_time_world ?tw\<close> \<open>fst tw < next_time_world ?tw\<close>
      by (simp add: worldline_upd2_def worldline_upd_def)
    also have "... = wline_of tw IN i"
      using assms(2-3) unfolding inv_first_hold_def
      by (smt \<open>get_time tw \<le> i\<close> \<open>get_time tw[ OUT, 1 :=\<^sub>2 v] = get_time tw\<close> \<open>i < next_time_world tw[
      OUT, 1 :=\<^sub>2 v]\<close> comp_apply sig.distinct(3) snd_conv unchanged_until_next_time_world
      worldline_upd2_def worldline_upd_def)
    also have "... = wline_of ?tw IN i"
      by (simp add: worldline_upd2_def worldline_upd_def)
    finally have "wline_of ?tw TEMP (i + 1) = wline_of ?tw IN i"
      by auto }
  ultimately have "wline_of ?tw TEMP (i + 1) = wline_of ?tw IN i"
    by auto
  thus "wline_of (next_time_world tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)], snd tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)]) TEMP (i + 1) =
        wline_of (next_time_world tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)], snd tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)]) IN i"
    by (simp add: v_def)
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
  moreover have "(\<forall>i \<ge> fst tw. wline_of tw TEMP (i + 1) = wline_of tw IN (fst tw))"
    using assms unfolding inv_first_hold_def by auto
  ultimately have "wline_of tw TEMP (i + 1) = wline_of tw IN (fst tw)"
    by auto
  also have "... = wline_of tw IN (next_time_world tw - 1)"
    using unchanged_until_next_time_world
    by (metis Suc_diff_1 Suc_leI \<open>get_time tw < next_time_world tw\<close> diff_less le_0_eq
    less_imp_le_nat not_less zero_less_one)
  also have "... = wline_of tw IN (next_time_world tw)"
    using \<open>disjnt {IN} (event_of (next_time_world tw, snd tw))\<close>
    unfolding event_of_alt_def  using \<open>get_time tw < next_time_world tw\<close> by auto
  finally have "wline_of tw TEMP (i + 1) = wline_of tw IN (next_time_world tw)"
    by auto
  thus "wline_of (next_time_world tw, snd tw) TEMP (i + 1) =
                        wline_of (next_time_world tw, snd tw) IN (get_time (next_time_world tw, snd tw))"
    by auto
qed

lemma inv_first_hold_disjnt_next_time:
  assumes "inv_first_hold tw" and "disjnt {IN} (event_of tw)"
  shows "let v = wline_of tw TEMP (fst tw) in inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])"
  unfolding inv_first_hold_def Let_def
proof (rule, rule, rule)
  define v where "v = wline_of tw TEMP (fst tw)"
  let ?tw = "tw[OUT, 1 :=\<^sub>2 v]"
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
  have "wline_of ?tw TEMP (i + 1) = wline_of tw TEMP (i + 1)"
    by (simp add: worldline_upd2_def worldline_upd_def)
  also have "... = wline_of tw IN (fst tw)"
    using assms(1-2) \<open>fst tw < next_time_world ?tw\<close> \<open>next_time_world ?tw \<le> i\<close>
    unfolding inv_first_hold_def by auto
  also have "... = wline_of ?tw IN (fst tw)"
    by (metis less_add_one worldline_upd2_before_dly)
  also have "... = wline_of ?tw IN (fst ?tw)"
    by (simp add: \<open>get_time tw = get_time tw[ OUT, 1 :=\<^sub>2 v]\<close>)
  also have "... = wline_of ?tw IN (next_time_world ?tw - 1)"
    using unchanged_until_next_time_world
    by (smt \<open>get_time tw < next_time_world ?tw\<close> \<open>get_time tw = get_time ?tw\<close> diff_add diff_is_0_eq'
    discrete le_0_eq le_numeral_extra(4) less_le not_less)
  also have "... = wline_of ?tw IN (next_time_world ?tw)"
    using \<open>disjnt {IN} (event_of (next_time_world ?tw, snd ?tw))\<close>
    unfolding event_of_alt_def
    using \<open>get_time tw < next_time_world tw[ OUT, 1 :=\<^sub>2 v]\<close> by auto
  finally have "wline_of ?tw TEMP (i + 1) = wline_of ?tw IN (next_time_world ?tw)"
    by auto
  thus "wline_of (next_time_world tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)], snd tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)]) TEMP (i + 1) =
         wline_of (next_time_world tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)], snd tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)]) IN
          (get_time (next_time_world tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)], snd tw[ OUT, 1 :=\<^sub>2 wline_of tw TEMP (get_time tw)]))"
    unfolding v_def by auto
qed

lemma conc_next_time:
  "\<turnstile> \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw\<rbrace>
        process {IN} : Bassign_trans TEMP (Bsig IN) 1
     \<lbrace>\<lambda>tw. (let v = wline_of tw TEMP (fst tw) in inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v]))
         \<and> inv_first (next_time_world tw, snd tw)
         \<and> inv_second tw
         \<and> (let v = wline_of tw TEMP (fst tw) in inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v]))
         \<and> inv_first_hold (next_time_world tw, snd tw) \<and> inv_second_hold tw\<rbrace>"
  apply (rule Single)
   apply (rule seq_part_when_not_disjnt)
  using inv_first_disjnt_next_time inv_first_hold_disjnt_next_time
    inv_first_disjnt_next_time_no_process_later inv_first_hold_disjnt_next_time_no_process_later
  by auto

lemma snd_seq_part_when_not_disjnt:
  "\<turnstile> [\<lambda>tw. ((let v = wline_of tw TEMP (fst tw) in inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])) \<and>
              inv_first (next_time_world tw, snd tw) \<and>
              inv_second tw \<and>
            (let v = wline_of tw TEMP (fst tw) in inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])) \<and>
              inv_first_hold (next_time_world tw, snd tw) \<and> inv_second_hold tw) \<and>
             \<not> disjnt {TEMP} (event_of tw)]
       Bassign_trans OUT (Bsig TEMP) 1
       [\<lambda>tw. inv_first (next_time_world tw, snd tw) \<and>
             inv_second (next_time_world tw, snd tw) \<and> inv_first_hold (next_time_world tw, snd tw) \<and> inv_second_hold (next_time_world tw, snd tw)]"
proof (rule Assign2_altI, rule, rule, rule)
  fix tw v
  assume asm: "(((let v = wline_of tw TEMP (get_time tw) in inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])) \<and>
         inv_first (next_time_world tw, snd tw) \<and>
         inv_second tw \<and>
         (let v = wline_of tw TEMP (get_time tw) in inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])) \<and>
         inv_first_hold (next_time_world tw, snd tw) \<and> inv_second_hold tw) \<and>
        \<not> disjnt {TEMP} (event_of tw)) \<and>
       beval_world_raw2 tw (Bsig TEMP) v"
  define tw' where "tw' = tw[ OUT, 1 :=\<^sub>2 v]"
  define t' where "t' = next_time_world tw'"

  hence 0: "inv_first (t', snd tw')" and "inv_second tw" and 1: "inv_first_hold (t', snd tw')" and "inv_second_hold tw"
    and "\<not> disjnt {TEMP} (event_of tw)" and "beval_world_raw2 tw (Bsig TEMP) v"
    using asm beval_world_raw2_def beval_world_raw_deterministic
    unfolding t'_def tw'_def by (metis beval_world_raw2_Bsig)+

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
      hence "wline_of tw' OUT (i + 1) = wline_of tw OUT (i + 1)"
        by (metis add_mono1 tw'_def worldline_upd2_before_dly)
      also have "... = wline_of tw TEMP i"
        using \<open>inv_second tw\<close> \<open>i < fst tw\<close> unfolding inv_second_def by auto
      also have "... = wline_of tw' TEMP i"
        by (simp add: tw'_def worldline_upd2_def worldline_upd_def)
      finally have "wline_of tw' OUT (i + 1) = wline_of tw' TEMP i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < t' - 1"
      hence "fst tw' \<le> i \<and> i < t' - 1"
        by (simp add: \<open>get_time tw = get_time tw'\<close>)
      hence "wline_of tw' OUT (i + 1) = wline_of tw' OUT (fst tw' + 1)"
        by (metis (no_types, lifting) One_nat_def Suc_less_eq \<open>get_time tw' < t'\<close> add.right_neutral
        add_Suc_right le_Suc_eq less_diff_conv not_less t'_def unchanged_until_next_time_world)
      also have "... = wline_of tw' OUT (fst tw + 1)"
        using \<open>get_time tw = get_time tw'\<close> by auto
      also have "... = wline_of tw TEMP (fst tw) "
        unfolding tw'_def
        by (metis \<open>beval_world_raw2 tw (Bsig TEMP) v\<close> beval_world_raw2_Bsig beval_world_raw2_def
        beval_world_raw_deterministic worldline_upd2_at_dly)
      also have "... = wline_of tw' TEMP (fst tw')"
        by (metis \<open>get_time tw = get_time tw'\<close> less_add_one tw'_def worldline_upd2_before_dly)
      also have "... = wline_of tw' TEMP i"
        using \<open>get_time tw' \<le> i \<and> i < t' - 1\<close> \<open>i < t'\<close> t'_def unchanged_until_next_time_world
        by metis
      finally have "wline_of tw' OUT (i + 1) = wline_of tw' TEMP i"
        by auto }
    moreover
    { assume "i = t' - 1"
      hence "wline_of tw' OUT (i + 1) = wline_of tw' OUT t'"
        using \<open>i < t'\<close> by auto
      also have "... = wline_of tw TEMP (fst tw)"
        unfolding tw'_def using \<open>fst tw < t'\<close>
        by (smt \<open>beval_world_raw2 tw (Bsig TEMP) v\<close> beval_world_raw2_Bsig beval_world_raw2_def
        beval_world_raw_deterministic discrete leD o_apply snd_conv worldline_upd2_def
        worldline_upd_def)
      also have "... = wline_of tw' TEMP (fst tw')"
        by (metis \<open>get_time tw = get_time tw'\<close> less_add_one tw'_def worldline_upd2_before_dly)
      also have "... = wline_of tw' TEMP i"
        by (metis \<open>get_time tw = get_time tw'\<close> \<open>i < get_time tw \<Longrightarrow> wline_of tw' OUT (i + 1) =
        wline_of tw' TEMP i\<close> \<open>i < t'\<close> calculation not_less t'_def unchanged_until_next_time_world)
      finally have "wline_of tw' OUT (i + 1) = wline_of tw' TEMP i"
        by auto }
    ultimately have "wline_of tw' OUT (i + 1) = wline_of tw' TEMP i"
      using \<open>i < t'\<close> by fastforce
    thus "wline_of (t', snd tw') OUT (i + 1) = wline_of (t', snd tw') TEMP i"
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
    hence "beval_world_raw2 tw (Bsig TEMP) (wline_of tw' OUT (i + 1))"
      using `fst tw < t'` unfolding tw'_def worldline_upd2_def worldline_upd_def
      using \<open>beval_world_raw2 tw (Bsig TEMP) v\<close> by auto
    also have "... = wline_of tw TEMP (fst tw)"
      by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic calculation)
    also have "... = wline_of tw' TEMP (fst tw')"
      by (metis \<open>get_time tw = get_time tw'\<close> less_add_one tw'_def worldline_upd2_before_dly)
    also have "... = wline_of tw' TEMP (t' - 1)"
      using unchanged_until_next_time_world \<open>fst tw < t'\<close>
      by (metis Suc_diff_1 \<open>get_time tw = get_time tw'\<close> diff_less gr_implies_not_zero le_Suc_eq
      less_imp_le_nat nat_neq_iff t'_def zero_less_one)
    also have "... = wline_of tw' TEMP t'"
      using \<open>disjnt {TEMP} (event_of (t', snd tw'))\<close> unfolding event_of_alt_def
      using \<open>get_time tw < t'\<close> by auto
    finally have "wline_of tw' OUT (i + 1) = wline_of tw' TEMP t'"
      using \<open>wline_of tw TEMP (get_time tw) = wline_of tw' TEMP (get_time tw')\<close> \<open>wline_of tw' OUT (i
      + 1) = wline_of tw TEMP (get_time tw)\<close> \<open>wline_of tw' TEMP (get_time tw') = wline_of tw' TEMP
      (t' - 1)\<close> \<open>wline_of tw' TEMP (t' - 1) = wline_of tw' TEMP t'\<close> by auto
    thus "wline_of (t', snd tw') OUT (i + 1) = wline_of (t', snd tw') TEMP (get_time (t', snd tw'))"
      by auto
  qed

  show "inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v]) \<and>
       inv_second (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v]) \<and>
       inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v]) \<and> inv_second_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])"
    using 0 1 2 3 unfolding t'_def tw'_def by auto
qed

lemma inv_second_next_time_world:
  assumes "inv_second tw" and "inv_second_hold tw" and " disjnt {TEMP} (event_of tw)"
  shows "inv_second (next_time_world tw, snd tw)"
  unfolding inv_second_def
proof (rule, rule)
  have *: "(\<forall>i \<ge> fst tw. wline_of tw OUT (i + 1) = wline_of tw TEMP (fst tw))"
    using assms(2-3) unfolding inv_second_hold_def by auto
  fix i
  assume "i < fst (next_time_world tw, snd tw)"
  hence "i < next_time_world tw"
    by auto
  hence "i < fst tw \<or> fst tw \<le> i"
    by auto
  moreover
  { assume "i < fst tw"
    hence "wline_of tw OUT (i + 1) = wline_of tw TEMP i"
      using assms(1) unfolding inv_second_def by auto }
  moreover
  { assume "fst tw \<le> i"
    with * have "wline_of tw OUT (i + 1) = wline_of tw TEMP (fst tw)"
      by blast
    also have "... = wline_of tw TEMP i"
      using \<open>i < next_time_world tw\<close> unchanged_until_next_time_world
      using \<open>get_time tw \<le> i\<close> by metis
    finally have "wline_of tw OUT (i + 1) = wline_of tw TEMP i"
      by auto }
  ultimately have "wline_of tw OUT (i + 1) = wline_of tw TEMP i"
    by auto
  thus " wline_of (next_time_world tw, snd tw) OUT (i + 1) = wline_of (next_time_world tw, snd tw) TEMP i"
    by auto
qed

lemma inv_second_hold_next_time_world:
  assumes "inv_second_hold tw" and "disjnt {TEMP} (event_of tw)"
  shows " inv_second_hold (next_time_world tw, snd tw)"
  unfolding inv_second_hold_def
proof (rule, rule, rule)
  have *: "(\<forall>i \<ge> fst tw. wline_of tw OUT (i + 1) = wline_of tw TEMP (fst tw))"
    using assms(1-2) unfolding inv_second_hold_def by auto
  fix i
  assume "disjnt {TEMP} (event_of (next_time_world tw, snd tw))"
  assume "get_time (next_time_world tw, snd tw) \<le> i"
  hence "next_time_world tw \<le> i"
    by auto
  hence "fst tw \<le> i"
    using next_time_world_at_least  by (metis dual_order.trans order.strict_iff_order)
  hence "wline_of tw OUT (i + 1) = wline_of tw TEMP (fst tw)"
    using * by blast
  also have "... = wline_of tw TEMP (next_time_world tw - 1)"
    using unchanged_until_next_time_world
    by (metis (no_types, lifting) Suc_diff_1 diff_less dual_order.strict_iff_order le_0_eq le_Suc_eq
    next_time_world_at_least not_less zero_less_one)
  also have "... = wline_of tw TEMP (next_time_world tw)"
    using \<open>disjnt {TEMP} (event_of (next_time_world tw, snd tw))\<close>
    unfolding event_of_alt_def
    by (smt comp_apply diff_0_eq_0 disjnt_insert1 fst_conv mem_Collect_eq snd_conv)
  finally have "wline_of tw OUT (i + 1) = wline_of tw TEMP (next_time_world tw)"
    by auto
  thus "wline_of (next_time_world tw, snd tw) OUT (i + 1) =
        wline_of (next_time_world tw, snd tw) TEMP (get_time (next_time_world tw, snd tw))"
    by auto
qed

lemma conc_next_time_second:
  "\<turnstile> \<lbrace>\<lambda>tw. (let v = wline_of tw TEMP (fst tw) in inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])) \<and>
            inv_first (next_time_world tw, snd tw) \<and>
            inv_second tw \<and>
           (let v = wline_of tw TEMP (fst tw) in inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])) \<and>
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
  apply (rule Parallel[where R="\<lambda>tw. (let v = wline_of tw TEMP (fst tw) in inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd  tw[ OUT, 1 :=\<^sub>2 v]))
                                   \<and> inv_first (next_time_world tw, snd tw)
                                   \<and> inv_second tw
                                   \<and> (let v = wline_of tw TEMP (fst tw) in inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd  tw[ OUT, 1 :=\<^sub>2 v]))
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
       \<lbrace>\<lambda>tw. let v' = wline_of tw TEMP (fst tw) in inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 v'], snd tw[ OUT, 1 :=\<^sub>2 v'])\<rbrace>"
proof (rule SingleI, rule Assign2_altI, rule, rule, rule)
  fix tw :: "nat \<times> sig worldline_init"
  fix v
  assume "get_time tw = 0 \<and> beval_world_raw2 tw (Bsig IN) v"
  define tw1 where "tw1 = tw[ TEMP, 1 :=\<^sub>2 v]"
  obtain v' where "beval_world_raw2 tw1 (Bsig TEMP) v'"
    by (meson beval_world_raw2_Bsig)
  define tw2 where "tw2 = tw1[ OUT, 1 :=\<^sub>2 v']"
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
      using next_time_world_at_least  by (metis \<open>get_time tw = 0 \<and> beval_world_raw2 tw (Bsig IN) v\<close> neq0_conv not_less0)
    have "fst tw1 < next_time_world tw2"
      using next_time_world_at_least
      by (simp add: \<open>get_time tw < next_time_world tw2\<close> \<open>get_time tw1 = get_time tw\<close>)
    have "i < fst tw \<or> fst tw \<le> i \<and> i < next_time_world tw2 - 1 \<or> i = next_time_world tw2 - 1"
      using \<open>i < next_time_world tw2\<close> by linarith
    moreover
    { assume "i < fst tw"
      hence "False"
        using \<open>get_time tw = 0 \<and> beval_world_raw2 tw (Bsig IN) v\<close> by auto
      hence " wline_of tw2 TEMP (i + 1) = wline_of tw2 IN i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < next_time_world tw2 - 1"
      hence "wline_of tw2 TEMP (i + 1) = wline_of tw1 TEMP (i + 1)"
        unfolding tw2_def by (simp add: worldline_upd2_def worldline_upd_def)
      have "beval_world_raw2 tw (Bsig IN) ..."
        unfolding tw1_def using \<open>fst tw \<le> i \<and> i < next_time_world tw2 - 1\<close>
        by (simp add: \<open>get_time tw = 0 \<and> beval_world_raw2 tw (Bsig IN) v\<close> worldline_upd2_def worldline_upd_def)
      also have "... = wline_of tw IN (fst tw)"
        by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic calculation)
      also have "... = wline_of tw1 IN (fst tw1)"
        by (metis \<open>get_time tw1 = get_time tw\<close> less_add_one tw1_def worldline_upd2_before_dly)
      also have "... = wline_of tw2 IN (fst tw2)"
        by (simp add: tw2_def worldline_upd2_def worldline_upd_def)
      also have "... = wline_of tw2 IN i"
        by (metis \<open>get_time tw = 0 \<and> beval_world_raw2 tw (Bsig IN) v\<close> \<open>get_time tw1 = get_time tw\<close> \<open>i < next_time_world tw2\<close> snd_conv
        snd_swap swap_simp tw2_def unchanged_until_next_time_world worldline_upd2_def zero_le)
      finally have "wline_of tw2 TEMP (i + 1) = wline_of tw2 IN i"
        using \<open>wline_of tw IN (get_time tw) = wline_of tw1 IN (get_time tw1)\<close> \<open>wline_of tw1 IN
        (get_time tw1) = wline_of tw2 IN (get_time tw2)\<close> \<open>wline_of tw1 TEMP (i + 1) = wline_of tw IN
        (get_time tw)\<close> \<open>wline_of tw2 IN (get_time tw2) = wline_of tw2 IN i\<close> \<open>wline_of tw2 TEMP (i +
        1) = wline_of tw1 TEMP (i + 1)\<close> by auto }
    moreover
    { assume "i = next_time_world tw2 - 1"
      hence "wline_of tw2 TEMP (i + 1) = wline_of tw2 TEMP (next_time_world tw2)"
        using \<open>get_time tw < next_time_world tw2\<close> by force
      also have "... = wline_of tw1 TEMP (next_time_world tw2)"
        unfolding tw2_def  by (simp add: worldline_upd2_def worldline_upd_def)
      also have "... = wline_of tw1 IN (fst tw)"
        unfolding tw1_def using \<open>fst tw < next_time_world tw2\<close>
        by (smt One_nat_def Suc_diff_1 \<open>get_time tw = 0 \<and> beval_world_raw2 tw (Bsig IN) v\<close>
        add.commute beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic
        comp_def not_add_less2 plus_1_eq_Suc snd_conv worldline_upd2_def worldline_upd_def)
      also have "... = wline_of tw2 IN (fst tw2)"
        by (simp add: \<open>get_time tw1 = get_time tw\<close> tw2_def worldline_upd2_def worldline_upd_def)
      also have "... = wline_of tw2 IN i"
        by (metis \<open>get_time tw = 0 \<and> beval_world_raw2 tw (Bsig IN) v\<close> \<open>get_time tw1 = get_time tw\<close> \<open>i < next_time_world tw2\<close> fst_swap
        not_less not_less_zero snd_conv swap_simp tw2_def unchanged_until_next_time_world
        worldline_upd2_def)
      finally have "wline_of tw2 TEMP (i + 1) = wline_of tw2 IN i"
        by auto }
    ultimately have "wline_of tw2 TEMP (i + 1) = wline_of tw2 IN i"
      by auto
    thus "wline_of (next_time_world tw2, snd tw2) TEMP (i + 1) =
          wline_of (next_time_world tw2, snd tw2) IN i"
      by auto
  qed

  thus " let v' = wline_of tw[ TEMP, 1 :=\<^sub>2 v] TEMP (get_time tw[ TEMP, 1 :=\<^sub>2 v])
       in inv_first (next_time_world tw[ TEMP, 1 :=\<^sub>2 v][ OUT, 1 :=\<^sub>2 v'], snd tw[ TEMP, 1 :=\<^sub>2 v][ OUT, 1 :=\<^sub>2 v'])"
    unfolding t'_def tw1_def tw2_def
    using \<open>beval_world_raw2 tw1 (Bsig TEMP) v'\<close> tw1_def
    by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)
qed

lemma init_hoare2:
  "\<turnstile>\<^sub>I \<lbrace>\<lambda>tw. let v = wline_of tw TEMP (fst tw) in inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])\<rbrace>
          process {TEMP} : Bassign_trans OUT (Bsig TEMP) 1
      \<lbrace>\<lambda>tw. inv_first (next_time_world tw, snd tw)\<rbrace>"
  apply (rule SingleI)
  apply (rule Assign2_altI)
  apply (rule, rule)
  by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)

theorem init_preserves_inv_first:
  " init_sim_hoare (\<lambda>tw. fst tw = 0) two_inverter inv_first"
  unfolding two_inverter_def
  apply (rule AssignI)
  apply (rule ParallelI[where R="\<lambda>tw. let v = wline_of tw TEMP (fst tw) in
                                          inv_first (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd  tw[ OUT, 1 :=\<^sub>2 v])"])
    apply (rule init_hoare1)
   apply (rule init_hoare2)
  by (auto simp add: conc_stmt_wf_def)

lemma init_hoare3:
  "\<turnstile>\<^sub>I \<lbrace>\<lambda>tw. get_time tw = 0\<rbrace>  process {IN} : Bassign_trans TEMP (Bsig IN) 1 \<lbrace>inv_second\<rbrace>"
proof (rule SingleI, rule Assign2_altI, rule, rule, rule)
  fix tw :: "nat \<times> sig worldline_init"
  fix x
  assume "fst tw = 0 \<and> beval_world_raw2 tw (Bsig IN) x"
  let ?tw = "tw[ TEMP, 1 :=\<^sub>2 x]"
  have "fst tw = fst ?tw"
    unfolding worldline_upd2_def worldline_upd_def by auto
  thus "inv_second tw[ TEMP, 1 :=\<^sub>2 x]"
    using \<open>fst tw = 0 \<and> beval_world_raw2 tw (Bsig IN) x\<close> unfolding inv_second_def by auto
qed

lemma init_hoare4:
  "\<turnstile>\<^sub>I \<lbrace>inv_second\<rbrace>
        process {TEMP} : Bassign_trans OUT (Bsig TEMP) 1
      \<lbrace>\<lambda>tw. inv_second (next_time_world tw, snd tw)\<rbrace>"
  apply (rule SingleI)
  apply (rule Assign2_altI)
proof (rule)+
  fix tw x
  assume "inv_second tw \<and> beval_world_raw2 tw (Bsig TEMP) x"
  define tw' where "tw' = tw [OUT, 1 :=\<^sub>2 x]"
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
      hence "wline_of tw' OUT (i + 1) = wline_of tw OUT (i + 1)"
        unfolding tw'_def   by (meson add_mono1 worldline_upd2_before_dly)
      also have "... = wline_of tw TEMP i"
        using \<open>inv_second tw \<and> beval_world_raw2 tw (Bsig TEMP) x\<close>  \<open>i < fst tw\<close> unfolding inv_second_def by auto
      also have "... = wline_of tw' TEMP i"
        unfolding tw'_def  by (simp add: worldline_upd2_def worldline_upd_def)
      finally have "wline_of tw' OUT (i + 1) = wline_of tw' TEMP i"
        by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < next_time_world tw' - 1"
      hence "wline_of tw' OUT (i + 1) = wline_of tw TEMP (fst tw)"
        unfolding tw'_def
        by (smt Suc_eq_plus1 Suc_lessI \<open>get_time tw < next_time_world tw'\<close> \<open>inv_second tw \<and>
        beval_world_raw2 tw (Bsig TEMP) x\<close> beval_world_raw2_Bsig beval_world_raw2_def
        beval_world_raw_deterministic le_Suc_eq le_less less_diff_conv not_less_iff_gr_or_eq
        prod.sel(1) tw'_def unchanged_until_next_time_world worldline_upd2_at_dly
        worldline_upd2_def)
      also have "... = wline_of tw' TEMP (fst tw')"
        by (metis less_add_one prod.sel(1) tw'_def worldline_upd2_before_dly worldline_upd2_def)
      also have "... = wline_of tw' TEMP i"
        by (metis \<open>get_time tw \<le> i \<and> i < next_time_world tw' - 1\<close> \<open>i < next_time_world tw'\<close> snd_conv
        snd_swap swap_simp tw'_def unchanged_until_next_time_world worldline_upd2_def)
      finally have "wline_of tw' OUT (i + 1) = wline_of tw' TEMP i"
        by auto }
    moreover
    { assume "i = next_time_world tw' - 1"
      hence "wline_of tw' OUT (i + 1) = wline_of tw' OUT (next_time_world tw')"
        using \<open>i < next_time_world tw'\<close> by force
      also have "... = wline_of tw TEMP (fst tw)"
        unfolding tw'_def using \<open>fst tw < next_time_world tw'\<close>
        by (smt \<open>inv_second tw \<and> beval_world_raw2 tw (Bsig TEMP) x\<close> beval_world_raw2_Bsig
        beval_world_raw2_def beval_world_raw_deterministic discrete not_less o_apply snd_conv
        tw'_def worldline_upd2_def worldline_upd_def)
      also have "... = wline_of tw' TEMP (fst tw')"
        unfolding tw'_def  by (simp add: worldline_upd2_def worldline_upd_def)
      also have "... = wline_of tw' TEMP i"
        by (metis \<open>i < get_time tw \<Longrightarrow> wline_of tw' OUT (i + 1) = wline_of tw' TEMP i\<close> \<open>i <
        next_time_world tw'\<close> calculation fst_conv less_imp_le_nat nat_neq_iff tw'_def
        unchanged_until_next_time_world worldline_upd2_def)
      finally have "wline_of tw' OUT (i + 1) = wline_of tw' TEMP i"
        by auto }
    ultimately have "wline_of tw' OUT (i + 1) = wline_of tw' TEMP i"
      by auto
    thus "wline_of (next_time_world tw', snd tw') OUT (i + 1) =
          wline_of (next_time_world tw', snd tw') TEMP i "
      by auto
  qed
  thus "inv_second (next_time_world tw[ OUT, 1 :=\<^sub>2 x], snd tw[ OUT, 1 :=\<^sub>2 x]) "
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
      \<lbrace>\<lambda>tw. let v' = wline_of tw TEMP (fst tw) in inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v'], snd tw[ OUT, 1 :=\<^sub>2 v'])\<rbrace>"
  apply (rule SingleI)
  apply (rule Assign2_altI)
proof (rule, rule, rule)
  fix tw v
  assume "True \<and> beval_world_raw2 tw (Bsig IN) v"
  define tw1 where "tw1 = tw [ TEMP, 1 :=\<^sub>2 v]"
  obtain v' where "beval_world_raw2 tw1 (Bsig TEMP) v'"
    by (meson beval_world_raw2_Bsig)
  define tw2 where "tw2 = tw1[ OUT,  1 :=\<^sub>2 v']"
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
    have "wline_of tw2 TEMP (i + 1) = wline_of tw1 TEMP (i + 1)"
      unfolding tw2_def  by (simp add: worldline_upd2_def worldline_upd_def)
    also have "... = wline_of tw IN (fst tw)"
      unfolding tw1_def using \<open>fst tw < t'\<close> \<open>t' \<le> i\<close>
      by (smt \<open>True \<and> beval_world_raw2 tw (Bsig IN) v\<close> add_less_cancel_right beval_world_raw2_Bsig
      beval_world_raw2_def beval_world_raw_deterministic less_le_trans o_apply order.asym snd_conv
      worldline_upd2_def worldline_upd_def)
    also have "... = wline_of tw2 IN (fst tw2)"
      by (metis fst_conv less_add_one tw1_def tw2_def worldline_upd2_before_dly worldline_upd2_def)
    also have "... = wline_of tw2 IN (t' - 1)"
      unfolding t'_def  using unchanged_until_next_time_world
      by (metis (no_types, lifting) Suc_diff_1 diff_less gr_implies_not_zero le_0_eq less_Suc_eq_le
          next_time_world_at_least not_less zero_less_one)
    also have "... = wline_of tw2 IN t'"
      using \<open>disjnt {IN} (event_of (t', snd tw2))\<close> unfolding event_of_alt_def
      using \<open>get_time tw < t'\<close> by auto
    finally have "wline_of tw2 TEMP (i + 1) = wline_of tw2 IN t'"
      by auto
    thus "wline_of (t', snd tw2) TEMP (i + 1) = wline_of (t', snd tw2) IN (get_time (t', snd tw2))"
      by auto
  qed
  thus " let v' = wline_of tw[ TEMP, 1 :=\<^sub>2 v] TEMP (get_time tw[ TEMP, 1 :=\<^sub>2 v])
       in inv_first_hold (next_time_world tw[ TEMP, 1 :=\<^sub>2 v][ OUT, 1 :=\<^sub>2 v'], snd tw[ TEMP, 1 :=\<^sub>2 v][ OUT, 1 :=\<^sub>2 v'])"
    unfolding t'_def tw2_def tw1_def using \<open>beval_world_raw2 tw1 (Bsig TEMP) v'\<close> tw1_def
    by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)
qed

lemma init_hoare6:
  "\<turnstile>\<^sub>I \<lbrace>\<lambda>tw. let v = wline_of tw TEMP (fst tw) in inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])\<rbrace>
          process {TEMP} : Bassign_trans OUT (Bsig TEMP) 1
      \<lbrace>\<lambda>tw. inv_first_hold (next_time_world tw, snd tw)\<rbrace>"
  apply (rule SingleI)
  apply (rule Assign2_altI)
  by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)

theorem init_preserves_inv_first_hold:
  "init_sim_hoare (\<lambda>tw. True) two_inverter inv_first_hold"
  unfolding two_inverter_def
  apply (rule AssignI)
  apply (rule ParallelI[where R="\<lambda>tw. let v = wline_of tw TEMP (fst tw) in  inv_first_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd  tw[ OUT, 1 :=\<^sub>2 v])"])
    apply (rule init_hoare5)
   apply (rule init_hoare6)
  unfolding conc_stmt_wf_def by (auto)

lemma init_hoare7:
  " \<turnstile>\<^sub>I \<lbrace>\<lambda>tw. True\<rbrace>
          process {IN} : Bassign_trans TEMP (Bsig IN) 1
       \<lbrace>\<lambda>tw. let v' = wline_of tw TEMP (fst tw) in inv_second_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v'],  snd tw[ OUT, 1 :=\<^sub>2 v'])\<rbrace>"
proof (rule SingleI, rule Assign2_altI, rule, rule, rule)
  fix tw v
  define tw1 where "tw1 = tw [ TEMP, 1 :=\<^sub>2 v]"
  obtain v' where "beval_world_raw2 tw1 (Bsig TEMP) v'"
    by (meson beval_world_raw2_Bsig)
  define tw2 where "tw2 = tw1[ OUT,  1 :=\<^sub>2 v']"
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
    hence "wline_of tw2 OUT (i + 1) = wline_of tw1 TEMP (fst tw1)"
      unfolding tw2_def
      by (smt \<open>beval_world_raw2 tw1 (Bsig TEMP) v'\<close> \<open>get_time tw < t'\<close> \<open>t' \<le> i\<close>
      add_less_cancel_right beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic
      comp_def dual_order.strict_trans1 order.asym prod.sel(1) snd_conv tw1_def worldline_upd2_def
      worldline_upd_def)
    also have "... = wline_of tw2 TEMP (fst tw2)"
      by (simp add: tw2_def worldline_upd2_def worldline_upd_def)
    also have "... = wline_of tw2 TEMP (t' - 1)"
      using unchanged_until_next_time_world
      by (metis (no_types, lifting) Pair_inject Suc_diff_1 \<open>get_time tw < t'\<close> diff_less
      gr_implies_not_zero le_Suc_eq less_imp_le_nat nat_neq_iff prod.collapse t'_def tw1_def tw2_def
      worldline_upd2_def zero_less_one)
    also have "... = wline_of tw2 TEMP t'"
      using \<open>disjnt {TEMP} (event_of (t', snd tw2))\<close> unfolding event_of_alt_def
      using \<open>get_time tw < t'\<close> by auto
    finally have "wline_of tw2 OUT (i + 1) = wline_of tw2 TEMP t'"
      by auto
    thus "wline_of (t', snd tw2) OUT (i + 1) = wline_of (t', snd tw2) TEMP (get_time (t', snd tw2))"
      by auto
  qed
  thus " let v' = wline_of tw[ TEMP, 1 :=\<^sub>2 v] TEMP (get_time tw[ TEMP, 1 :=\<^sub>2 v])
       in inv_second_hold (next_time_world tw[ TEMP, 1 :=\<^sub>2 v][ OUT, 1 :=\<^sub>2 v'], snd tw[ TEMP, 1 :=\<^sub>2 v][ OUT, 1 :=\<^sub>2 v'])"
    unfolding tw1_def tw2_def t'_def
    using \<open>beval_world_raw2 tw1 (Bsig TEMP) v'\<close> tw1_def
    by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)
qed

lemma init_hoare8:
  "\<turnstile>\<^sub>I \<lbrace>\<lambda>tw. let v = wline_of tw TEMP (fst tw) in inv_second_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd tw[ OUT, 1 :=\<^sub>2 v])\<rbrace>
          process {TEMP} : Bassign_trans OUT (Bsig TEMP) 1
      \<lbrace>\<lambda>tw. inv_second_hold (next_time_world tw, snd tw)\<rbrace>"
  apply (rule SingleI)
  apply (rule Assign2_altI)
  by (metis beval_world_raw2_Bsig beval_world_raw2_def beval_world_raw_deterministic)

theorem init_preserves_inv_second_hold:
  "init_sim_hoare (\<lambda>tw. True) two_inverter inv_second_hold"
  unfolding two_inverter_def
  apply (rule AssignI)
  apply (rule ParallelI[where R="\<lambda>tw. let v = wline_of tw TEMP (fst tw) in inv_second_hold (next_time_world tw[ OUT, 1 :=\<^sub>2 v], snd  tw[ OUT, 1 :=\<^sub>2 v])"])
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
  shows "wline_of tw' TEMP (i + 1) = wline_of tw' IN i"
proof -
  obtain tw where "init_sim (0, w) two_inverter tw" and  "tw, i + 1, two_inverter \<Rightarrow>\<^sub>S tw'"
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
    using \<open>init_sim (0, w) two_inverter tw\<close> fst_conv unfolding init_sim_valid_def
    by metis+
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw\<rbrace> two_inverter \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw\<rbrace>"
    using conc_sim_soundness[OF sim_correctness_two_inverter2] \<open>conc_stmt_wf two_inverter\<close> \<open>nonneg_delay_conc two_inverter\<close>
    by auto
  ultimately have "inv_first tw'"
    using \<open>tw, i + 1, two_inverter \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'.  wline_of tw' TEMP (i + 1) = wline_of tw' IN i"
    unfolding inv_first_def by auto
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed

lemma
  assumes "sim_fin w (i + 1) two_inverter tw'"
  shows "wline_of tw' OUT (i + 1) = wline_of tw' TEMP i"
proof -
  obtain tw where "init_sim (0, w) two_inverter tw" and  "tw, i + 1, two_inverter \<Rightarrow>\<^sub>S tw'"
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
    using \<open>init_sim (0, w) two_inverter tw\<close> fst_conv unfolding init_sim_valid_def
    by metis+
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw \<and> inv_first_hold tw \<and> inv_second_hold tw\<rbrace> two_inverter \<lbrace>\<lambda>tw. inv_first tw \<and> inv_second tw\<rbrace>"
    using conc_sim_soundness[OF sim_correctness_two_inverter2] \<open>conc_stmt_wf two_inverter\<close> \<open>nonneg_delay_conc two_inverter\<close>
    by auto
  ultimately have "inv_second tw'"
    using \<open>tw, i + 1, two_inverter \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'.  wline_of tw' OUT (i + 1) = wline_of tw' TEMP i"
    unfolding inv_second_def by auto
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed

end