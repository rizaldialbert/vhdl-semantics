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
                               
definition mux2_inv :: "sig assn2" where
  "mux2_inv \<equiv> \<lambda>tw. (\<forall>i < fst tw. snd tw OUT (i + 1) \<longleftrightarrow> 
                                              (if snd tw SEL i then snd tw IN1 i else snd tw IN0 i))"

definition mux2_inv' :: "sig assn2" where
  "mux2_inv' \<equiv> (\<lambda>tw. disjnt {IN0, IN1, SEL} (event_of tw) \<longrightarrow> 
                  (\<forall>i\<ge>fst tw. snd tw OUT (i + 1) \<longleftrightarrow> 
                    (if snd tw SEL (fst tw) then snd tw IN1 (fst tw) else snd tw IN0 (fst tw))))"

subsection \<open>Proving that the sequential component preserves @{term "mux2_inv"}\<close>

lemma mux2_inv_next_time:
  assumes "mux2_inv tw" and "beval_world_raw2 tw (Bsig SEL)"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN1)]"
  shows   "mux2_inv (next_time_world tw', snd tw')"
proof -
  let ?t' = "next_time_world tw'"
  have "snd tw SEL (fst tw)"
    using assms(2) unfolding beval_world_raw2_def beval_world_raw_def state_of_world_def 
    by auto
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  have 0: "snd tw' SEL (fst tw)= snd tw SEL (fst tw)" and 1: "snd tw IN1 (fst tw)\<longleftrightarrow> snd tw' IN1 (fst tw)" 
   and 2: "snd tw IN0 (fst tw)\<longleftrightarrow> snd tw' IN0 (fst tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by simp+  
  have "\<forall>i < ?t'. snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
  proof (rule, rule)
    fix i
    assume "i < ?t'"
    have "i < fst tw \<or> fst tw \<le> i \<and> i < ?t' - 1 \<or> i = ?t' - 1"
      using next_time_world_at_least \<open>i < next_time_world tw'\<close> not_less by linarith
    moreover
    { assume "i < fst tw"
      hence "snd tw OUT (i + 1) \<longleftrightarrow> (if snd tw SEL i then snd tw IN1 i else snd tw IN0 i)"
        using assms(1) unfolding mux2_inv_def by auto
      moreover have "snd tw OUT (i + 1) \<longleftrightarrow> snd tw' OUT (i + 1)" and "snd tw IN1 i \<longleftrightarrow> snd tw' IN1 i" and "snd tw IN0 i \<longleftrightarrow> snd tw' IN0 i"
        unfolding tw'_def worldline_upd2_def worldline_upd_def  by (simp add: \<open>i < get_time tw\<close>)+
      ultimately have "snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)" 
        by (metis assms(3) prod.sel(2) sig.distinct(12) worldline_upd2_def worldline_upd_def) }
    moreover
    { assume "fst tw \<le> i \<and> i < ?t' - 1"
      hence "snd tw' OUT (i + 1) \<longleftrightarrow> snd tw' OUT (fst tw + 1)"
        using unchanged_until_next_time_world 
        by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
        le_less_trans less_diff_conv)        
      moreover have "snd tw' IN1 i \<longleftrightarrow> snd tw' IN1 (fst tw)" and "snd tw' IN0 i \<longleftrightarrow> snd tw' IN0 (fst tw)"
          and "snd tw' SEL i \<longleftrightarrow> snd tw' SEL (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i < next_time_world tw' - 1\<close>
        by (simp add: unchanged_until_next_time_world \<open>get_time tw = get_time tw'\<close> \<open>i < next_time_world tw'\<close>)+
      moreover have "snd tw' OUT (fst tw + 1) \<longleftrightarrow> 
                      (if snd tw' SEL (fst tw) then snd tw' IN1 (fst tw) else snd tw' IN0 (fst tw))"
      proof -
        have "snd tw' OUT (fst tw + 1) \<longleftrightarrow> beval_world_raw2 tw (Bsig IN1)"
          using \<open>fst tw \<le> i \<and> i < ?t' - 1\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def 
          by auto
        also have "... \<longleftrightarrow> snd tw IN1 (fst tw)"
          unfolding beval_world_raw2_def beval_world_raw_def state_of_world_def by auto
        also have "... \<longleftrightarrow> (if snd tw SEL (fst tw) then snd tw IN1 (fst tw) else snd tw IN0 (fst tw))"
          using \<open>snd tw SEL (fst tw)\<close> by auto
        \<comment> \<open>notice the change from @{term "tw"} to @{term "tw'"}\<close>
        also have "... \<longleftrightarrow> (if snd tw' SEL (fst tw) then snd tw' IN1 (fst tw) else snd tw' IN0 (fst tw))"
          using 0 1 2 by auto        
        finally show "snd tw' OUT (fst tw + 1) \<longleftrightarrow> (if snd tw' SEL (fst tw) then snd tw' IN1 (fst tw) else snd tw' IN0 (fst tw))"
          by auto
      qed
      ultimately have "snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
        by auto }
    moreover
    { assume "i = ?t' - 1"
      hence "snd tw' OUT (i + 1) = snd tw' OUT ?t'"
        using \<open>i < ?t'\<close> by auto
      also have "... \<longleftrightarrow> snd tw' OUT (fst tw + 1)"
        using \<open>fst tw < ?t'\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... \<longleftrightarrow> (if snd tw' SEL (fst tw) then snd tw' IN1 (fst tw) else snd tw' IN0 (fst tw))"
      proof -
        have "snd tw' OUT (fst tw + 1) = snd tw IN1 (fst tw)"
          unfolding tw'_def worldline_upd2_def worldline_upd_def beval_world_raw2_def beval_world_raw_def state_of_world_def 
          by auto
        \<comment> \<open>notice that we use @{term "tw'"} on the else part; no point of using @{term "tw"}\<close>
        also have "... \<longleftrightarrow> (if snd tw SEL (fst tw) then snd tw IN1 (fst tw) else snd tw' IN0 (fst tw))"
          using \<open>snd tw SEL (fst tw)\<close> by auto
        also have "... \<longleftrightarrow> (if snd tw' SEL (fst tw) then snd tw' IN1 (fst tw) else snd tw' IN0 (fst tw))"
          using 0 1 by auto
        finally show ?thesis by auto
      qed
      also have "... \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
        by (metis \<open>get_time tw = get_time tw'\<close> 
        \<open>i < get_time tw \<Longrightarrow> snd tw' OUT (i + 1) = (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)\<close> 
        \<open>i < next_time_world tw'\<close> calculation not_less unchanged_until_next_time_world)
      finally have "snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
        by auto }
    ultimately show "snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
      by auto
  qed
  thus ?thesis
    unfolding mux2_inv_def by auto
qed

lemma mux2_inv_next_time':
  assumes "mux2_inv tw" and "\<not> beval_world_raw2 tw (Bsig SEL)"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN0)]"
  shows   "mux2_inv (next_time_world tw', snd tw')"
proof -
  let ?t' = "next_time_world tw'"
  have "\<not> snd tw SEL (fst tw)"
    using assms(2) unfolding beval_world_raw2_def beval_world_raw_def state_of_world_def 
    by auto
  have "fst tw' < next_time_world tw'"
    using next_time_world_at_least  using nat_less_le by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < next_time_world tw'"
    by auto
  have 0: "snd tw' SEL (fst tw)= snd tw SEL (fst tw)" and 1: "snd tw IN1 (fst tw)\<longleftrightarrow> snd tw' IN1 (fst tw)" 
   and 2: "snd tw IN0 (fst tw)\<longleftrightarrow> snd tw' IN0 (fst tw)"
    unfolding tw'_def worldline_upd2_def worldline_upd_def by simp+  
  have "\<forall>i < ?t'. snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
  proof (rule, rule)
    fix i
    assume "i < ?t'"
    have "i < fst tw \<or> fst tw \<le> i \<and> i < ?t' - 1 \<or> i = ?t' - 1"
      using next_time_world_at_least \<open>i < next_time_world tw'\<close> not_less by linarith
    moreover
    { assume "i < fst tw"
      hence "snd tw OUT (i + 1) \<longleftrightarrow> (if snd tw SEL i then snd tw IN1 i else snd tw IN0 i)"
        using assms(1) unfolding mux2_inv_def by auto
      moreover have "snd tw OUT (i + 1) \<longleftrightarrow> snd tw' OUT (i + 1)" and "snd tw IN1 i \<longleftrightarrow> snd tw' IN1 i" and "snd tw IN0 i \<longleftrightarrow> snd tw' IN0 i"
        unfolding tw'_def worldline_upd2_def worldline_upd_def  by (simp add: \<open>i < get_time tw\<close>)+
      ultimately have "snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)" 
        by (metis assms(3) prod.sel(2) sig.distinct(12) worldline_upd2_def worldline_upd_def) }
    moreover
    { assume "fst tw \<le> i \<and> i < ?t' - 1"
      hence "snd tw' OUT (i + 1) \<longleftrightarrow> snd tw' OUT (fst tw + 1)"
        using unchanged_until_next_time_world 
        by (metis (mono_tags, lifting) Suc_eq_plus1 \<open>get_time tw = get_time tw'\<close> le_Suc_eq le_add1
        le_less_trans less_diff_conv)        
      moreover have "snd tw' IN1 i \<longleftrightarrow> snd tw' IN1 (fst tw)" and "snd tw' IN0 i \<longleftrightarrow> snd tw' IN0 (fst tw)"
          and "snd tw' SEL i \<longleftrightarrow> snd tw' SEL (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i < next_time_world tw' - 1\<close>
        by (simp add: unchanged_until_next_time_world \<open>get_time tw = get_time tw'\<close> \<open>i < next_time_world tw'\<close>)+
      moreover have "snd tw' OUT (fst tw + 1) \<longleftrightarrow> 
                      (if snd tw' SEL (fst tw) then snd tw' IN1 (fst tw) else snd tw' IN0 (fst tw))"
      proof -
        have "snd tw' OUT (fst tw + 1) \<longleftrightarrow> beval_world_raw2 tw (Bsig IN0)"
          using \<open>fst tw \<le> i \<and> i < ?t' - 1\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def 
          by auto
        also have "... \<longleftrightarrow> snd tw IN0 (fst tw)"
          unfolding beval_world_raw2_def beval_world_raw_def state_of_world_def by auto
        also have "... \<longleftrightarrow> (if snd tw SEL (fst tw) then snd tw IN1 (fst tw) else snd tw IN0 (fst tw))"
          using \<open>\<not> snd tw SEL (fst tw)\<close> by auto
        \<comment> \<open>notice the change from @{term "tw"} to @{term "tw'"}\<close>
        also have "... \<longleftrightarrow> (if snd tw' SEL (fst tw) then snd tw' IN1 (fst tw) else snd tw' IN0 (fst tw))"
          using 0 1 2 by auto        
        finally show "snd tw' OUT (fst tw + 1) \<longleftrightarrow> (if snd tw' SEL (fst tw) then snd tw' IN1 (fst tw) else snd tw' IN0 (fst tw))"
          by auto
      qed
      ultimately have "snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
        by auto }
    moreover
    { assume "i = ?t' - 1"
      hence "snd tw' OUT (i + 1) = snd tw' OUT ?t'"
        using \<open>i < ?t'\<close> by auto
      also have "... \<longleftrightarrow> snd tw' OUT (fst tw + 1)"
        using \<open>fst tw < ?t'\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
      also have "... \<longleftrightarrow> (if snd tw' SEL (fst tw) then snd tw' IN1 (fst tw) else snd tw' IN0 (fst tw))"
      proof -
        have "snd tw' OUT (fst tw + 1) = snd tw IN0 (fst tw)"
          unfolding tw'_def worldline_upd2_def worldline_upd_def beval_world_raw2_def beval_world_raw_def state_of_world_def 
          by auto
        \<comment> \<open>notice that we use @{term "tw'"} on the else part; no point of using @{term "tw"}\<close>
        also have "... \<longleftrightarrow> (if snd tw SEL (fst tw) then snd tw' IN1 (fst tw) else snd tw IN0 (fst tw))"
          using \<open>\<not> snd tw SEL (fst tw)\<close> by auto
        also have "... \<longleftrightarrow> (if snd tw' SEL (fst tw) then snd tw' IN1 (fst tw) else snd tw' IN0 (fst tw))"
          using 0 2 by auto
        finally show ?thesis by auto
      qed
      also have "... \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
        by (metis \<open>get_time tw = get_time tw'\<close> 
        \<open>i < get_time tw \<Longrightarrow> snd tw' OUT (i + 1) = (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)\<close> 
        \<open>i < next_time_world tw'\<close> calculation not_less unchanged_until_next_time_world)
      finally have "snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
        by auto }
    ultimately show "snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
      by auto
  qed
  thus ?thesis
    unfolding mux2_inv_def by auto
qed

lemma mux2_seq_hoare_next_time_if:
  "\<turnstile> [\<lambda>tw. mux2_inv tw \<and> beval_world_raw2 tw (Bsig SEL)] Bassign_trans OUT (Bsig IN1) 1 [\<lambda>tw. mux2_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using mux2_inv_next_time by auto

lemma mux2_seq_hoare_next_time_else:
  "\<turnstile> [\<lambda>tw. mux2_inv tw \<and> \<not> beval_world_raw2 tw (Bsig SEL)] Bassign_trans OUT (Bsig IN0) 1 [\<lambda>tw. mux2_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using mux2_inv_next_time' by auto

theorem mux2_seq_hoare_next_time:
  "\<turnstile> [mux2_inv] Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1) [\<lambda>tw. mux2_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv (next_time_world tw, snd tw)" and P = "mux2_inv", rotated 1], rule If2)
     apply (rule mux2_seq_hoare_next_time_if)
    apply (rule mux2_seq_hoare_next_time_else)
  apply simp+
  done

theorem mux2_seq_hoare_next_time0:
  "\<turnstile> [\<lambda>tw. fst tw = 0] Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1) [\<lambda>tw. mux2_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where P="mux2_inv" and Q="\<lambda>tw. mux2_inv (next_time_world tw, snd tw)"])
  using mux2_seq_hoare_next_time unfolding mux2_inv_def by auto

subsection \<open>Proving that the sequential component preserves @{term "mux2_inv'"}\<close>

lemma input_signals_unchanged:
  fixes tw any
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig any)]"
  defines "t' \<equiv> next_time_world tw'"
  assumes "disjnt {IN0, IN1, SEL} (event_of (t', snd tw'))"
  shows "\<And>s. s \<in> {IN0, IN1, SEL} \<Longrightarrow> snd tw' s t' \<longleftrightarrow> snd tw s (fst tw)"
proof -
  fix s
  assume "s \<in> {IN0, IN1, SEL}"
  have "fst tw' < t'"
    using next_time_world_at_least unfolding t'_def by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def unfolding worldline_upd2_def by auto
  ultimately have "fst tw < t'"
    by auto
  have "snd tw' s t' \<longleftrightarrow> snd tw s t'"
    using \<open>s \<in> {IN0, IN1, SEL}\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... \<longleftrightarrow> snd tw s (t' - 1)"
    using \<open>disjnt {IN0, IN1, SEL} (event_of (t', snd tw'))\<close> \<open>fst tw < t'\<close>
    unfolding event_of_alt_def 
    by (smt \<open>s \<in> {IN0, IN1, SEL}\<close> disjnt_iff fst_conv gr_implies_not_zero insertE mem_Collect_eq
    sig.distinct(12) sig.distinct(5) sig.distinct(9) singletonD snd_conv tw'_def
    worldline_upd2_def worldline_upd_def)
  also have "... \<longleftrightarrow> snd tw s (fst tw)"
  proof -
    have "fst tw' \<le> t' - 1" and "t' - 1 < t'"
      using \<open>fst tw' < t'\<close> by auto
    hence "snd tw' s (t' - 1) = snd tw' s (fst tw')"
      using unchanged_until_next_time_world[where tw="tw'"] unfolding t'_def by blast
    moreover have "snd tw' s (t' - 1) = snd tw s (t' - 1)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def  using \<open>s \<in> {IN0, IN1, SEL}\<close> by auto
    moreover have "snd tw' s (fst tw') = snd tw s (fst tw')"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    ultimately show ?thesis
      using \<open>fst tw = fst tw'\<close> by auto
  qed
  finally show "snd tw' s t' \<longleftrightarrow> snd tw s (fst tw)"
    by auto
qed

lemma mux2_inv'_next_time:
  assumes "beval_world_raw2 tw (Bsig SEL)"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN1)]"
  shows   "mux2_inv' (next_time_world tw', snd tw')"
proof -
  let ?t' = "next_time_world tw'"
  have "snd tw SEL (fst tw)"
    using assms(1) unfolding beval_world_raw2_def beval_world_raw_def state_of_world_def 
    by auto
  { assume "disjnt {IN0, IN1, SEL} (event_of (?t', snd tw'))"
    have "fst tw' < ?t'"
      using next_time_world_at_least by blast
    moreover have "fst tw = fst tw'"
      unfolding tw'_def unfolding worldline_upd2_def by auto
    ultimately have "fst tw < ?t'"
      by auto
    have *: "\<And>s. s \<in> {IN0, IN1, SEL} \<Longrightarrow> snd tw' s ?t' \<longleftrightarrow> snd tw s (fst tw)"
      using \<open>disjnt {IN0, IN1, SEL} (event_of (next_time_world tw', snd tw'))\<close> 
      input_signals_unchanged tw'_def by blast
    have "\<And>i. ?t' \<le> i \<Longrightarrow> snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL ?t' then snd tw' IN1 ?t' else snd tw' IN0 ?t')"
    proof -
      fix i 
      assume "?t' \<le> i"
      hence "snd tw' OUT (i + 1) \<longleftrightarrow> snd tw IN1 (fst tw)"
        using `fst tw < ?t'` unfolding tw'_def worldline_upd2_def worldline_upd_def beval_world_raw2_def
          beval_world_raw_def state_of_world_def by auto
      also have "... \<longleftrightarrow> (if snd tw SEL (fst tw) then snd tw IN1 (fst tw) else snd tw' IN0 ?t')"
        using \<open>snd tw SEL (fst tw)\<close> unfolding beval_world_raw2_def beval_world_raw_def  
        by (simp add: state_of_world_def)
      also have "... \<longleftrightarrow> (if snd tw' SEL ?t' then snd tw' IN1 ?t' else snd tw' IN0 ?t')"
        using * by auto
      finally show "snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL ?t' then snd tw' IN1 ?t' else snd tw' IN0 ?t')"
        by auto
    qed }
  thus ?thesis
    unfolding mux2_inv'_def by auto
qed

lemma mux2_inv'_next_time2:
  assumes "\<not> beval_world_raw2 tw (Bsig SEL)"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 beval_world_raw2 tw (Bsig IN0)]"
  shows   "mux2_inv' (next_time_world tw', snd tw')"
proof -
  let ?t' = "next_time_world tw'"
  have "\<not> snd tw SEL (fst tw)"
    using assms(1) unfolding beval_world_raw2_def beval_world_raw_def state_of_world_def 
    by auto
  { assume "disjnt {IN0, IN1, SEL} (event_of (?t', snd tw'))"
    have "fst tw' < ?t'"
      using next_time_world_at_least by blast
    moreover have "fst tw = fst tw'"
      unfolding tw'_def unfolding worldline_upd2_def by auto
    ultimately have "fst tw < ?t'"
      by auto
    have *: "\<And>s. s \<in> {IN0, IN1, SEL} \<Longrightarrow> snd tw' s ?t' \<longleftrightarrow> snd tw s (fst tw)"
      using \<open>disjnt {IN0, IN1, SEL} (event_of (next_time_world tw', snd tw'))\<close> 
      input_signals_unchanged tw'_def by blast
    have "\<And>i. ?t' \<le> i \<Longrightarrow> snd tw' OUT (i + 1) \<longleftrightarrow> 
                                     (if snd tw' SEL ?t' then snd tw' IN1 ?t' else snd tw' IN0 ?t')"
    proof -
      fix i 
      assume "?t' \<le> i"
      hence "snd tw' OUT (i + 1) \<longleftrightarrow> snd tw IN0 (fst tw)"
        using `fst tw < ?t'` unfolding tw'_def worldline_upd2_def worldline_upd_def beval_world_raw2_def
          beval_world_raw_def state_of_world_def by auto
      also have "... \<longleftrightarrow> (if snd tw SEL (fst tw) then snd tw IN1 (fst tw) else snd tw IN0 (fst tw))"
        using \<open>\<not> snd tw SEL (fst tw)\<close> unfolding beval_world_raw2_def beval_world_raw_def  
        by (simp add: state_of_world_def)
      also have "... \<longleftrightarrow> (if snd tw' SEL ?t' then snd tw' IN1 ?t' else snd tw' IN0 ?t')"
        using * by auto
      finally show "snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL ?t' then snd tw' IN1 ?t' else snd tw' IN0 ?t')"
        by auto
    qed }
  thus ?thesis
    unfolding mux2_inv'_def by auto
qed

lemma mux2_seq_hoare_next_time_if':
  "\<turnstile> [\<lambda>tw. beval_world_raw2 tw (Bsig SEL)] Bassign_trans OUT (Bsig IN1) 1 [\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using mux2_inv'_next_time by auto

lemma mux2_seq_hoare_next_time_else':
  " \<turnstile> [\<lambda>tw. \<not> beval_world_raw2 tw (Bsig SEL)] Bassign_trans OUT (Bsig IN0) 1 [\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)", rotated 1], rule Assign2)
  using mux2_inv'_next_time2 by auto

theorem mux2_seq_hoare_next_time':
  "\<turnstile> [\<lambda>tw. True] Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig IN1) 1) (Bassign_trans OUT (Bsig IN0) 1) [\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where Q="\<lambda>tw. mux2_inv' (next_time_world tw, snd tw)" and P = "\<lambda>tw. True", rotated 1], rule If2)
  unfolding simp_thms(22)
     apply (rule mux2_seq_hoare_next_time_if')
    apply (rule mux2_seq_hoare_next_time_else')
   apply simp+
  done

subsection \<open>Proving that the concurrent component\<close>

lemma mux2_inv_conc_hoare:
  "\<And>tw. mux2_inv tw \<and> mux2_inv' tw \<and> disjnt {IN0, IN1, SEL} (event_of tw) \<Longrightarrow> mux2_inv (next_time_world tw, snd tw)"
proof -
  fix tw
  assume "mux2_inv tw \<and> mux2_inv' tw \<and> disjnt {IN0, IN1, SEL} (event_of tw)"
  hence "mux2_inv tw" and "mux2_inv' tw" and "disjnt {IN0, IN1, SEL} (event_of tw)"
    by auto
  hence *: "\<forall>i < fst tw. snd tw OUT (i + 1) \<longleftrightarrow> (if snd tw SEL i then snd tw IN1 i else snd tw IN0 i)"
    unfolding mux2_inv_def by auto
  have **: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. snd tw s i = snd tw s (fst tw))"
    using unchanged_until_next_time_world by blast
  have ***: "(\<forall>i\<ge> fst tw. snd tw OUT (i + 1) \<longleftrightarrow> (if snd tw SEL (fst tw) then snd tw IN1 (fst tw) else snd tw IN0 (fst tw)))"
    using \<open>mux2_inv' tw\<close> \<open>disjnt {IN0, IN1, SEL} (event_of tw)\<close> unfolding mux2_inv'_def by auto

  \<comment> \<open>obtain the value of A and B at time fst tw\<close>
  have  "snd tw SEL (fst tw) = snd tw SEL (fst tw - 1)" and "snd tw IN0 (fst tw) = snd tw IN0 (fst tw - 1)"
    and "snd tw IN1 (fst tw) = snd tw IN1 (fst tw - 1)"
    using \<open>disjnt {IN0, IN1, SEL} (event_of tw)\<close> unfolding event_of_alt_def 
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+
 { fix i 
    assume "i < next_time_world tw"
    have "i < fst tw \<or> fst tw \<le> i" 
      by auto
    moreover
    { assume "i < fst tw"
      hence "snd tw OUT (i + 1) \<longleftrightarrow> (if snd tw SEL i then snd tw IN1 i else snd tw IN0 i)"
        using * by auto }
    moreover
    { assume "fst tw \<le> i"
      hence "snd tw OUT (i + 1) \<longleftrightarrow> snd tw OUT (fst tw + 1)"
        using *** by auto
      also have "... \<longleftrightarrow> (if snd tw SEL (fst tw) then snd tw IN1 (fst tw) else snd tw IN0 (fst tw))"
        using *** \<open>fst tw \<le> i\<close> by auto
      also have "... \<longleftrightarrow> (if snd tw SEL i then snd tw IN1 i else snd tw IN0 i)"
        using ** \<open>i < next_time_world tw\<close> \<open>fst tw \<le> i\<close> less_imp_le_nat by presburger
      finally have "snd tw OUT (i + 1) \<longleftrightarrow> (if snd tw SEL i then snd tw IN1 i else snd tw IN0 i)"
        by auto }
    ultimately have "snd tw OUT (i + 1) \<longleftrightarrow> (if snd tw SEL i then snd tw IN1 i else snd tw IN0 i)"
      by auto }
  hence "\<And>i. i < next_time_world tw \<Longrightarrow> snd tw OUT (i + 1) \<longleftrightarrow> (if snd tw SEL i then snd tw IN1 i else snd tw IN0 i)"
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
  hence 0: "(\<forall>i\<ge>fst tw. snd tw OUT (i + 1) \<longleftrightarrow> (if snd tw SEL (get_time tw) then snd tw IN1 (get_time tw) else snd tw IN0 (get_time tw)))"
    unfolding mux2_inv'_def by auto  
  have 1: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. snd tw s i = snd tw s (fst tw))"
    using unchanged_until_next_time_world by blast
  let ?t' = "next_time_world tw"
  { assume "disjnt {IN0, IN1, SEL} (event_of (next_time_world tw, snd tw))" 
    hence *: "snd tw IN0 ?t' = snd tw IN0 (?t' - 1)" and **: "snd tw IN1 ?t' = snd tw IN1 (?t' - 1)"
        and ***: "snd tw SEL ?t' = snd tw SEL (?t' - 1)"
      unfolding event_of_alt_def  by (smt diff_0_eq_0 disjnt_insert1 fst_conv mem_Collect_eq snd_conv)+
    have "fst tw < next_time_world tw"
      by (simp add: next_time_world_at_least)
    { fix i
      assume "?t' \<le> i"
      hence "snd tw OUT (i + 1) \<longleftrightarrow> (if snd tw SEL (fst tw) then snd tw IN1 (fst tw) else snd tw IN0 (fst tw))"
        using 0 \<open>fst tw < ?t'\<close> by auto
      moreover have "snd tw IN0 (fst tw) = snd tw IN0 (?t' - 1)" and "snd tw IN1 (fst tw) = snd tw IN1 (?t' - 1)"
        and "snd tw SEL (fst tw) = snd tw SEL (?t' - 1)"
        using 1 
        by (metis (no_types, lifting) One_nat_def Suc_leI \<open>get_time tw < next_time_world tw\<close>
        add_le_cancel_right diff_add diff_less discrete gr_implies_not_zero neq0_conv zero_less_one)+
      ultimately have "snd tw OUT (i + 1) \<longleftrightarrow> (if snd tw SEL ?t' then snd tw IN1 ?t' else snd tw IN0 ?t')"
        using * ** *** by auto
    }
    hence "(\<forall>i\<ge>?t'. snd tw OUT (i + 1) = (if snd tw SEL ?t' then snd tw IN1 ?t' else snd tw IN0 ?t'))"
      by auto }
  thus "mux2_inv' (next_time_world tw, snd tw)"
    unfolding mux2_inv'_def by auto
qed

lemma mux2_conc_hoare:
  "\<turnstile> \<lbrace>\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw\<rbrace> mux2 \<lbrace>\<lambda>tw. mux2_inv  (next_time_world tw, snd tw)  \<and> mux2_inv' (next_time_world tw, snd tw)\<rbrace>"
  unfolding mux2_def
  apply (rule Single)
   apply (unfold conj_assoc)
   apply (rule compositional_conj)  
    apply(rule mux2_seq_hoare_next_time)
   apply(rule Conseq2[where P="\<lambda>tw. True"])
     apply simp
    apply (rule mux2_seq_hoare_next_time')
   apply simp
  apply (rule allI)
  apply (rule impI)
  apply (rule conjI)
  apply (erule mux2_inv_conc_hoare)
  apply (erule mux2_inv'_conc_hoare)
  done

subsection \<open>Simulation preserves the invariant\<close>

lemma mux2_conc_sim:
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw\<rbrace> mux2 \<lbrace>\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw\<rbrace>"
  apply (rule While)
  apply (rule mux2_conc_hoare)
  done   

lemma mux2_conc_sim':
  "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw\<rbrace> mux2 \<lbrace>mux2_inv\<rbrace>"
  by (rule Conseq_sim[where Q="\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw" and 
                            P="\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw"])
     (simp_all add: mux2_conc_sim)  

subsection \<open>Initialisation preserves the invariant\<close>

lemma init_sat_mux2_inv:
  "init_sim_hoare (\<lambda>tw. fst tw = 0) mux2 mux2_inv"
  unfolding mux2_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule mux2_seq_hoare_next_time0)
  done

lemma init_sat_mux_inv': 
  "init_sim_hoare (\<lambda>tw. True) mux2 mux2_inv'"
  unfolding mux2_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule mux2_seq_hoare_next_time')
  done

lemma init_sat_nand_mux_inv_comb:
  "init_sim_hoare (\<lambda>tw. fst tw = 0) mux2 (\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw)"
  apply (rule ConjI_sim)
  apply (rule init_sat_mux2_inv)
  apply (rule ConseqI_sim[where P="\<lambda>tw. True" and Q="mux2_inv'"])
  apply (simp, rule init_sat_mux_inv', simp)
  done

lemma nand_correctness_inert:
  assumes "sim_fin w (i + 1) mux2 tw'"
  shows "snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
proof -
  obtain tw where "init_sim (0, w) mux2 = tw" and  "tw, i + 1, mux2 \<Rightarrow>\<^sub>S tw'" 
    using premises_sim_fin_obt[OF assms] by auto
  hence "i + 1 < fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf mux2"
    unfolding conc_stmt_wf_def mux2_def by auto
  moreover have "nonneg_delay_conc mux2"
    unfolding mux2_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0) mux2 (\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw)"
    using init_sim_hoare_soundness[OF init_sat_nand_mux_inv_comb] by auto
  hence "mux2_inv tw" and "mux2_inv' tw"
    using \<open>init_sim (0, w) mux2 = tw\<close> fst_conv unfolding init_sim_valid_def 
    by fastforce+ 
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw\<rbrace> mux2 \<lbrace>mux2_inv\<rbrace>"
    using conc_sim_soundness[OF mux2_conc_sim'] \<open>conc_stmt_wf mux2\<close> \<open>nonneg_delay_conc mux2\<close>
    by auto                               
  ultimately have "mux2_inv tw'"
    using \<open>tw, i + 1, mux2 \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i < fst tw'. snd tw' OUT (i + 1) \<longleftrightarrow> (if snd tw' SEL i then snd tw' IN1 i else snd tw' IN0 i)"
    unfolding mux2_inv_def by auto
  with \<open>i + 1 < fst tw'\<close> show ?thesis
    by auto
qed
     
end