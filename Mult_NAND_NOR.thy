(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Mult_NAND_NOR
  imports VHDL_Hoare_Complete 
begin

text \<open>Define the new datatype for the all signals occurred in a multiplexer. A multiplexer has three
inputs: in0, in1, and a selector.\<close>

datatype sig = IN0 | IN1 | SEL | OUT | TEMP0 | TEMP1

abbreviation mux2_seq :: "sig seq_stmt" where
  "mux2_seq \<equiv> Bcomp
              (Bassign_trans TEMP0 (Bnand (Bsig IN0) (Bsig IN1)) 1)
              (Bcomp
                (Bassign_trans TEMP1 (Bnor  (Bsig IN0) (Bsig IN1)) 1)
                (Bguarded (Bsig SEL)
                  (Bassign_trans OUT (Bsig TEMP0) 1)
                  (Bassign_trans OUT (Bsig TEMP1) 1)))"

\<comment> \<open>We put suffix 2 because it only selects between two inputs\<close>
definition mux2 :: "sig conc_stmt" where
  "mux2 = process {IN0, IN1, SEL, TEMP0, TEMP1} : mux2_seq"

lemma potential_tyenv:
  assumes "seq_wt \<Gamma> mux2_seq"
  shows "\<exists>ki len. \<Gamma> IN0 = Bty \<and> \<Gamma> IN1 = Bty \<and> \<Gamma> SEL = Bty \<and> \<Gamma> OUT = Bty \<and> \<Gamma> TEMP0 = Bty \<and> \<Gamma> TEMP1 = Bty
             \<or> \<Gamma> IN0 = Lty ki len \<and> \<Gamma> IN1 = Lty ki len \<and> \<Gamma> SEL = Bty \<and> \<Gamma> OUT = Lty ki len \<and> \<Gamma> TEMP0 = Lty ki len \<and> \<Gamma> TEMP1 = Lty ki len"
  apply (rule seq_wt_cases(2)[OF assms])
proof  (erule seq_wt_cases)+
  assume "bexp_wt \<Gamma> (Bsig SEL) Bty"
  assume "bexp_wt \<Gamma> (Bnand (Bsig IN0) (Bsig IN1)) (\<Gamma> TEMP0)"
  hence "\<Gamma> IN0 = \<Gamma> TEMP0 \<and> \<Gamma> IN1 = \<Gamma> TEMP0"
    by (metis bexp_wt_cases(4) bexp_wt_cases(9))    
  assume "bexp_wt \<Gamma> (Bsig TEMP0) (\<Gamma> OUT) "
  hence "\<Gamma> TEMP0 = \<Gamma> OUT"
    by (rule bexp_wt_cases_all) auto
  assume "bexp_wt \<Gamma> (Bsig TEMP1) (\<Gamma> OUT) "
  hence "\<Gamma> TEMP1 = \<Gamma> OUT"
    by (rule bexp_wt_cases_all) auto
  have "\<Gamma> SEL = Bty"
    by (rule bexp_wt_cases_all[OF \<open>bexp_wt \<Gamma> (Bsig SEL) Bty\<close>]) auto
  obtain ki len where "\<Gamma> OUT = Bty \<or> \<Gamma> OUT = Lty ki len"
    using ty.exhaust by meson
  moreover
  { assume "\<Gamma> OUT = Bty"
    hence "\<Gamma> TEMP0 = Bty"
      by (simp add: \<open>\<Gamma> TEMP0 = \<Gamma> OUT\<close>)
    moreover have "\<Gamma> TEMP1 = Bty"
      using \<open>\<Gamma> TEMP1 = \<Gamma> OUT\<close> \<open>\<Gamma> OUT = Bty\<close> by auto
    ultimately have ?thesis
      using \<open>\<Gamma> OUT = Bty\<close> \<open>\<Gamma> SEL = Bty\<close> \<open>\<Gamma> IN0 = \<Gamma> TEMP0 \<and> \<Gamma> IN1 = \<Gamma> TEMP0\<close> by auto }
  moreover
  { assume "\<Gamma> OUT = Lty ki len"
    moreover hence "\<Gamma> TEMP0 = Lty ki len" and "\<Gamma> TEMP1 = Lty ki len"
      using \<open>\<Gamma> TEMP0 = \<Gamma> OUT\<close> \<open>\<Gamma> TEMP1 = \<Gamma> OUT\<close> by auto
    ultimately have ?thesis
      using \<open>\<Gamma> SEL = Bty\<close> \<open>\<Gamma> IN0 = \<Gamma> TEMP0 \<and> \<Gamma> IN1 = \<Gamma> TEMP0\<close> by auto }
  ultimately show ?thesis
    by auto
qed

abbreviation "bval_of_wline tw sig t \<equiv> bval_of (wline_of tw sig t)"

locale scalar_type = 
  fixes \<Gamma> :: "sig tyenv"
  assumes "\<Gamma> IN0 = Bty" and "seq_wt \<Gamma> mux2_seq"
begin

definition mux2_inv :: "sig assn2" where
  "mux2_inv \<equiv> \<lambda>tw. (\<forall>i < fst tw. (bval_of_wline tw OUT   (i + 1) = (if bval_of_wline tw SEL i then bval_of_wline tw TEMP0 i else bval_of_wline tw TEMP1 i))
                               \<and> (bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<and> bval_of_wline tw IN1 i))
                               \<and> (bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<or> bval_of_wline tw IN1 i)))"

definition mux2_inv' :: "sig assn2" where
  "mux2_inv' \<equiv> (\<lambda>tw. disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of tw) \<longrightarrow>
                  (\<forall>i\<ge>fst tw. (bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL (fst tw) then bval_of_wline tw TEMP0 (fst tw)  else bval_of_wline tw TEMP1 (fst tw)))
                            \<and> (bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 (fst tw) \<and> bval_of_wline tw IN1 (fst tw)))
                            \<and> (bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 (fst tw) \<or> bval_of_wline tw IN1 (fst tw)))                             
                  ))"

subsection \<open>Proving that the sequential component preserves @{term "mux2_inv"}\<close>

lemma nonneg_delay_mux2_seq:
  "nonneg_delay mux2_seq" by auto

lemma nonneg_delay_mux2_seq_next:
  "nonneg_delay  (Bcomp (Bassign_trans TEMP1 (Bnor (Bsig IN0) (Bsig IN1)) 1) 
                        (Bguarded (Bsig SEL) (Bassign_trans OUT (Bsig TEMP0) 1) (Bassign_trans OUT (Bsig TEMP1) 1)))"
  by auto

theorem mux2_seq_hoare_next_time:
  "\<turnstile> [\<lambda>tw. mux2_inv tw \<and> wityping \<Gamma> (snd tw)] 
        mux2_seq
     [\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. mux2_inv (j, snd tw)]"
  apply (rule Conseq2[where P= "wp mux2_seq (\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. mux2_inv (j, snd tw))" and 
                            Q= "\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. mux2_inv (j, snd tw)", rotated])
    apply (rule wp_is_pre, simp, simp)
  unfolding wp_bcomp[OF nonneg_delay_mux2_seq] wp_bcomp[OF nonneg_delay_mux2_seq_next] wp_guarded wp_trans[OF zero_less_one]
proof (rule+, unfold if_bool_eq_conj, rule, rule_tac[!] impI, rule_tac[!] allI, rule_tac[!] impI, rule_tac[!] ballI)
  fix tw x xa xb xc j
  assume assms1: "mux2_inv tw \<and> wityping \<Gamma> (snd tw) "
  define tw2 where "tw2 = tw  [TEMP0, 1 :=\<^sub>2 x ]"
  define tw3 where "tw3 = tw2 [TEMP1, 1 :=\<^sub>2 xa]"
  define tw4 where "tw4 = tw3 [OUT  , 1 :=\<^sub>2 xc]"
  assume "beval_world_raw2 tw (Bnand (Bsig IN0) (Bsig IN1)) x"
  have assms2: "beval_world_raw (snd tw) (get_time tw) (Bnand (Bsig IN0) (Bsig IN1)) x"
    using \<open>beval_world_raw2 tw (Bnand (Bsig IN0) (Bsig IN1)) x\<close> unfolding beval_world_raw2_def  by auto
  have "bexp_wt \<Gamma> (Bnand (Bsig IN0) (Bsig IN1)) Bty" and "bexp_wt \<Gamma> (Bnor (Bsig IN0) (Bsig IN1)) Bty"
    using assms1 scalar_type_axioms potential_tyenv unfolding scalar_type_def 
    by (metis seq_wt_cases(2) seq_wt_cases(4))+  
  have "type_of x = Bty"
    by (rule beval_world_raw_cases[OF assms2]) (meson \<open>bexp_wt \<Gamma> (Bnand (Bsig IN0) (Bsig IN1)) Bty\<close> assms1 beval_raw_preserve_well_typedness
    wityping_def wityping_ensure_styping wityping_ensure_ttyping)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x] (Bnor (Bsig IN0) (Bsig IN1)) xa"
  hence  "beval_world_raw2 tw2 (Bnor (Bsig IN0) (Bsig IN1)) xa"
    unfolding tw2_def by auto
  hence assms3: "beval_world_raw (snd tw2) (get_time tw2) (Bnor (Bsig IN0) (Bsig IN1)) xa"
    unfolding beval_world_raw2_def  by auto
  have "type_of xa = Bty"
    apply (rule beval_world_raw_cases[OF assms3]) 
    by (smt Suc_eq_plus1 \<open>type_of x = Bty\<close> assms2 beval_cases(1) beval_cases(10) beval_cases(9)
    beval_world_raw_cases comp_apply lessI prod.sel(1) state_of_world_def tw2_def ty.distinct(1)
    type_of.elims val.distinct(1) worldline_upd2_before_dly worldline_upd2_def)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig SEL) xb \<and> is_Bv xb"
  hence  "beval_world_raw2 tw3 (Bsig SEL) xb \<and> is_Bv xb"
    unfolding tw3_def tw2_def by auto
  assume "bval_of xb"
  have "bval_of_wline tw SEL (fst tw)"
    by (metis (no_types, lifting) \<open>beval_world_raw2 tw3 (Bsig SEL) xb \<and> is_Bv xb\<close> \<open>bval_of xb\<close>
    beval_world_raw2_Bsig beval_world_raw2_deterministic eq_fst_iff less_add_one tw2_def tw3_def
    worldline_upd2_before_dly worldline_upd2_def)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig TEMP0) xc"
  hence  "beval_world_raw (snd tw3) (fst tw3) (Bsig TEMP0) xc"
    unfolding tw3_def tw2_def beval_world_raw2_def by auto
  assume *: "j \<in> {get_time tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa][ OUT, 1 :=\<^sub>2 xc]<..next_time_world tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa][ OUT, 1 :=\<^sub>2 xc]}"
  have "j \<in> {fst tw4 <.. next_time_world tw4}"
    using * unfolding tw4_def tw3_def tw2_def by auto
  have "fst tw4 < j"
    using next_time_world_at_least  using nat_less_le 
    using \<open>j \<in> {get_time tw4<..next_time_world tw4}\<close> by auto
  moreover have "fst tw = fst tw4"
    unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < j"
    by auto
  have 0: "bval_of_wline tw4 SEL (fst tw)= bval_of_wline tw SEL (fst tw)" and 1: "wline_of tw TEMP0 (fst tw) = wline_of tw4 TEMP0 (fst tw)"
   and 2: "wline_of tw TEMP1 (fst tw) =  wline_of tw4 TEMP1 (fst tw)"
    unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by simp+
  have "\<forall>i < j. (bval_of_wline tw4 OUT   (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i))
              \<and> (bval_of_wline tw4 TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i))
              \<and> (bval_of_wline tw4 TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i))"
  proof (rule, rule)
    fix i
    assume "i < j"
    have "i < fst tw \<or> fst tw \<le> i \<and> i < j - 1 \<or> i = j - 1"
      using next_time_world_at_least \<open>i  < j\<close> \<open>get_time tw = get_time tw4\<close>  by linarith
    moreover
    { assume "i < fst tw"
      have "(bval_of_wline tw OUT   (i + 1) = (if bval_of_wline tw SEL i then bval_of_wline tw TEMP0 i else bval_of_wline tw TEMP1 i))
          \<and> (bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<and> bval_of_wline tw IN1 i))
          \<and> (bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<or> bval_of_wline tw IN1 i))"
        using assms1 \<open>i < fst tw\<close> unfolding mux2_inv_def by auto
      hence " bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i) \<and>
              bval_of_wline tw4 TEMP0 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i)) \<and>
              bval_of_wline tw4 TEMP1 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i))"
        unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def using \<open>i < fst tw\<close> by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < j - 1" hence "fst tw \<le> i" and "i < j - 1"  
        by auto
      hence "(wline_of tw4 OUT (i + 1) = wline_of tw4 OUT (fst tw + 1)) \<and> (wline_of tw4 TEMP0 (i + 1) = wline_of tw4 TEMP0 (fst tw + 1)) 
           \<and> (wline_of tw4 TEMP1 (i + 1) = wline_of tw4 TEMP1 (fst tw + 1))"
        using unchanged_until_next_time_world by (smt \<open>get_time tw = get_time tw4\<close> \<open>j \<in> {get_time
        tw4<..next_time_world tw4}\<close> dual_order.strict_trans1 greaterThanAtMost_iff le_add1
        less_diff_conv not_less)
      moreover have "wline_of tw4 TEMP1 i = wline_of tw4 TEMP1 (fst tw)" and "wline_of tw4 TEMP0 i = wline_of tw4 TEMP0 (fst tw)"
          and "wline_of tw4 SEL i = wline_of tw4 SEL (fst tw)" and "wline_of tw4 IN0 i = wline_of tw4 IN0 (fst tw)" and 
              "wline_of tw4 IN1 i = wline_of tw4 IN1 (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i < j - 1\<close>
        by (metis (no_types, lifting) \<open>get_time tw = get_time tw4\<close> \<open>i < j\<close> \<open>j \<in> {get_time tw4<..next_time_world tw4}\<close> dual_order.strict_trans1 greaterThanAtMost_iff)+
      moreover have "bval_of_wline tw4 OUT (fst tw + 1) =
                      (if bval_of_wline tw4 SEL (fst tw) then bval_of_wline tw4 TEMP0 (fst tw) else bval_of_wline tw4 TEMP1 (fst tw))"
      proof -
        have "wline_of tw4 OUT (fst tw + 1) = xc"
          using \<open>fst tw \<le> i \<and> i < j - 1\<close> unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
        also have "... = wline_of tw TEMP0 (fst tw)"
          by (metis \<open>beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig TEMP0) xc\<close>
          beval_world_raw2_Bsig beval_world_raw2_deterministic fst_conv less_add_one
          worldline_upd2_before_dly worldline_upd2_def)
        also have " ... = (if bval_of_wline tw SEL (fst tw) then wline_of tw TEMP0 (fst tw) else wline_of tw TEMP1 (fst tw))"
          using \<open>bval_of_wline tw SEL (fst tw)\<close> by auto
        \<comment> \<open>notice the change from @{term "tw"} to @{term "tw4"}\<close>
        also have "... = (if bval_of_wline tw4 SEL (fst tw) then wline_of tw4 TEMP0 (fst tw) else wline_of tw4 TEMP1 (fst tw))"
          using 0 1 2 by auto
        finally show ?thesis 
          by auto
      qed 
      moreover have "bval_of_wline tw4 TEMP0 (fst tw + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<and> bval_of_wline tw4 IN1 (fst tw))"
      proof -
        have "wline_of tw4 TEMP0 (fst tw + 1) = x"
          unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
        also have "bval_of ... \<longleftrightarrow> (\<not> (bval_of_wline tw IN0 (fst tw) \<and> bval_of_wline tw IN1 (fst tw)))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
          using \<open>type_of x = Bty\<close> by simp
        also have "... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<and> bval_of_wline tw4 IN1 (fst tw))"
          unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by simp
        finally show ?thesis
          by simp
      qed  
      moreover have "bval_of_wline tw4 TEMP1 (fst tw + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<or> bval_of_wline tw4 IN1 (fst tw))"
      proof -
        have "wline_of tw4 TEMP1 (fst tw + 1) = xa"
          unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
        also have "bval_of ... \<longleftrightarrow> (\<not> (bval_of_wline tw2 IN0 (fst tw2) \<or> bval_of_wline tw2 IN1 (fst tw2)))"
          apply (rule beval_world_raw_cases[OF assms3], erule beval_cases(10))          
           apply (metis beval_cases(1) comp_apply state_of_world_def val.sel(1))
          using \<open>type_of xa = Bty\<close> by simp
        also have "... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<or> bval_of_wline tw4 IN1 (fst tw))"
          unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto 
        finally show ?thesis
          by simp
      qed 
      ultimately have "bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i) \<and>
              bval_of_wline tw4 TEMP0 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i)) \<and>
              bval_of_wline tw4 TEMP1 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i))"
        by auto }
    moreover
    { assume "i = j - 1"
      hence "wline_of tw4 OUT (i + 1) = wline_of tw4 OUT j"
        using \<open>i < j\<close> by auto
      also have "... = wline_of tw4 OUT (fst tw + 1)"
        using \<open>fst tw < j\<close> unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
      also have "bval_of ... = (if bval_of_wline tw4 SEL (fst tw) then bval_of_wline tw4 TEMP0 (fst tw) else bval_of_wline tw4 TEMP1 (fst tw))"
      proof -
        have "wline_of tw4 OUT (fst tw + 1) = wline_of tw TEMP0 (fst tw)"
          apply (rule beval_world_raw_cases[OF \<open>beval_world_raw (snd tw3) (fst tw3) (Bsig TEMP0) xc\<close>], erule beval_cases)
          by (metis (mono_tags) "1" \<open>get_time tw = get_time tw4\<close> comp_apply fst_conv less_add_one
          state_of_world_def tw4_def worldline_upd2_at_dly worldline_upd2_before_dly
          worldline_upd2_def)
        \<comment> \<open>notice that we use @{term "tw4"} on the else part; no point of using @{term "tw"}\<close>
        show ?thesis 
          using "0" "1" \<open>bval_of_wline tw SEL (get_time tw)\<close> \<open>wline_of tw4 OUT (get_time tw + 1) =
          wline_of tw TEMP0 (get_time tw)\<close> by auto
      qed
      also have "... = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i)"
        by (smt One_nat_def Suc_lessI \<open>get_time tw = get_time tw4\<close> \<open>i < j\<close> \<open>i = j - 1\<close> \<open>j \<in>
        {get_time tw4<..next_time_world tw4}\<close> add.right_neutral add_Suc_right greaterThanAtMost_iff
        less_Suc_eq_le less_add_one less_diff_conv not_less_eq unchanged_until_next_time_world)
      finally have "bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i)"
        by auto 
      moreover have "bval_of_wline tw4 TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i)"
      proof -
        have "wline_of tw4 TEMP0 (i + 1) = wline_of tw4 TEMP0 j"
          using \<open>i = j - 1\<close> \<open>i < j\<close> by auto
        also have "... = wline_of tw4 TEMP0 (fst tw + 1)"
          using \<open>fst tw < j\<close> unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
        also have "bval_of ... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<and> bval_of_wline tw4 IN1 (fst tw))"
        proof -
          have "wline_of tw4 TEMP0 (fst tw + 1) = x"
            unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
          also have "bval_of ... \<longleftrightarrow> (\<not> (bval_of_wline tw IN0 (fst tw) \<and> bval_of_wline tw IN1 (fst tw)))"
            apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
            apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
            using \<open>type_of x = Bty\<close> by auto
          also have "... \<longleftrightarrow> (\<not> (bval_of_wline tw4 IN0 (fst tw) \<and> bval_of_wline tw4 IN1 (fst tw)))"
            unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto 
          finally show ?thesis
            by simp
        qed        
        finally show ?thesis
          by (smt One_nat_def Suc_lessI \<open>get_time tw = get_time tw4\<close> \<open>i < j\<close> \<open>i = j - 1\<close> \<open>j \<in>
          {get_time tw4<..next_time_world tw4}\<close> add.right_neutral add_Suc_right
          greaterThanAtMost_iff less_Suc_eq_le less_add_one less_diff_conv not_less_eq
          unchanged_until_next_time_world)
      qed
      moreover have "bval_of_wline tw4 TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i)"
      proof -
        have "wline_of tw4 TEMP1 (i + 1) = wline_of tw4 TEMP1 j"
          using \<open>i = j - 1\<close> \<open>i < j\<close> by auto
        also have "... = wline_of tw4 TEMP1 (fst tw + 1)"
          using \<open>fst tw < j\<close> unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
        also have "bval_of ... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<or> bval_of_wline tw4 IN1 (fst tw))"
        proof -
          have "wline_of tw4 TEMP1 (fst tw + 1) = xa"
            unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
          also have "bval_of ... \<longleftrightarrow> (\<not> (bval_of_wline tw2 IN0 (fst tw2) \<or> bval_of_wline tw2 IN1 (fst tw2)))"
            apply (rule beval_world_raw_cases[OF assms3], erule beval_cases)
            apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
            using \<open>type_of xa = Bty\<close> by auto
          also have "... \<longleftrightarrow> (\<not> (bval_of_wline tw4 IN0 (fst tw) \<or> bval_of_wline tw4 IN1 (fst tw)))"
            unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto 
          finally show ?thesis
            by simp
        qed        
        finally show ?thesis
          by (smt One_nat_def Suc_lessI \<open>get_time tw = get_time tw4\<close> \<open>i < j\<close> \<open>i = j - 1\<close> \<open>j \<in>
          {get_time tw4<..next_time_world tw4}\<close> add.right_neutral add_Suc_right
          greaterThanAtMost_iff less_Suc_eq_le less_add_one less_diff_conv not_less_eq
          unchanged_until_next_time_world)
      qed
      ultimately have "bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i) \<and>
              bval_of_wline tw4 TEMP0 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i)) \<and>
              bval_of_wline tw4 TEMP1 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i))"
        by auto }
    ultimately show "bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i) \<and>
              bval_of_wline tw4 TEMP0 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i)) \<and>
              bval_of_wline tw4 TEMP1 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i))"
      by auto 
  qed
  thus "mux2_inv (j, snd tw4)"
    unfolding mux2_inv_def by auto
next
  fix tw x xa xb xc j
  assume assms1: "mux2_inv tw \<and> wityping \<Gamma> (snd tw) "
  define tw2 where "tw2 = tw  [TEMP0, 1 :=\<^sub>2 x ]"
  define tw3 where "tw3 = tw2 [TEMP1, 1 :=\<^sub>2 xa]"
  define tw4 where "tw4 = tw3 [OUT  , 1 :=\<^sub>2 xc]"
  assume "beval_world_raw2 tw (Bnand (Bsig IN0) (Bsig IN1)) x"
  have assms2: "beval_world_raw (snd tw) (get_time tw) (Bnand (Bsig IN0) (Bsig IN1)) x"
    using \<open>beval_world_raw2 tw (Bnand (Bsig IN0) (Bsig IN1)) x\<close> unfolding beval_world_raw2_def  by auto
  have "bexp_wt \<Gamma> (Bnand (Bsig IN0) (Bsig IN1)) Bty" and "bexp_wt \<Gamma> (Bnor (Bsig IN0) (Bsig IN1)) Bty"
    using assms1 scalar_type_axioms potential_tyenv unfolding scalar_type_def 
    by (metis seq_wt_cases(2) seq_wt_cases(4))+  
  have "type_of x = Bty"
    by (rule beval_world_raw_cases[OF assms2]) (meson \<open>bexp_wt \<Gamma> (Bnand (Bsig IN0) (Bsig IN1)) Bty\<close> assms1 beval_raw_preserve_well_typedness
    wityping_def wityping_ensure_styping wityping_ensure_ttyping)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x] (Bnor (Bsig IN0) (Bsig IN1)) xa"
  hence  "beval_world_raw2 tw2 (Bnor (Bsig IN0) (Bsig IN1)) xa"
    unfolding tw2_def by auto
  hence assms3: "beval_world_raw (snd tw2) (get_time tw2) (Bnor (Bsig IN0) (Bsig IN1)) xa"
    unfolding beval_world_raw2_def  by auto
  have "type_of xa = Bty"
    apply (rule beval_world_raw_cases[OF assms3]) 
    by (smt Suc_eq_plus1 \<open>type_of x = Bty\<close> assms2 beval_cases(1) beval_cases(10) beval_cases(9)
    beval_world_raw_cases comp_apply lessI prod.sel(1) state_of_world_def tw2_def ty.distinct(1)
    type_of.elims val.distinct(1) worldline_upd2_before_dly worldline_upd2_def)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig SEL) xb \<and> is_Bv xb"
  hence  "beval_world_raw2 tw3 (Bsig SEL) xb \<and> is_Bv xb"
    unfolding tw3_def tw2_def by auto
  assume "\<not> bval_of xb"
  have "\<not> bval_of_wline tw SEL (fst tw)"
    by (metis (no_types, lifting) \<open>beval_world_raw2 tw3 (Bsig SEL) xb \<and> is_Bv xb\<close> \<open>\<not> bval_of xb\<close>
    beval_world_raw2_Bsig beval_world_raw2_deterministic eq_fst_iff less_add_one tw2_def tw3_def
    worldline_upd2_before_dly worldline_upd2_def)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig TEMP1) xc"
  hence  "beval_world_raw (snd tw3) (fst tw3) (Bsig TEMP1) xc"
    unfolding tw3_def tw2_def beval_world_raw2_def by auto
  assume *: "j \<in> {get_time tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa][ OUT, 1 :=\<^sub>2 xc]<..next_time_world tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa][ OUT, 1 :=\<^sub>2 xc]}"
  have "j \<in> {fst tw4 <.. next_time_world tw4}"
    using * unfolding tw4_def tw3_def tw2_def by auto
  have "fst tw4 < j"
    using next_time_world_at_least  using nat_less_le 
    using \<open>j \<in> {get_time tw4<..next_time_world tw4}\<close> by auto
  moreover have "fst tw = fst tw4"
    unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < j"
    by auto
  have 0: "bval_of_wline tw4 SEL (fst tw)= bval_of_wline tw SEL (fst tw)" and 1: "wline_of tw TEMP0 (fst tw) = wline_of tw4 TEMP0 (fst tw)"
   and 2: "wline_of tw TEMP1 (fst tw) =  wline_of tw4 TEMP1 (fst tw)"
    unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by simp+
  have "\<forall>i < j. (bval_of_wline tw4 OUT   (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i))
              \<and> (bval_of_wline tw4 TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i))
              \<and> (bval_of_wline tw4 TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i))"
  proof (rule, rule)
    fix i
    assume "i < j"
    have "i < fst tw \<or> fst tw \<le> i \<and> i < j - 1 \<or> i = j - 1"
      using next_time_world_at_least \<open>i  < j\<close> \<open>get_time tw = get_time tw4\<close>  by linarith
    moreover
    { assume "i < fst tw"
      have "(bval_of_wline tw OUT   (i + 1) = (if bval_of_wline tw SEL i then bval_of_wline tw TEMP0 i else bval_of_wline tw TEMP1 i))
          \<and> (bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<and> bval_of_wline tw IN1 i))
          \<and> (bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<or> bval_of_wline tw IN1 i))"
        using assms1 \<open>i < fst tw\<close> unfolding mux2_inv_def by auto
      hence " bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i) \<and>
              bval_of_wline tw4 TEMP0 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i)) \<and>
              bval_of_wline tw4 TEMP1 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i))"
        unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def using \<open>i < fst tw\<close> by auto }
    moreover
    { assume "fst tw \<le> i \<and> i < j - 1" hence "fst tw \<le> i" and "i < j - 1"  
        by auto
      hence "(wline_of tw4 OUT (i + 1) = wline_of tw4 OUT (fst tw + 1)) \<and> (wline_of tw4 TEMP0 (i + 1) = wline_of tw4 TEMP0 (fst tw + 1)) 
           \<and> (wline_of tw4 TEMP1 (i + 1) = wline_of tw4 TEMP1 (fst tw + 1))"
        using unchanged_until_next_time_world by (smt \<open>get_time tw = get_time tw4\<close> \<open>j \<in> {get_time
        tw4<..next_time_world tw4}\<close> dual_order.strict_trans1 greaterThanAtMost_iff le_add1
        less_diff_conv not_less)
      moreover have "wline_of tw4 TEMP1 i = wline_of tw4 TEMP1 (fst tw)" and "wline_of tw4 TEMP0 i = wline_of tw4 TEMP0 (fst tw)"
          and "wline_of tw4 SEL i = wline_of tw4 SEL (fst tw)" and "wline_of tw4 IN0 i = wline_of tw4 IN0 (fst tw)" and 
              "wline_of tw4 IN1 i = wline_of tw4 IN1 (fst tw)"
        using unchanged_until_next_time_world \<open>fst tw \<le> i \<and> i < j - 1\<close>
        by (metis (no_types, lifting) \<open>get_time tw = get_time tw4\<close> \<open>i < j\<close> \<open>j \<in> {get_time tw4<..next_time_world tw4}\<close> dual_order.strict_trans1 greaterThanAtMost_iff)+
      moreover have "bval_of_wline tw4 OUT (fst tw + 1) =
                      (if bval_of_wline tw4 SEL (fst tw) then bval_of_wline tw4 TEMP0 (fst tw) else bval_of_wline tw4 TEMP1 (fst tw))"
      proof -
        have "wline_of tw4 OUT (fst tw + 1) = xc"
          using \<open>fst tw \<le> i \<and> i < j - 1\<close> unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
        also have "... = wline_of tw TEMP1 (fst tw)"
          by (metis \<open>beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig TEMP1) xc\<close>
          beval_world_raw2_Bsig beval_world_raw2_deterministic fst_conv less_add_one
          worldline_upd2_before_dly worldline_upd2_def)
        also have " ... = (if bval_of_wline tw SEL (fst tw) then wline_of tw TEMP0 (fst tw) else wline_of tw TEMP1 (fst tw))"
          using \<open>\<not> bval_of_wline tw SEL (fst tw)\<close> by auto
        \<comment> \<open>notice the change from @{term "tw"} to @{term "tw4"}\<close>
        also have "... = (if bval_of_wline tw4 SEL (fst tw) then wline_of tw4 TEMP0 (fst tw) else wline_of tw4 TEMP1 (fst tw))"
          using 0 1 2 by auto
        finally show ?thesis 
          by auto
      qed 
      moreover have "bval_of_wline tw4 TEMP0 (fst tw + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<and> bval_of_wline tw4 IN1 (fst tw))"
      proof -
        have "wline_of tw4 TEMP0 (fst tw + 1) = x"
          unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
        also have "bval_of ... \<longleftrightarrow> (\<not> (bval_of_wline tw IN0 (fst tw) \<and> bval_of_wline tw IN1 (fst tw)))"
          apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
          apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
          using \<open>type_of x = Bty\<close> by simp
        also have "... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<and> bval_of_wline tw4 IN1 (fst tw))"
          unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by simp
        finally show ?thesis
          by simp
      qed  
      moreover have "bval_of_wline tw4 TEMP1 (fst tw + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<or> bval_of_wline tw4 IN1 (fst tw))"
      proof -
        have "wline_of tw4 TEMP1 (fst tw + 1) = xa"
          unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
        also have "bval_of ... \<longleftrightarrow> (\<not> (bval_of_wline tw2 IN0 (fst tw2) \<or> bval_of_wline tw2 IN1 (fst tw2)))"
          apply (rule beval_world_raw_cases[OF assms3], erule beval_cases(10))          
           apply (metis beval_cases(1) comp_apply state_of_world_def val.sel(1))
          using \<open>type_of xa = Bty\<close> by simp
        also have "... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<or> bval_of_wline tw4 IN1 (fst tw))"
          unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto 
        finally show ?thesis
          by simp
      qed 
      ultimately have "bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i) \<and>
              bval_of_wline tw4 TEMP0 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i)) \<and>
              bval_of_wline tw4 TEMP1 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i))"
        by auto }
    moreover
    { assume "i = j - 1"
      hence "wline_of tw4 OUT (i + 1) = wline_of tw4 OUT j"
        using \<open>i < j\<close> by auto
      also have "... = wline_of tw4 OUT (fst tw + 1)"
        using \<open>fst tw < j\<close> unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
      also have "bval_of ... = (if bval_of_wline tw4 SEL (fst tw) then bval_of_wline tw4 TEMP0 (fst tw) else bval_of_wline tw4 TEMP1 (fst tw))"
      proof -
        have "wline_of tw4 OUT (fst tw + 1) = wline_of tw TEMP1 (fst tw)"
          apply (rule beval_world_raw_cases[OF \<open>beval_world_raw (snd tw3) (fst tw3) (Bsig TEMP1) xc\<close>], erule beval_cases)
          by (metis (mono_tags) "2" \<open>get_time tw = get_time tw4\<close> comp_apply fst_conv less_add_one
          state_of_world_def tw4_def worldline_upd2_at_dly worldline_upd2_before_dly
          worldline_upd2_def)
        \<comment> \<open>notice that we use @{term "tw4"} on the else part; no point of using @{term "tw"}\<close>
        thus ?thesis 
          using "0" "1" \<open>\<not> bval_of_wline tw SEL (get_time tw)\<close>  using "2" by auto          
      qed
      also have "... = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i)"
        by (smt One_nat_def Suc_lessI \<open>get_time tw = get_time tw4\<close> \<open>i < j\<close> \<open>i = j - 1\<close> \<open>j \<in>
        {get_time tw4<..next_time_world tw4}\<close> add.right_neutral add_Suc_right greaterThanAtMost_iff
        less_Suc_eq_le less_add_one less_diff_conv not_less_eq unchanged_until_next_time_world)
      finally have "bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i)"
        by auto 
      moreover have "bval_of_wline tw4 TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i)"
      proof -
        have "wline_of tw4 TEMP0 (i + 1) = wline_of tw4 TEMP0 j"
          using \<open>i = j - 1\<close> \<open>i < j\<close> by auto
        also have "... = wline_of tw4 TEMP0 (fst tw + 1)"
          using \<open>fst tw < j\<close> unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
        also have "bval_of ... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<and> bval_of_wline tw4 IN1 (fst tw))"
        proof -
          have "wline_of tw4 TEMP0 (fst tw + 1) = x"
            unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
          also have "bval_of ... \<longleftrightarrow> (\<not> (bval_of_wline tw IN0 (fst tw) \<and> bval_of_wline tw IN1 (fst tw)))"
            apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
            apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
            using \<open>type_of x = Bty\<close> by auto
          also have "... \<longleftrightarrow> (\<not> (bval_of_wline tw4 IN0 (fst tw) \<and> bval_of_wline tw4 IN1 (fst tw)))"
            unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto 
          finally show ?thesis
            by simp
        qed        
        finally show ?thesis
          by (smt One_nat_def Suc_lessI \<open>get_time tw = get_time tw4\<close> \<open>i < j\<close> \<open>i = j - 1\<close> \<open>j \<in>
          {get_time tw4<..next_time_world tw4}\<close> add.right_neutral add_Suc_right
          greaterThanAtMost_iff less_Suc_eq_le less_add_one less_diff_conv not_less_eq
          unchanged_until_next_time_world)
      qed
      moreover have "bval_of_wline tw4 TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i)"
      proof -
        have "wline_of tw4 TEMP1 (i + 1) = wline_of tw4 TEMP1 j"
          using \<open>i = j - 1\<close> \<open>i < j\<close> by auto
        also have "... = wline_of tw4 TEMP1 (fst tw + 1)"
          using \<open>fst tw < j\<close> unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
        also have "bval_of ... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 (fst tw) \<or> bval_of_wline tw4 IN1 (fst tw))"
        proof -
          have "wline_of tw4 TEMP1 (fst tw + 1) = xa"
            unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
          also have "bval_of ... \<longleftrightarrow> (\<not> (bval_of_wline tw2 IN0 (fst tw2) \<or> bval_of_wline tw2 IN1 (fst tw2)))"
            apply (rule beval_world_raw_cases[OF assms3], erule beval_cases)
            apply (smt beval_cases(1) comp_apply state_of_world_def val.sel(1))
            using \<open>type_of xa = Bty\<close> by auto
          also have "... \<longleftrightarrow> (\<not> (bval_of_wline tw4 IN0 (fst tw) \<or> bval_of_wline tw4 IN1 (fst tw)))"
            unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto 
          finally show ?thesis
            by simp
        qed        
        finally show ?thesis
          by (smt One_nat_def Suc_lessI \<open>get_time tw = get_time tw4\<close> \<open>i < j\<close> \<open>i = j - 1\<close> \<open>j \<in>
          {get_time tw4<..next_time_world tw4}\<close> add.right_neutral add_Suc_right
          greaterThanAtMost_iff less_Suc_eq_le less_add_one less_diff_conv not_less_eq
          unchanged_until_next_time_world)
      qed
      ultimately have "bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i) \<and>
              bval_of_wline tw4 TEMP0 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i)) \<and>
              bval_of_wline tw4 TEMP1 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i))"
        by auto }
    ultimately show "bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline tw4 SEL i then bval_of_wline tw4 TEMP0 i else bval_of_wline tw4 TEMP1 i) \<and>
              bval_of_wline tw4 TEMP0 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<and> bval_of_wline tw4 IN1 i)) \<and>
              bval_of_wline tw4 TEMP1 (i + 1) = (\<not> (bval_of_wline tw4 IN0 i \<or> bval_of_wline tw4 IN1 i))"
      by auto 
  qed
  thus "mux2_inv (j, snd tw4)"
    unfolding mux2_inv_def by auto
qed

theorem mux2_seq_hoare_next_time_wityping:
  shows"
   \<turnstile> [\<lambda>tw. mux2_inv tw \<and> wityping \<Gamma> (snd tw)] mux2_seq
     [\<lambda>tw. mux2_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
   apply (rule Conseq2[rotated])
     apply (rule mux2_seq_hoare_next_time)
    apply (simp add: next_time_world_at_least)
  apply simp
  apply (rule strengthen_precondition2)
  apply (rule seq_stmt_preserve_wityping_hoare)
  using scalar_type_axioms unfolding scalar_type_def by auto

theorem mux2_seq_hoare_next_time0:
  "\<turnstile> [\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)] mux2_seq
     [\<lambda>tw. mux2_inv (next_time_world tw, snd tw)]"
  apply (rule Conseq2[where P="\<lambda>tw. mux2_inv tw \<and> wityping \<Gamma> (snd tw)" and Q="\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. mux2_inv (j, snd tw)"])
    apply (simp add: mux2_inv_def)
  apply (rule mux2_seq_hoare_next_time)
  by (simp add: next_time_world_at_least)

theorem mux2_seq_hoare_next_time0_wityping:
  shows
  "\<turnstile> [\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)] mux2_seq
     [\<lambda>tw. mux2_inv (next_time_world tw, snd tw) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
   apply (rule mux2_seq_hoare_next_time0)
  apply (rule strengthen_precondition2)
  apply (rule seq_stmt_preserve_wityping_hoare)
  using scalar_type_axioms unfolding scalar_type_def by auto

subsection \<open>Proving that the sequential component preserves @{term "mux2_inv'"}\<close>

lemma input_signals_unchanged:
  fixes tw any
  assumes "beval_world_raw2 tw (Bsig any) v"
  defines "tw' \<equiv> tw[ OUT, 1 :=\<^sub>2 v]"
  defines "t' \<equiv> next_time_world tw'"
  assumes "disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of (t', snd tw'))"
  shows "\<And>s. s \<in> {IN0, IN1, SEL, TEMP0, TEMP1} \<Longrightarrow> wline_of tw' s t' = wline_of tw s (fst tw)"
proof -
  fix s
  assume "s \<in> {IN0, IN1, SEL, TEMP0, TEMP1}"
  have "fst tw' < t'"
    using next_time_world_at_least unfolding t'_def by blast
  moreover have "fst tw = fst tw'"
    unfolding tw'_def unfolding worldline_upd2_def by auto
  ultimately have "fst tw < t'"
    by auto
  have "wline_of tw' s t' = wline_of tw s t'"
    using \<open>s \<in> {IN0, IN1, SEL, TEMP0, TEMP1}\<close> unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
  also have "... = wline_of tw s (t' - 1)"
    using \<open>disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of (t', snd tw'))\<close> \<open>fst tw < t'\<close>
    unfolding event_of_alt_def  tw'_def worldline_upd2_def worldline_upd_def using \<open>s \<in> {IN0, IN1, SEL, TEMP0, TEMP1}\<close>
    by auto
  also have "... = wline_of tw s (fst tw)"
  proof -
    have "fst tw' \<le> t' - 1" and "t' - 1 < t'"
      using \<open>fst tw' < t'\<close> by auto
    hence "wline_of tw' s (t' - 1) = wline_of tw' s (fst tw')"
      using unchanged_until_next_time_world[where tw="tw'"] unfolding t'_def by blast
    moreover have "wline_of tw' s (t' - 1) = wline_of tw s (t' - 1)"
      unfolding tw'_def worldline_upd2_def worldline_upd_def  using \<open>s \<in> {IN0, IN1, SEL, TEMP0, TEMP1}\<close> by auto
    moreover have "wline_of tw' s (fst tw') = wline_of tw s (fst tw')"
      unfolding tw'_def worldline_upd2_def worldline_upd_def by auto
    ultimately show ?thesis
      using \<open>fst tw = fst tw'\<close> by auto
  qed
  finally show "wline_of tw' s t' = wline_of tw s (fst tw)"
    by auto
qed

theorem mux2_seq_hoare_next_time':
  "\<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] 
        mux2_seq 
     [\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. mux2_inv' (j, snd tw)]"
  apply (rule Conseq2[where P= "wp mux2_seq (\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. mux2_inv' (j, snd tw))" and 
                            Q= "\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. mux2_inv' (j, snd tw)", rotated])
    apply (rule wp_is_pre, simp, simp)
  unfolding wp_bcomp[OF nonneg_delay_mux2_seq] wp_bcomp[OF nonneg_delay_mux2_seq_next] wp_guarded wp_trans[OF zero_less_one]
proof (rule+, unfold if_bool_eq_conj, rule, rule_tac[!] impI, rule_tac[!] allI, rule_tac[!] impI, rule_tac[!] ballI)
  fix tw :: "nat \<times> (sig \<Rightarrow> val) \<times> (sig \<Rightarrow> nat \<Rightarrow> val)"
  fix x xa xb xc j
  assume assms1: "wityping \<Gamma> (snd tw) "
  define tw2 where "tw2 = tw  [TEMP0, 1 :=\<^sub>2 x ]"
  define tw3 where "tw3 = tw2 [TEMP1, 1 :=\<^sub>2 xa]"
  define tw4 where "tw4 = tw3 [OUT  , 1 :=\<^sub>2 xc]"
  assume "beval_world_raw2 tw (Bnand (Bsig IN0) (Bsig IN1)) x"
  have assms2: "beval_world_raw (snd tw) (get_time tw) (Bnand (Bsig IN0) (Bsig IN1)) x"
    using \<open>beval_world_raw2 tw (Bnand (Bsig IN0) (Bsig IN1)) x\<close> unfolding beval_world_raw2_def  by auto
  have "bexp_wt \<Gamma> (Bnand (Bsig IN0) (Bsig IN1)) Bty" and "bexp_wt \<Gamma> (Bnor (Bsig IN0) (Bsig IN1)) Bty"
    using assms1 scalar_type_axioms potential_tyenv unfolding scalar_type_def 
    by (metis seq_wt_cases(2) seq_wt_cases(4))+  
  have "type_of x = Bty"
    by (rule beval_world_raw_cases[OF assms2]) (meson \<open>bexp_wt \<Gamma> (Bnand (Bsig IN0) (Bsig IN1)) Bty\<close> assms1 beval_raw_preserve_well_typedness
    wityping_def wityping_ensure_styping wityping_ensure_ttyping)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x] (Bnor (Bsig IN0) (Bsig IN1)) xa"
  hence  "beval_world_raw2 tw2 (Bnor (Bsig IN0) (Bsig IN1)) xa"
    unfolding tw2_def by auto
  hence assms3: "beval_world_raw (snd tw2) (get_time tw2) (Bnor (Bsig IN0) (Bsig IN1)) xa"
    unfolding beval_world_raw2_def  by auto
  have "type_of xa = Bty"
    apply (rule beval_world_raw_cases[OF assms3]) 
    by (smt Suc_eq_plus1 \<open>type_of x = Bty\<close> assms2 beval_cases(1) beval_cases(10) beval_cases(9)
    beval_world_raw_cases comp_apply lessI prod.sel(1) state_of_world_def tw2_def ty.distinct(1)
    type_of.elims val.distinct(1) worldline_upd2_before_dly worldline_upd2_def)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig SEL) xb \<and> is_Bv xb"
  hence  "beval_world_raw2 tw3 (Bsig SEL) xb \<and> is_Bv xb"
    unfolding tw3_def tw2_def by auto
  assume "bval_of xb"
  have "bval_of_wline tw SEL (fst tw)"
    by (metis (no_types, lifting) \<open>beval_world_raw2 tw3 (Bsig SEL) xb \<and> is_Bv xb\<close> \<open>bval_of xb\<close>
    beval_world_raw2_Bsig beval_world_raw2_deterministic eq_fst_iff less_add_one tw2_def tw3_def
    worldline_upd2_before_dly worldline_upd2_def)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig TEMP0) xc"
  hence  "beval_world_raw (snd tw3) (fst tw3) (Bsig TEMP0) xc"
    unfolding tw3_def tw2_def beval_world_raw2_def by auto
  assume *: "j \<in> {get_time tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa][ OUT, 1 :=\<^sub>2 xc]<..next_time_world tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa][ OUT, 1 :=\<^sub>2 xc]}"
  have "j \<in> {fst tw4 <.. next_time_world tw4}"
    using * unfolding tw4_def tw3_def tw2_def by auto
  have "fst tw4 < j"
    using next_time_world_at_least  using nat_less_le 
    using \<open>j \<in> {get_time tw4<..next_time_world tw4}\<close> by auto
  moreover have "fst tw = fst tw4"
    unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < j"
    by auto
  have "mux2_inv' (j, snd tw4)"
    unfolding mux2_inv'_def
  proof (rule, rule, rule)
    fix i
    assume "disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of (j, snd tw4)) "
    assume "fst (j, snd tw4) \<le> i" hence "j \<le> i" by auto
    have *: "\<And>s. s \<in> {IN0, IN1, SEL, TEMP0, TEMP1} \<Longrightarrow> wline_of tw4 s j = wline_of tw3 s (fst tw3)"
      using \<open>disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of (j, snd tw4))\<close>
      input_signals_unchanged unfolding tw4_def
      by (smt "*" Pair_inject \<open>beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig TEMP0)
      xc\<close> antisym_conv1 greaterThanAtMost_iff less_add_one less_imp_le_nat prod.collapse tw2_def
      tw3_def unchanged_until_next_time_world worldline_upd2_before_dly worldline_upd2_def)
    have "wline_of tw4 OUT (i + 1) = xc"
      unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def 
      using \<open>get_time tw = get_time tw4\<close> \<open>get_time tw4 < j\<close> \<open>j \<le> i\<close> by auto
    also have "bval_of ... = bval_of_wline tw TEMP0 (fst tw)"
      apply (rule beval_world_raw_cases[OF \<open>beval_world_raw (snd tw3) (fst tw3) (Bsig TEMP0) xc\<close>], erule beval_cases)
      unfolding tw3_def tw2_def
      by (metis (mono_tags) Suc_eq_plus1 comp_apply eq_fst_iff lessI state_of_world_def worldline_upd2_before_dly worldline_upd2_def)
    also have "... = (if bval_of_wline tw SEL (fst tw) then bval_of_wline tw TEMP0 (fst tw) else bval_of_wline tw TEMP1 (fst tw))"
      using \<open>bval_of_wline tw SEL (fst tw)\<close>  by (simp add: state_of_world_def)
    also have "... = (if bval_of_wline tw3 SEL (fst tw3) then bval_of_wline tw3 TEMP0 (fst tw3) else bval_of_wline tw3 TEMP1 (fst tw3))"
      using \<open>bval_of_wline tw SEL (fst tw)\<close>  unfolding tw3_def tw2_def worldline_upd2_def worldline_upd_def 
      by auto
    also have "... = (if bval_of_wline tw4 SEL j then bval_of_wline tw4 TEMP0 j else bval_of_wline tw4 TEMP1 j)"
      using * by auto
    finally have temp1: "bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline (j, snd tw4) SEL (get_time (j, snd tw4)) then bval_of_wline (j, snd tw4) TEMP0 (get_time (j, snd tw4))
          else bval_of_wline (j, snd tw4) TEMP1 (get_time (j, snd tw4)))"
      by auto

    have "wline_of tw4 TEMP0 (i + 1) = x"
      unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def 
      using \<open>get_time tw = get_time tw4\<close> \<open>get_time tw4 < j\<close> \<open>j \<le> i\<close> by auto    
    also have "bval_of ... \<longleftrightarrow> \<not> (bval_of_wline tw IN0 (fst tw) \<and> bval_of_wline tw IN1 (fst tw))"
      apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
      apply (metis beval_cases(1) comp_apply state_of_world_def val.sel(1))
      using \<open>type_of x = Bty\<close> by auto
    also have "... \<longleftrightarrow> \<not> (bval_of_wline tw3 IN0 (fst tw3) \<and> bval_of_wline tw3 IN1 (fst tw3))"
      unfolding tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
    also have "... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 j \<and> bval_of_wline tw4 IN1 j)"
      using * by auto
    finally have temp2: "bval_of_wline (j, snd tw4) TEMP0 (i + 1) =
         (\<not> (bval_of_wline (j, snd tw4) IN0 (get_time (j, snd tw4)) \<and> bval_of_wline (j, snd tw4) IN1 (get_time (j, snd tw4))))"
      by auto

    have "wline_of tw4 TEMP1 (i + 1) = xa"
      unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def 
      using \<open>get_time tw = get_time tw4\<close> \<open>get_time tw4 < j\<close> \<open>j \<le> i\<close> by auto    
    also have "bval_of ... \<longleftrightarrow> \<not> (bval_of_wline tw2 IN0 (fst tw2) \<or> bval_of_wline tw2 IN1 (fst tw2))"
      apply (rule beval_world_raw_cases[OF assms3], erule beval_cases)
      apply (metis beval_cases(1) comp_apply state_of_world_def val.sel(1))
      using \<open>type_of xa = Bty\<close> by auto
    also have "... \<longleftrightarrow> \<not> (bval_of_wline tw3 IN0 (fst tw3) \<or> bval_of_wline tw3 IN1 (fst tw3))"
      unfolding tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
    also have "... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 j \<or> bval_of_wline tw4 IN1 j)"
      using * by auto
    finally have temp3: "bval_of_wline (j, snd tw4) TEMP1 (i + 1) =
         (\<not> (bval_of_wline (j, snd tw4) IN0 (get_time (j, snd tw4)) \<or> bval_of_wline (j, snd tw4) IN1 (get_time (j, snd tw4))))"
      by auto
    show "bval_of_wline (j, snd tw4) OUT (i + 1) =
         (if bval_of_wline (j, snd tw4) SEL (get_time (j, snd tw4)) then bval_of_wline (j, snd tw4) TEMP0 (get_time (j, snd tw4))
          else bval_of_wline (j, snd tw4) TEMP1 (get_time (j, snd tw4))) \<and>
         bval_of_wline (j, snd tw4) TEMP0 (i + 1) =
         (\<not> (bval_of_wline (j, snd tw4) IN0 (get_time (j, snd tw4)) \<and> bval_of_wline (j, snd tw4) IN1 (get_time (j, snd tw4)))) \<and>
         bval_of_wline (j, snd tw4) TEMP1 (i + 1) = (\<not> (bval_of_wline (j, snd tw4) IN0 (get_time (j, snd tw4)) \<or> bval_of_wline (j, snd tw4) IN1 (get_time (j, snd tw4))))"
      using temp1 temp2 temp3 by auto
  qed
  thus "mux2_inv' (j, snd tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa][ OUT, 1 :=\<^sub>2 xc])"
    unfolding tw4_def tw3_def tw2_def by auto
next
  fix tw :: "nat \<times> (sig \<Rightarrow> val) \<times> (sig \<Rightarrow> nat \<Rightarrow> val)"
  fix x xa xb xc j
  assume assms1: "wityping \<Gamma> (snd tw) "
  define tw2 where "tw2 = tw  [TEMP0, 1 :=\<^sub>2 x ]"
  define tw3 where "tw3 = tw2 [TEMP1, 1 :=\<^sub>2 xa]"
  define tw4 where "tw4 = tw3 [OUT  , 1 :=\<^sub>2 xc]"
  assume "beval_world_raw2 tw (Bnand (Bsig IN0) (Bsig IN1)) x"
  have assms2: "beval_world_raw (snd tw) (get_time tw) (Bnand (Bsig IN0) (Bsig IN1)) x"
    using \<open>beval_world_raw2 tw (Bnand (Bsig IN0) (Bsig IN1)) x\<close> unfolding beval_world_raw2_def  by auto
  have "bexp_wt \<Gamma> (Bnand (Bsig IN0) (Bsig IN1)) Bty" and "bexp_wt \<Gamma> (Bnor (Bsig IN0) (Bsig IN1)) Bty"
    using assms1 scalar_type_axioms potential_tyenv unfolding scalar_type_def 
    by (metis seq_wt_cases(2) seq_wt_cases(4))+  
  have "type_of x = Bty"
    by (rule beval_world_raw_cases[OF assms2]) (meson \<open>bexp_wt \<Gamma> (Bnand (Bsig IN0) (Bsig IN1)) Bty\<close> assms1 beval_raw_preserve_well_typedness
    wityping_def wityping_ensure_styping wityping_ensure_ttyping)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x] (Bnor (Bsig IN0) (Bsig IN1)) xa"
  hence  "beval_world_raw2 tw2 (Bnor (Bsig IN0) (Bsig IN1)) xa"
    unfolding tw2_def by auto
  hence assms3: "beval_world_raw (snd tw2) (get_time tw2) (Bnor (Bsig IN0) (Bsig IN1)) xa"
    unfolding beval_world_raw2_def  by auto
  have "type_of xa = Bty"
    apply (rule beval_world_raw_cases[OF assms3]) 
    by (smt Suc_eq_plus1 \<open>type_of x = Bty\<close> assms2 beval_cases(1) beval_cases(10) beval_cases(9)
    beval_world_raw_cases comp_apply lessI prod.sel(1) state_of_world_def tw2_def ty.distinct(1)
    type_of.elims val.distinct(1) worldline_upd2_before_dly worldline_upd2_def)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig SEL) xb \<and> is_Bv xb"
  hence  "beval_world_raw2 tw3 (Bsig SEL) xb \<and> is_Bv xb"
    unfolding tw3_def tw2_def by auto
  assume "\<not> bval_of xb"
  have "\<not> bval_of_wline tw SEL (fst tw)"
    by (metis (no_types, lifting) \<open>beval_world_raw2 tw3 (Bsig SEL) xb \<and> is_Bv xb\<close> \<open>\<not> bval_of xb\<close>
    beval_world_raw2_Bsig beval_world_raw2_deterministic eq_fst_iff less_add_one tw2_def tw3_def
    worldline_upd2_before_dly worldline_upd2_def)
  assume "beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig TEMP1) xc"
  hence  "beval_world_raw (snd tw3) (fst tw3) (Bsig TEMP1) xc"
    unfolding tw3_def tw2_def beval_world_raw2_def by auto
  assume *: "j \<in> {get_time tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa][ OUT, 1 :=\<^sub>2 xc]<..next_time_world tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa][ OUT, 1 :=\<^sub>2 xc]}"
  have "j \<in> {fst tw4 <.. next_time_world tw4}"
    using * unfolding tw4_def tw3_def tw2_def by auto
  have "fst tw4 < j"
    using next_time_world_at_least  using nat_less_le 
    using \<open>j \<in> {get_time tw4<..next_time_world tw4}\<close> by auto
  moreover have "fst tw = fst tw4"
    unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
  ultimately have "fst tw < j"
    by auto
  have "mux2_inv' (j, snd tw4)"
    unfolding mux2_inv'_def
  proof (rule, rule, rule)
    fix i
    assume "disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of (j, snd tw4)) "
    assume "fst (j, snd tw4) \<le> i" hence "j \<le> i" by auto
    have *: "\<And>s. s \<in> {IN0, IN1, SEL, TEMP0, TEMP1} \<Longrightarrow> wline_of tw4 s j = wline_of tw3 s (fst tw3)"
      using \<open>disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of (j, snd tw4))\<close>
      input_signals_unchanged unfolding tw4_def
      by (smt "*" Pair_inject \<open>beval_world_raw2 tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa] (Bsig TEMP1)
      xc\<close> antisym_conv1 greaterThanAtMost_iff less_add_one less_imp_le_nat prod.collapse tw2_def
      tw3_def unchanged_until_next_time_world worldline_upd2_before_dly worldline_upd2_def)
    have "wline_of tw4 OUT (i + 1) = xc"
      unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def 
      using \<open>get_time tw = get_time tw4\<close> \<open>get_time tw4 < j\<close> \<open>j \<le> i\<close> by auto
    also have "bval_of ... = bval_of_wline tw TEMP1 (fst tw)"
      apply (rule beval_world_raw_cases[OF \<open>beval_world_raw (snd tw3) (fst tw3) (Bsig TEMP1) xc\<close>], erule beval_cases)
      unfolding tw3_def tw2_def
      by (metis (mono_tags) Suc_eq_plus1 comp_apply eq_fst_iff lessI state_of_world_def worldline_upd2_before_dly worldline_upd2_def)
    also have "... = (if bval_of_wline tw SEL (fst tw) then bval_of_wline tw TEMP0 (fst tw) else bval_of_wline tw TEMP1 (fst tw))"
      using \<open>\<not> bval_of_wline tw SEL (fst tw)\<close>  by (simp add: state_of_world_def)
    also have "... = (if bval_of_wline tw3 SEL (fst tw3) then bval_of_wline tw3 TEMP0 (fst tw3) else bval_of_wline tw3 TEMP1 (fst tw3))"
      using \<open>\<not> bval_of_wline tw SEL (fst tw)\<close>  unfolding tw3_def tw2_def worldline_upd2_def worldline_upd_def 
      by auto
    also have "... = (if bval_of_wline tw4 SEL j then bval_of_wline tw4 TEMP0 j else bval_of_wline tw4 TEMP1 j)"
      using * by auto
    finally have temp1: "bval_of_wline tw4 OUT (i + 1) = (if bval_of_wline (j, snd tw4) SEL (get_time (j, snd tw4)) then bval_of_wline (j, snd tw4) TEMP0 (get_time (j, snd tw4))
          else bval_of_wline (j, snd tw4) TEMP1 (get_time (j, snd tw4)))"
      by auto

    have "wline_of tw4 TEMP0 (i + 1) = x"
      unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def 
      using \<open>get_time tw = get_time tw4\<close> \<open>get_time tw4 < j\<close> \<open>j \<le> i\<close> by auto    
    also have "bval_of ... \<longleftrightarrow> \<not> (bval_of_wline tw IN0 (fst tw) \<and> bval_of_wline tw IN1 (fst tw))"
      apply (rule beval_world_raw_cases[OF assms2], erule beval_cases)
      apply (metis beval_cases(1) comp_apply state_of_world_def val.sel(1))
      using \<open>type_of x = Bty\<close> by auto
    also have "... \<longleftrightarrow> \<not> (bval_of_wline tw3 IN0 (fst tw3) \<and> bval_of_wline tw3 IN1 (fst tw3))"
      unfolding tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
    also have "... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 j \<and> bval_of_wline tw4 IN1 j)"
      using * by auto
    finally have temp2: "bval_of_wline (j, snd tw4) TEMP0 (i + 1) =
         (\<not> (bval_of_wline (j, snd tw4) IN0 (get_time (j, snd tw4)) \<and> bval_of_wline (j, snd tw4) IN1 (get_time (j, snd tw4))))"
      by auto

    have "wline_of tw4 TEMP1 (i + 1) = xa"
      unfolding tw4_def tw3_def tw2_def worldline_upd2_def worldline_upd_def 
      using \<open>get_time tw = get_time tw4\<close> \<open>get_time tw4 < j\<close> \<open>j \<le> i\<close> by auto    
    also have "bval_of ... \<longleftrightarrow> \<not> (bval_of_wline tw2 IN0 (fst tw2) \<or> bval_of_wline tw2 IN1 (fst tw2))"
      apply (rule beval_world_raw_cases[OF assms3], erule beval_cases)
      apply (metis beval_cases(1) comp_apply state_of_world_def val.sel(1))
      using \<open>type_of xa = Bty\<close> by auto
    also have "... \<longleftrightarrow> \<not> (bval_of_wline tw3 IN0 (fst tw3) \<or> bval_of_wline tw3 IN1 (fst tw3))"
      unfolding tw3_def tw2_def worldline_upd2_def worldline_upd_def by auto
    also have "... \<longleftrightarrow> \<not> (bval_of_wline tw4 IN0 j \<or> bval_of_wline tw4 IN1 j)"
      using * by auto
    finally have temp3: "bval_of_wline (j, snd tw4) TEMP1 (i + 1) =
         (\<not> (bval_of_wline (j, snd tw4) IN0 (get_time (j, snd tw4)) \<or> bval_of_wline (j, snd tw4) IN1 (get_time (j, snd tw4))))"
      by auto
    show "bval_of_wline (j, snd tw4) OUT (i + 1) =
         (if bval_of_wline (j, snd tw4) SEL (get_time (j, snd tw4)) then bval_of_wline (j, snd tw4) TEMP0 (get_time (j, snd tw4))
          else bval_of_wline (j, snd tw4) TEMP1 (get_time (j, snd tw4))) \<and>
         bval_of_wline (j, snd tw4) TEMP0 (i + 1) =
         (\<not> (bval_of_wline (j, snd tw4) IN0 (get_time (j, snd tw4)) \<and> bval_of_wline (j, snd tw4) IN1 (get_time (j, snd tw4)))) \<and>
         bval_of_wline (j, snd tw4) TEMP1 (i + 1) = (\<not> (bval_of_wline (j, snd tw4) IN0 (get_time (j, snd tw4)) \<or> bval_of_wline (j, snd tw4) IN1 (get_time (j, snd tw4))))"
      using temp1 temp2 temp3 by auto
  qed
  thus "mux2_inv' (j, snd tw[ TEMP0, 1 :=\<^sub>2 x][ TEMP1, 1 :=\<^sub>2 xa][ OUT, 1 :=\<^sub>2 xc])"
    unfolding tw4_def tw3_def tw2_def by auto
qed

theorem mux2_seq_hoare_next_time'_wityping:
    "\<turnstile> [\<lambda>tw. wityping \<Gamma> (snd tw)] mux2_seq
     [\<lambda>tw. (\<forall>j \<in> {fst tw <.. next_time_world tw}. mux2_inv' (j, snd tw)) \<and> wityping \<Gamma> (snd tw)]"
  apply (rule Conj)
   apply (rule mux2_seq_hoare_next_time')
  apply (rule seq_stmt_preserve_wityping_hoare)
  using scalar_type_axioms unfolding scalar_type_def by auto

subsection \<open>Proving that the concurrent component\<close>

lemma mux2_inv_conc_hoare:
  "\<And>tw. mux2_inv tw \<and> mux2_inv' tw \<and> disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of tw) \<Longrightarrow> \<forall>k \<in> {fst tw <.. next_time_world tw}. mux2_inv (k, snd tw)"
proof (rule)
  fix k
  fix tw :: "nat \<times> (sig \<Rightarrow> val) \<times> (sig \<Rightarrow> nat \<Rightarrow> val)"
  assume "k \<in> {fst tw <.. next_time_world tw}"
  assume "mux2_inv tw \<and> mux2_inv' tw \<and> disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of tw)"
  hence "mux2_inv tw" and "mux2_inv' tw" and "disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of tw)"
    by auto
  hence *: "\<forall>i < fst tw. bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL i then bval_of_wline tw TEMP0 i else bval_of_wline tw TEMP1 i)" and 
        star2:   "\<forall>i < fst tw. bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<and> bval_of_wline tw IN1 i)" and 
        star3: "\<forall>i < fst tw. bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<or> bval_of_wline tw IN1 i)"
    unfolding mux2_inv_def by auto
  have **: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. wline_of tw s i = wline_of tw s (fst tw))"
    using unchanged_until_next_time_world by blast
  have ***: "(\<forall>i\<ge> fst tw. bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL (fst tw) then bval_of_wline tw TEMP0 (fst tw) else bval_of_wline tw TEMP1 (fst tw)))" and
       tstar2: "(\<forall>i\<ge> fst tw. bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 (fst tw) \<and> bval_of_wline tw IN1 (fst tw)))" and
       tstar3: "(\<forall>i\<ge> fst tw. bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 (fst tw) \<or> bval_of_wline tw IN1 (fst tw)))" 
    using \<open>mux2_inv' tw\<close> \<open>disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of tw)\<close> unfolding mux2_inv'_def by auto

  \<comment> \<open>obtain the value of A and B at time fst tw\<close>
  have  "wline_of tw SEL (fst tw) = wline_of tw SEL (fst tw - 1)" and "wline_of tw IN0 (fst tw) = wline_of tw IN0 (fst tw - 1)"
    and "wline_of tw IN1 (fst tw) = wline_of tw IN1 (fst tw - 1)" and "wline_of tw TEMP0 (fst tw) = wline_of tw TEMP0 (fst tw - 1)"
    and "wline_of tw TEMP1 (fst tw) = wline_of tw TEMP1 (fst tw - 1)"
    using \<open>disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of tw)\<close> unfolding event_of_alt_def
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)+
 { fix i
    assume "i < k"
    have "i < fst tw \<or> fst tw \<le> i"
      by auto
    moreover
    { assume "i < fst tw"
      hence "bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL i then bval_of_wline tw TEMP0 i else bval_of_wline tw TEMP1 i)"
        using * by auto 
      moreover have "bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<and> bval_of_wline tw IN1 i)"
        using star2 \<open>i < fst tw\<close> by auto
      moreover have "bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<or> bval_of_wline tw IN1 i)"
        using star3 \<open>i < fst tw\<close> by auto 
      ultimately have " (bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL i then bval_of_wline tw TEMP0 i else bval_of_wline tw TEMP1 i))
                      \<and> (bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<and> bval_of_wline tw IN1 i))
                      \<and> (bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<or> bval_of_wline tw IN1 i))"
        by auto }
    moreover
    { assume "fst tw \<le> i"
      hence "bval_of_wline tw OUT (i + 1) = bval_of_wline tw OUT (fst tw + 1)"
        using *** by auto
      also have "... = (if bval_of_wline tw SEL (fst tw) then bval_of_wline tw TEMP0 (fst tw) else bval_of_wline tw TEMP1 (fst tw))"
        using *** \<open>fst tw \<le> i\<close> by auto
      also have "... = (if bval_of_wline tw SEL i then bval_of_wline tw TEMP0 i else bval_of_wline tw TEMP1 i)"
        using ** \<open>i < k\<close> \<open>fst tw \<le> i\<close> less_imp_le_nat 
        by (smt \<open>k \<in> {get_time tw<..next_time_world tw}\<close> dual_order.strict_trans1
            greaterThanAtMost_iff)
      finally have temp1: "bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL i then bval_of_wline tw TEMP0 i else bval_of_wline tw TEMP1 i)"
        by auto 
      
      have "bval_of_wline tw TEMP0 (i + 1) = bval_of_wline tw TEMP0 (fst tw + 1)"
        using tstar2 \<open>fst tw \<le> i\<close> by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw IN0 (fst tw) \<and> bval_of_wline tw IN1 (fst tw))"
        using tstar2 \<open>fst tw \<le> i\<close> by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<and> bval_of_wline tw IN1 i)"
        using ** \<open>i < k\<close> \<open>fst tw \<le> i\<close> 
        by (smt \<open>k \<in> {get_time tw<..next_time_world tw}\<close> dual_order.strict_trans1 greaterThanAtMost_iff)
      finally have temp2: "bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<and> bval_of_wline tw IN1 i)"
        by auto

      have "bval_of_wline tw TEMP1 (i + 1) = bval_of_wline tw TEMP1 (fst tw + 1)"
        using tstar3 \<open>fst tw \<le> i\<close> by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw IN0 (fst tw) \<or> bval_of_wline tw IN1 (fst tw))"
        using tstar3 \<open>fst tw \<le> i\<close> by auto
      also have "... \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<or> bval_of_wline tw IN1 i)"
        using ** \<open>i < k\<close> \<open>fst tw \<le> i\<close> 
        by (smt \<open>k \<in> {get_time tw<..next_time_world tw}\<close> dual_order.strict_trans1 greaterThanAtMost_iff)
      finally have temp3: "bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<or> bval_of_wline tw IN1 i)"
        by auto
      have " (bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL i then bval_of_wline tw TEMP0 i else bval_of_wline tw TEMP1 i))
                      \<and> (bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<and> bval_of_wline tw IN1 i))
                      \<and> (bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<or> bval_of_wline tw IN1 i))"
        using temp1 temp2 temp3 by auto }
    ultimately have "(bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL i then bval_of_wline tw TEMP0 i else bval_of_wline tw TEMP1 i))
                      \<and> (bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<and> bval_of_wline tw IN1 i))
                      \<and> (bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<or> bval_of_wline tw IN1 i))"
      by auto }
  hence "\<And>i. i < k \<Longrightarrow> (bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL i then bval_of_wline tw TEMP0 i else bval_of_wline tw TEMP1 i))
                      \<and> (bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<and> bval_of_wline tw IN1 i))
                      \<and> (bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 i \<or> bval_of_wline tw IN1 i))"
    by auto
  thus " mux2_inv (k, snd tw)"
    unfolding mux2_inv_def by auto
qed

lemma mux2_inv'_conc_hoare:
  "\<And>tw. mux2_inv tw \<and> mux2_inv' tw \<and> disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of tw) \<Longrightarrow> \<forall>j \<in> {fst tw <.. next_time_world tw}. mux2_inv' (j, snd tw)"
proof (rule)
  fix tw :: "nat \<times> (sig \<Rightarrow> val) \<times> (sig \<Rightarrow> nat \<Rightarrow> val)"
  fix j
  assume "j \<in> {fst tw <.. next_time_world tw}"
  assume "mux2_inv tw \<and> mux2_inv' tw \<and> disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of tw)"
  hence "mux2_inv tw" and "mux2_inv' tw" and "disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of tw)"
    by auto
  hence 0: "    (\<forall>i\<ge>get_time tw.
        bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL (get_time tw) then bval_of_wline tw TEMP0 (get_time tw) else bval_of_wline tw TEMP1 (get_time tw)) \<and>
        bval_of_wline tw TEMP0 (i + 1) = (\<not> (bval_of_wline tw IN0 (get_time tw) \<and> bval_of_wline tw IN1 (get_time tw))) \<and>
        bval_of_wline tw TEMP1 (i + 1) = (\<not> (bval_of_wline tw IN0 (get_time tw) \<or> bval_of_wline tw IN1 (get_time tw))))"
    unfolding mux2_inv'_def by auto
  have 1: "\<forall>i\<ge>fst tw. i < next_time_world tw \<longrightarrow> (\<forall>s. wline_of tw s i = wline_of tw s (fst tw))"
    using unchanged_until_next_time_world by blast
  { assume "disjnt {IN0, IN1, SEL, TEMP0, TEMP1} (event_of (j, snd tw))"
    hence *: "wline_of tw IN0 j = wline_of tw IN0 (j - 1)" and **: "wline_of tw IN1 j = wline_of tw IN1 (j - 1)"
        and ***: "wline_of tw SEL j = wline_of tw SEL (j - 1)" and ****: "wline_of tw TEMP0 j = wline_of tw TEMP0 (j - 1)"
        and *****: "wline_of tw TEMP1 j = wline_of tw TEMP1 (j - 1)"
      unfolding event_of_alt_def
      by (smt comp_apply diff_is_0_eq' disjnt_insert1 fst_conv le_numeral_extra(1) mem_Collect_eq snd_conv)+
    have "fst tw < j"
      using \<open>j \<in> {get_time tw<..next_time_world tw}\<close> by auto
    { fix i
      assume "j \<le> i"
      hence "bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL (fst tw) then bval_of_wline tw TEMP0 (fst tw) else bval_of_wline tw TEMP1 (fst tw))"
        using 0 \<open>fst tw < j\<close> by auto
      moreover have "wline_of tw IN0 (fst tw) = wline_of tw IN0 (j - 1)" and "wline_of tw IN1 (fst tw) = wline_of tw IN1 (j - 1)"
        and "wline_of tw SEL (fst tw) = wline_of tw SEL (j - 1)" and "wline_of tw TEMP0 (fst tw) = wline_of tw TEMP0 (j - 1)" and 
            "wline_of tw TEMP1 (fst tw) = wline_of tw TEMP1 (j - 1)"
        using 1
        by (metis (no_types, lifting) \<open>j \<in> {get_time tw<..next_time_world tw}\<close> add_le_cancel_right
        diff_add diff_is_0_eq' discrete gr_implies_not_zero greaterThanAtMost_iff
        le_numeral_extra(4) neq0_conv)+
      ultimately have "bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL j then bval_of_wline tw TEMP0 j else bval_of_wline tw TEMP1 j)"
        using * ** *** **** ***** by auto 
      moreover have "bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 j \<and> bval_of_wline tw IN1 j)"
        using "*" "**" "0" \<open>get_time tw < j\<close> \<open>j \<le> i\<close> \<open>wline_of tw IN0 (get_time tw) = wline_of tw
        IN0 (j - 1)\<close> \<open>wline_of tw IN1 (get_time tw) = wline_of tw IN1 (j - 1)\<close> by auto
      moreover have "bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 j \<or> bval_of_wline tw IN1 j)"
        using "*" "**" "0" \<open>get_time tw < j\<close> \<open>j \<le> i\<close> \<open>wline_of tw IN0 (get_time tw) = wline_of tw IN0 (j - 1)\<close> \<open>wline_of tw IN1 (get_time tw) = wline_of tw IN1 (j - 1)\<close> by auto
      ultimately have "(bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL j then bval_of_wline tw TEMP0 j else bval_of_wline tw TEMP1 j)) \<and>
                       (bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 j \<and> bval_of_wline tw IN1 j)) \<and>
                       (bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 j \<or> bval_of_wline tw IN1 j))"
        by auto }
    hence "(\<forall>i\<ge>j. (bval_of_wline tw OUT (i + 1) = (if bval_of_wline tw SEL j then bval_of_wline tw TEMP0 j else bval_of_wline tw TEMP1 j)) \<and>
                       (bval_of_wline tw TEMP0 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 j \<and> bval_of_wline tw IN1 j)) \<and>
                       (bval_of_wline tw TEMP1 (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw IN0 j \<or> bval_of_wline tw IN1 j)))"
      by auto }
  thus "mux2_inv' (j, snd tw)"
    unfolding mux2_inv'_def by auto
qed

lemma mux2_conc_hoare_without:
  "\<turnstile> \<lbrace>\<lambda>tw. (mux2_inv tw \<and> mux2_inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace>
        mux2
     \<lbrace>\<lambda>tw. \<forall>j \<in> {fst tw <.. next_time_world tw}. mux2_inv  (j, snd tw)  \<and> mux2_inv' (j, snd tw)\<rbrace>"
  unfolding mux2_def
  apply (rule Single)
   apply (rule Conj_univ_qtfd)
    apply (rule Conseq2[rotated])
      apply (rule mux2_seq_hoare_next_time)
     apply simp
    apply simp
   apply(rule Conseq2[rotated])
     apply (rule mux2_seq_hoare_next_time')
    apply simp
   apply simp       
  using mux2_inv_conc_hoare mux2_inv'_conc_hoare by blast

lemma mux2_conc_hoare:
  "\<turnstile> \<lbrace>\<lambda>tw. (mux2_inv tw \<and> mux2_inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace>
        mux2
     \<lbrace>\<lambda>tw. \<forall>i\<in>{get_time tw<..next_time_world tw}. (mux2_inv (i, snd tw) \<and> mux2_inv' (i, snd tw)) \<and> wityping \<Gamma> (snd (i, snd tw))\<rbrace>"
  apply (rule Conj2_univ_qtfd)
   apply (rule weaken_post_conc_hoare[OF _ mux2_conc_hoare_without], blast)
  apply (rule strengthen_pre_conc_hoare[rotated])
   apply (rule weaken_post_conc_hoare[rotated])
  unfolding mux2_def apply (rule single_conc_stmt_preserve_wityping_hoare[where \<Gamma>="\<Gamma>"])
  using scalar_type_axioms unfolding scalar_type_def by auto

subsection \<open>Simulation preserves the invariant\<close>

lemma mux2_conc_sim:
    "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (mux2_inv tw \<and> mux2_inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace> 
            mux2 
        \<lbrace>\<lambda>tw. (mux2_inv tw \<and> mux2_inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace>"
  apply (rule While)
  apply (unfold snd_conv, rule mux2_conc_hoare[unfolded snd_conv])
  done

lemma mux2_conc_sim':
  shows "\<turnstile>\<^sub>s \<lbrace>\<lambda>tw. (mux2_inv tw \<and> wityping \<Gamma> (snd tw)) \<and> mux2_inv' tw\<rbrace> mux2 \<lbrace>mux2_inv'\<rbrace>"
  apply (rule Conseq_sim[where Q="\<lambda>tw. (mux2_inv tw \<and> mux2_inv' tw) \<and> wityping \<Gamma> (snd tw)" and
                               P="\<lambda>tw. (mux2_inv tw \<and> mux2_inv' tw) \<and> wityping \<Gamma> (snd tw)"])
  by (blast intro: mux2_conc_sim)+

subsection \<open>Initialisation preserves the invariant\<close>

lemma init_sat_mux2_inv:
  "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) mux2 (mux2_inv)"
  unfolding mux2_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule weaken_postcondition[OF mux2_seq_hoare_next_time0_wityping])
  done

lemma init_sat_mux_inv':
  "init_sim_hoare (\<lambda>tw. wityping \<Gamma> (snd tw)) mux2 mux2_inv'"
  unfolding mux2_def
  apply (rule AssignI)
  apply (rule SingleI)
  apply (rule Conseq2[rotated])
    apply (rule mux2_seq_hoare_next_time'_wityping)
   apply (simp add: next_time_world_at_least)
  by auto

lemma init_sat_nand_mux_inv_comb:
   "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) mux2 (\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw)"
  apply (rule ConjI_sim)
   apply (rule init_sat_mux2_inv)
  apply (rule ConseqI_sim[where P="\<lambda>tw. wityping \<Gamma> (snd tw)"])
  apply (simp, rule init_sat_mux_inv', simp)
  done

lemma init_sat_nand_mux_inv_comb_wityping:
  shows "init_sim_hoare (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) mux2 (\<lambda>tw. (mux2_inv tw \<and> mux2_inv' tw) \<and> wityping \<Gamma> (snd tw))"
  apply (rule ConjI_sim)
   apply (rule ConseqI_sim[rotated])
     apply (rule init_sat_nand_mux_inv_comb)
    apply simp
   apply simp
  apply (rule strengthen_precondition_init_sim_hoare[rotated])
  unfolding mux2_def apply (rule single_conc_stmt_preserve_wityping_init_sim_hoare)
  using scalar_type_axioms unfolding scalar_type_def by auto

lemma mux2_correctness:
  assumes "sim_fin w (i + 1) mux2 tw'" and "wityping \<Gamma> w"
  assumes "conc_wt \<Gamma> mux2"
  shows "
     bval_of_wline tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then bval_of_wline tw' TEMP0 i else bval_of_wline tw' TEMP1 i) \<and>
     bval_of_wline tw' TEMP0 (i + 1) = (\<not> (bval_of_wline tw' IN0 i \<and> bval_of_wline tw' IN1 i)) \<and>
     bval_of_wline tw' TEMP1 (i + 1) = (\<not> (bval_of_wline tw' IN0 i \<or> bval_of_wline tw' IN1 i))"
proof -
  obtain tw where "init_sim (0, w) mux2 tw" and  "tw, i + 1, mux2 \<Rightarrow>\<^sub>S tw'"
    using premises_sim_fin_obt[OF assms(1)] by auto
  hence "i + 1 = fst tw'"
    using world_maxtime_lt_fst_tres  by blast
  have "conc_stmt_wf mux2"
    unfolding conc_stmt_wf_def mux2_def by auto
  moreover have "nonneg_delay_conc mux2"
    unfolding mux2_def by auto
  ultimately have "init_sim_valid (\<lambda>tw. fst tw = 0 \<and> wityping \<Gamma> (snd tw)) mux2 (\<lambda>tw. mux2_inv tw \<and> mux2_inv' tw \<and> wityping \<Gamma> (snd tw))"
    using init_sim_hoare_soundness[OF init_sat_nand_mux_inv_comb_wityping]  by auto
  hence "mux2_inv tw \<and> mux2_inv' tw \<and> wityping \<Gamma> (snd tw)"
    using \<open>init_sim (0, w) mux2 tw\<close> fst_conv assms(2) unfolding init_sim_valid_def
    by (metis (full_types) snd_conv)
  hence "mux2_inv tw" and "mux2_inv' tw" and "wityping \<Gamma> (snd tw)"
    by auto
  moreover have "\<Turnstile>\<^sub>s \<lbrace>\<lambda>tw. (mux2_inv tw \<and> mux2_inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace> mux2 \<lbrace>\<lambda>tw. (mux2_inv tw \<and> mux2_inv' tw) \<and> wityping \<Gamma> (snd tw)\<rbrace>"
    using conc_sim_soundness[OF mux2_conc_sim] \<open>conc_stmt_wf mux2\<close> \<open>nonneg_delay_conc mux2\<close>
    by simp
  ultimately have "mux2_inv tw'"
    using \<open>tw, i + 1, mux2 \<Rightarrow>\<^sub>S tw'\<close> unfolding sim_hoare_valid_def by blast
  hence "\<forall>i<get_time tw'.
     bval_of_wline tw' OUT (i + 1) = (if bval_of_wline tw' SEL i then bval_of_wline tw' TEMP0 i else bval_of_wline tw' TEMP1 i) \<and>
     bval_of_wline tw' TEMP0 (i + 1) = (\<not> (bval_of_wline tw' IN0 i \<and> bval_of_wline tw' IN1 i)) \<and>
     bval_of_wline tw' TEMP1 (i + 1) = (\<not> (bval_of_wline tw' IN0 i \<or> bval_of_wline tw' IN1 i))"
    unfolding mux2_inv_def by auto
  with \<open>i + 1 = fst tw'\<close> show ?thesis
    by (metis less_add_one)
qed

end