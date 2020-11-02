(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory NAND_Hoare_Inert_Typed
  imports VHDL_Hoare_Typed NAND_Femto
begin

subsection \<open>Proving @{term "nand3"}: NAND with inert delay \<close>

abbreviation "bval_of_wline tw sig n \<equiv> bval_of (wline_of tw sig n)"
abbreviation "lof_wline tw sig n \<equiv> lval_of (wline_of tw sig n)"

locale scalar_type_nand3 =
  fixes \<Gamma> :: "sig tyenv"
  assumes "\<Gamma> A = Bty" and "\<Gamma> B = Bty" and "\<Gamma> C = Bty"
begin

text \<open>Invariant for NAND: at all times @{term "i"}, the signal @{term "C :: sig"} at @{term "i"} 
should be the NAND value of @{term "A :: sig"} and @{term "B :: sig"} at time @{term "i - 1"}.\<close>

definition nand_inv :: "sig assn2" where
  "nand_inv \<equiv> (\<lambda>tw. bval_of_wline tw C (fst tw) \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw - 1) \<and> bval_of_wline tw B (fst tw - 1)))"

definition nand_inv2 :: "sig assn2" where
  "nand_inv2 \<equiv> (\<lambda>tw. disjnt {A, B} (event_of tw) \<longrightarrow> (\<forall>i > fst tw. bval_of_wline tw C i \<longleftrightarrow> bval_of_wline tw C (fst tw)))"

lemma nand_inv_next_time:
  fixes tw
  defines "v \<equiv> eval_world_raw2 tw (Bnand (Bsig A) (Bsig B))"
  defines "tw' \<equiv> tw\<lbrakk>C, 1 :=\<^sub>2 v\<rbrakk>"
  assumes "wityping \<Gamma> (snd tw)"
  shows   "nand_inv (fst tw' + 1, snd tw')"
proof -
  have bexpA: "bexp_wt \<Gamma> (Bsig A) Bty" and bexpB: "bexp_wt \<Gamma> (Bsig B) Bty" 
    using scalar_type_nand3_axioms unfolding scalar_type_nand3_def  by (metis bexp_wt.intros(3))+
  have "type_of v = Bty"
    using assms(3) bexpA bexpB bexp_wt.intros(9) type_of_eval_world_raw2 v_def by blast
  hence "bval_of_wline tw' C (fst tw + 1) \<longleftrightarrow> bval_of v"
    unfolding tw'_def
  proof (induction v)
    case (Bv x)
    have "snd (snd tw) C (get_time tw) \<noteq> Bv x \<and> snd (snd tw) C (get_time tw + 1) = Bv x \<Longrightarrow> 
          (GREATEST n. n \<le> get_time tw + 1 \<and> snd (snd tw) C (n - 1) \<noteq> Bv x \<and> snd (snd tw) C n = Bv x) \<le> fst tw + 1"
      by (metis (mono_tags, lifting) GreatestI_ex_nat Suc_eq_plus1 add_diff_cancel_left' order_refl plus_1_eq_Suc)
    then show ?case 
      unfolding worldline_inert_upd2_def VHDL_Hoare.worldline_inert_upd2.simps worldline_inert_upd_def
      comp_def snd_conv by auto
  next
    case (Lv sign bs)
    then show ?case
      by auto
  qed
  also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
    using eval_world_raw_bv[OF bexpA `wityping \<Gamma> (snd tw)`]  eval_world_raw_bv[OF bexpB `wityping \<Gamma> (snd tw)`] 
    unfolding v_def by (auto split:val.split)(metis val.distinct(1))+ 
  finally show ?thesis
    unfolding nand_inv_def tw'_def worldline_inert_upd2_def worldline_inert_upd_def 
    by (metis (no_types, hide_lams) One_nat_def add_implies_diff comp_def fst_conv not_less_less_Suc_eq not_less_zero order_refl snd_conv snd_worldline_inert_upd2 worldline_inert_upd2_def)
qed

lemma nand_inv2_next_time:
  fixes tw v
  defines "tw' \<equiv> tw\<lbrakk>C, 1 :=\<^sub>2 v\<rbrakk>"
  shows   "nand_inv2 (fst tw' + 1, snd tw')"
proof -
  { assume "disjnt {A, B} (event_of (fst tw' + 1, snd tw'))"
    have "\<And>j. fst tw + 1 < j \<Longrightarrow> bval_of_wline tw' C j \<longleftrightarrow> bval_of_wline tw' C (fst tw + 1)"
      unfolding tw'_def 
    proof (induction v)
      case (Bv x)
      then show ?case 
      proof (cases "snd (snd tw) C (get_time tw) = Bv x \<or> snd (snd tw) C (get_time tw + 1) \<noteq> Bv x ")
        case True
        then show ?thesis 
          using Bv
          unfolding worldline_inert_upd2_def VHDL_Hoare.worldline_inert_upd2.simps worldline_inert_upd_def
          comp_def snd_conv by auto
      next
        case False
        hence "snd (snd tw) C (get_time tw) \<noteq> Bv x \<and> snd (snd tw) C (get_time tw + 1) = Bv x"
          by auto
        hence "(GREATEST n. n \<le> get_time tw + 1 \<and> snd (snd tw) C (n - 1) \<noteq> Bv x \<and> snd (snd tw) C n = Bv x) = fst tw + 1"
          using GreatestI_nat[where k="fst tw + 1"] 
          by (metis (mono_tags, lifting) Greatest_equality Suc_eq_plus1 diff_Suc_1 le_eq_less_or_eq)
        then show ?thesis
          using Bv False
          unfolding worldline_inert_upd2_def VHDL_Hoare.worldline_inert_upd2.simps worldline_inert_upd_def
          comp_def snd_conv by auto
      qed
    next
      case (Lv sign bs)
      let ?w' = "\<lambda>b. snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)]"
      let ?time = "LEAST n. get_time tw < n \<and> n \<le> get_time tw + 1 \<and> (\<exists>b\<in>set [0..<length bs]. ?w' b C (n - 1) \<noteq> ?w' b C n)"
      have *: " bs = (map (\<lambda>b. bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (fst tw + 1))) [0..<length bs])"
      proof (rule nth_equalityI)
        show "length bs = length (map (\<lambda>b. bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (fst tw + 1))) [0..<length bs])"
          by auto
      next
        fix b
        assume "b < length bs"
        hence "map (\<lambda>b. bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (fst tw + 1))) [0..<length bs] ! b = 
              bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (fst tw + 1))"
          by auto
        have "((snd (snd tw))(C := to_bit b \<circ> snd (snd tw) C)) C (get_time tw)  \<noteq> Bv (bs ! b) \<and>
             ((snd (snd tw))(C := to_bit b \<circ> snd (snd tw) C)) C (get_time tw + 1) = Bv (bs ! b) \<Longrightarrow> 
            ( GREATEST n.
                  n \<le> get_time tw + 1 \<and>
                  ((snd (snd tw))(C := to_bit b \<circ> snd (snd tw) C)) C (n - 1) \<noteq> Bv (bs ! b) \<and>
                  ((snd (snd tw))(C := to_bit b \<circ> snd (snd tw) C)) C n = Bv (bs ! b)) = fst tw + 1"
          by (metis (mono_tags, lifting) Greatest_equality add_diff_cancel_right' le_eq_less_or_eq)
        hence "bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (fst tw + 1)) = (bs ! b)"
          unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv by auto
        thus " bs ! b =
        map (\<lambda>b. bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (fst tw + 1))) [0..<length bs] !
        b "
          using \<open>map (\<lambda>b. bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (fst tw + 1))) [0..<length bs] ! b = bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (fst tw + 1))\<close> 
          by blast
      qed
      have **: " bs = (map (\<lambda>b. bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (j))) [0..<length bs])"
      proof (rule nth_equalityI)
        show "length bs = length (map (\<lambda>b. bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (j))) [0..<length bs])"
          by auto
      next
        fix b
        assume "b < length bs"
        hence "map (\<lambda>b. bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (j))) [0..<length bs] ! b = 
              bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (j))"
          by auto
        have "((snd (snd tw))(C := to_bit b \<circ> snd (snd tw) C)) C (get_time tw)  \<noteq> Bv (bs ! b) \<and>
             ((snd (snd tw))(C := to_bit b \<circ> snd (snd tw) C)) C (get_time tw + 1) = Bv (bs ! b) \<Longrightarrow> 
            ( GREATEST n.
                  n \<le> get_time tw + 1 \<and>
                  ((snd (snd tw))(C := to_bit b \<circ> snd (snd tw) C)) C (n - 1) \<noteq> Bv (bs ! b) \<and>
                  ((snd (snd tw))(C := to_bit b \<circ> snd (snd tw) C)) C n = Bv (bs ! b)) = fst tw + 1"
          by (metis (mono_tags, lifting) Greatest_equality add_diff_cancel_right' le_eq_less_or_eq)
        hence "bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (j)) = (bs ! b)"
          unfolding to_worldline_init_bit_def worldline_inert_upd_def snd_conv 
          using Lv by auto
        thus " bs ! b =
        map (\<lambda>b. bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (j))) [0..<length bs] !
        b "
          using \<open>map (\<lambda>b. bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (j))) [0..<length bs] ! b = bval_of (snd to_worldline_init_bit (snd tw) C b[C, get_time tw, 1 := Bv (bs ! b)] C (j))\<close> 
          by blast
      qed
      show ?case 
      proof (cases "\<exists>n>get_time tw. n \<le> get_time tw + 1 \<and> (\<exists>b\<in>set [0..<length bs]. ?w' b C (n - 1) \<noteq> ?w' b C n)")
        case True
        hence "?time = fst tw + 1"
          by (metis (mono_tags, lifting) LeastI_ex antisym_conv1 discrete leD)
        hence "wline_of tw\<lbrakk> C, 1 :=\<^sub>2 Lv sign bs\<rbrakk> C (get_time tw + 1) = Lv sign bs"
          using *[THEN sym] True unfolding worldline_inert_upd2_def VHDL_Hoare.worldline_inert_upd2.simps comp_def snd_conv fun_upd_def
          by auto
        moreover have " wline_of tw\<lbrakk> C, 1 :=\<^sub>2 Lv sign bs\<rbrakk> C j =  Lv sign bs"
          using Lv True \<open>?time = fst tw + 1\<close> **
          unfolding worldline_inert_upd2_def comp_def snd_conv VHDL_Hoare.worldline_inert_upd2.simps
            fun_upd_def by auto
        ultimately show ?thesis
          by auto
      next
        case False
        then show ?thesis
          using Lv * **
          unfolding worldline_inert_upd2_def comp_def snd_conv VHDL_Hoare.worldline_inert_upd2.simps
          fun_upd_def by auto 
      qed
    qed }
    thus "nand_inv2 (fst tw' + 1, snd tw')"
      unfolding nand_inv2_def by (simp add: tw'_def worldline_inert_upd2_def)
qed
 
lemma pre_nand_conc_hoare':
  "\<And>tw. nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> nand_inv (fst tw + 1, snd tw)"
proof -
  fix tw
  assume "nand_inv tw \<and> nand_inv2 tw \<and> disjnt {A, B} (event_of tw)"
  hence "nand_inv tw" and "nand_inv2 tw" and "disjnt {A, B} (event_of tw)"
    by auto
  have "bval_of_wline tw C (fst tw + 1) \<longleftrightarrow> bval_of_wline tw C (fst tw)"
    using `nand_inv2 tw` `disjnt {A, B} (event_of tw)` unfolding nand_inv2_def 
    by (simp add: next_time_world_at_least) 
  also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw - 1) \<and> bval_of_wline tw B (fst tw - 1))"
    using `nand_inv tw` unfolding nand_inv_def by auto
  also have "... \<longleftrightarrow> \<not> (bval_of_wline tw A (fst tw) \<and> bval_of_wline tw B (fst tw))"
    using `disjnt {A, B} (event_of tw)`  unfolding event_of_alt_def 
    by (smt diff_0_eq_0 disjnt_insert1 mem_Collect_eq)
  finally show "nand_inv (fst tw + 1, snd tw)"
    unfolding nand_inv_def by auto
qed

lemma nand_conc_hoare2:
  "\<And>tw. nand_inv2 tw \<and> disjnt {A, B} (event_of tw) \<Longrightarrow> nand_inv2 (fst tw + 1, snd tw)"
  unfolding nand_inv2_def by auto

lemma conc_stmt_wf_nand3:
  "conc_stmt_wf nand"
  unfolding nand_def conc_stmt_wf_def by auto  

lemma nonneg_delay_conc_nand3:
  "nonneg_delay_conc nand"
  unfolding nand_def by auto

lemma nonneg_delay_conc_nand3':
  "nonneg_delay_conc ( process {A, B} : Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1)"
  using nonneg_delay_conc_nand3  by auto

lemma conc_wt_nand3:
  "conc_wt \<Gamma> nand"
  unfolding nand_def  by (metis bexp_wt.intros(3) bexp_wt.intros(9) conc_wt.intros(1) scalar_type_nand3_axioms
  scalar_type_nand3_def seq_wt.intros(5))

lemma conc_wt_nand3':
  "conc_wt \<Gamma> ( process {A, B} : Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1)"
  using conc_wt_nand3 unfolding nand_def by auto

lemma nand_conc_sim2':
  "\<Gamma> \<turnstile>\<^sub>s \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace> nand \<lbrace>\<lambda>tw. nand_inv tw \<and> nand_inv2 tw\<rbrace>"
  apply (rule While_Suc)
  apply (rule Conseq'[where P="wp3_conc \<Gamma> nand (\<lambda>tw. nand_inv  (fst tw + 1, snd tw) \<and> 
                                                      nand_inv2 (fst tw + 1, snd tw))", rotated])
  apply (rule wp3_conc_is_pre, rule conc_stmt_wf_nand3, rule nonneg_delay_conc_nand3, rule conc_wt_nand3, simp)
  unfolding nand_def  wp3_conc_single'[OF conc_wt_nand3' nonneg_delay_conc_nand3'] wp3_fun.simps
  using nand_conc_hoare2 nand_inv2_next_time nand_inv_next_time pre_nand_conc_hoare' by presburger

text \<open>Initialisation preserves the invariant\<close>

lemma seq_wt_nand3':
  "seq_wt \<Gamma> (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1)"
  using conc_wt_nand3' by auto

lemma nonneg_delay_nand3:
  " nonneg_delay (Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1)"
  using nonneg_delay_conc_nand3' by auto

lemma init_sat_nand_inv_comb:
  "init_sim2_hoare_wt \<Gamma> (\<lambda>tw. fst tw = 0) nand (\<lambda>tw. nand_inv tw \<and> nand_inv2 tw)"
  unfolding nand_def
  apply (rule AssignI_suc, rule SingleI)
  apply (rule Conseq3[where Q="\<lambda>tw. nand_inv (fst tw + 1, snd tw) \<and> nand_inv2 (fst tw + 1, snd tw)", rotated])
  apply (rule wp3_fun_is_pre[OF seq_wt_nand3' nonneg_delay_nand3], simp)
  unfolding wp3_fun.simps using nand_inv_next_time nand_inv2_next_time by blast

lemma nand_correctness:
  assumes "sim_fin2 w (i + 1) nand tw'" and "wityping \<Gamma> w"
  shows "bval_of_wline tw' C (i + 1) \<longleftrightarrow> \<not> (bval_of_wline tw' A i \<and> bval_of_wline tw' B i)"
  using grand_correctness[OF assms conc_stmt_wf_nand3 conc_wt_nand3 nonneg_delay_conc_nand3 nand_conc_sim2' init_sat_nand_inv_comb]
  unfolding nand_inv_def by (metis (no_types, lifting) add_diff_cancel_right' assms(1)
  sim_fin2.cases world_maxtime_lt_fst_tres)

end