(*
 * Copyright 2018-2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory NAND_Femto
imports
  Femto_VHDL Femto_VHDL_Executable
begin

lemma trans_post_empty_trans_upd:
  "trans_post sig v def empty_trans t dly =
    (if v \<noteq> def then Poly_Mapping.update (t + dly) [sig \<mapsto> v] empty_trans else empty_trans)"
proof transfer'
  fix sig :: "'a"
  fix v def t dly
  have "post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def \<or> \<not> post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def"
    by auto
  moreover
  { assume nec: "post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def"
    hence "v \<noteq> def"
      by (metis post_necessary_raw_correctness zero_fun_def zero_option_def)
    hence "(if post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def then post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_raw sig (\<lambda>k. 0) (t + dly)) =
      (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))"
      using nec unfolding trans_post_raw_def post_raw_def preempt_raw_def zero_upd zero_map fun_upd_def
      by auto }
  moreover
  { assume not_nec: "\<not> post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def"
    hence "v = def"
      by (meson signal_of_def zero_fun_def)
    hence "(if post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def then post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_raw sig (\<lambda>k. 0) (t + dly)) =
      (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))"
      using not_nec by (auto simp add: preempt_raw_def zero_fun_def zero_option_def) }
  ultimately have " (if post_necessary_raw (dly-1) (\<lambda>k. 0) t sig v def then post_raw sig v (\<lambda>k. 0) (t + dly) else preempt_raw sig (\<lambda>k. 0) (t + dly)) =
       (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0))" by auto
  thus "trans_post_raw sig v def (\<lambda>k. 0) t dly = (if v \<noteq> def then (\<lambda>k. 0)(t + dly := [sig \<mapsto> v]) else (\<lambda>k. 0)) "
    unfolding trans_post_raw_def by auto
qed

lemma get_trans_trans_upd_cancel:
  "lookup (Poly_Mapping.update n [sig \<mapsto> v] \<tau>) n = [sig \<mapsto> v]"
  by transfer auto

definition nand :: "sig conc_stmt" where
  "nand = process {A, B} : Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1"

code_thms simulate_fin

code_thms functional_simulate_fin

values  "{lookup (get_beh beh) 1 C | beh. simulate_fin_ind 10 0 (\<lambda>x. Bv False) {A} 0 (\<lambda>x. Bv False) nand empty_trans beh}"

value " ((lookup o get_beh) (functional_simulate_fin 10 0 (\<lambda>x. Bv False) {A} 0 (\<lambda>x. Bv False) nand 0)) 1 C"

theorem
  "(lookup o get_beh) (functional_simulate_fin 10 0 (\<lambda>x. Bv False) {A} 0 (\<lambda>x. Bv False) nand empty_trans) 1 C = Some (Bv True)"
  by eval

value "(lookup o get_beh) (functional_simulate 10 (\<lambda>x. Bv False) nand empty_trans) 1 C"

value "signal_of2 (Bv False) (get_beh (functional_simulate 10 (\<lambda>x. Bv False) nand empty_trans)) C 100"

value [code] "to_signal (Bv False) (to_transaction_sig (empty_trans :: nat \<Rightarrow>\<^sub>0 sig \<rightharpoonup> val)) A 123456"

hide_const Femto_VHDL.next_time Femto_VHDL.next_state Femto_VHDL.next_event Femto_VHDL.add_to_beh
           Femto_VHDL.quiet Femto_VHDL.inf_time Femto_VHDL.init' Femto_VHDL.to_signal
hide_fact  Femto_VHDL.next_time_def Femto_VHDL.next_state_def Femto_VHDL.next_event_def
           Femto_VHDL.add_to_beh_def Femto_VHDL.quiet_def Femto_VHDL.to_signal_def Femto_VHDL.inf_time_def
           Femto_VHDL.init'_def

theorem
  assumes "10, 0, (\<lambda>x. Bv False), {A}, 0, (\<lambda>x. Bv False) \<turnstile> <nand, 0> \<leadsto> beh"
  shows "(get_beh beh) 1 C = Some (Bv True)"
  using assms
proof (cases)
  case (1 \<tau>')
  have temp0: "trans_post_raw C (Bv True) (Bv False) (override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}) 0 (Suc 0) =
        0(Suc 0 := [C \<mapsto> Bv True])"
  proof -
    let ?\<tau> = "override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}"
    have "signal_of (Bv False) ?\<tau> C 0 = (Bv False)"
      by (metis (no_types, lifting) greaterThanAtMost_iff less_irrefl_nat override_on_def
      signal_of_zero zero_fun_def)
    hence "post_necessary_raw (Suc 0 - 1) (override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}) 0 C (Bv True) (Bv False)"
      by auto
    hence "trans_post_raw C (Bv True) (Bv False) ?\<tau> 0 (Suc 0) = post_raw C (Bv True) ?\<tau> (Suc 0)"
      unfolding trans_post_raw_def by auto
    also have "... = 0(Suc 0 := [C \<mapsto> Bv True])"
      unfolding post_raw_def by (auto simp add: zero_fun_def zero_option_def)
    finally show ?thesis
      by auto
  qed
  have "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 , 0> \<longrightarrow>\<^sub>s (0(1 := [C \<mapsto> Bv True]))"
  proof (intro b_seq_exec.intros)
    have "0 , \<lambda>x. Bv False , {A} , 0, \<lambda>x. Bv False  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv (\<not> (False \<and> False))"
      by (intro beval_raw.intros)
    thus " 0 , \<lambda>x. Bv False , {A} , 0, \<lambda>x. Bv False  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv True"
      by auto
  next
    have "signal_of (Bv False) 0 C 1 \<noteq> Bv True"
      by (metis signal_of_empty val.inject(1))
    hence "purge_raw 0 0 1 C (Bv False) (Bv True) = override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}"
      unfolding purge_raw_def Let_def by auto
    thus "inr_post_raw C (Bv True) (Bv False) 0 0 1 = 0(1 := [C \<mapsto> Bv True])"
      using temp0 unfolding inr_post_raw_def by auto
  qed
  hence "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <get_seq nand , 0> \<longrightarrow>\<^sub>s (0(1 := [C \<mapsto> Bv True]))"
    unfolding nand_def by auto
  hence base: "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <nand , 0> \<longrightarrow>\<^sub>c (0(1 := [C \<mapsto> Bv True]))"
    unfolding nand_def
    by (simp add: b_conc_exec.intros(2))
  hence \<tau>'_def: "\<tau>' = (0(1:=[C \<mapsto> Bv True]))"
    using 1  by (simp add: b_conc_exec_deterministic)
  have nt: "next_time 0 \<tau>' = 1"
  proof -
    have "(0(1:=[C \<mapsto> Bv True])) \<noteq> 0"
      by (metis fun_upd_same option.distinct(1) zero_fun_def zero_option_def)
    moreover have "(LEAST n. dom (\<tau>' n) \<noteq> {}) = 1"
      unfolding \<tau>'_def
    proof (rule Least_equality)
      show "dom ((0(1 := [C \<mapsto> Bv True])) 1) \<noteq> {}"
        by auto
    next
      { fix y :: nat
        assume "\<not> 1 \<le> y"
        hence "y = 0"
          by auto
        hence "dom (((\<lambda>_. 0)(1 := [C \<mapsto> Bv True])) y) = {}"
          by (auto simp add: zero_map)
        hence "\<not> dom (((\<lambda>_. 0)(1 := [C \<mapsto> Bv True])) y) \<noteq> {}"
          by auto
        hence "\<not> dom ((0(1 := [C \<mapsto> Bv True])) y) \<noteq> {}"
          by (simp add: zero_fun_def) }
      thus "\<And>y::nat.  dom ((0(1 := [C \<mapsto> Bv True])) y) \<noteq> {} \<Longrightarrow> 1 \<le> y"
        by fastforce
    qed
    ultimately show ?thesis
      unfolding \<tau>'_def next_time_def by auto
  qed
  have ns: "next_state 0 \<tau>' (\<lambda>x. Bv False) = (\<lambda>x. Bv False) (C := Bv True)" (is "?lhs = ?rhs")
    unfolding next_state_def Let_def nt
    by (simp add: \<tau>'_def override_on_insert')
  have ne: "next_event 0 \<tau>' (\<lambda>x. Bv False) = {C}"
  proof -
    {
      fix sig
      assume "sig \<in> dom (\<tau>' 1)"
      hence "sig = C"
        unfolding \<tau>'_def by transfer' auto
      hence "(the \<circ> \<tau>' 1) sig \<noteq> Bv False"
        unfolding \<tau>'_def by transfer' auto
      with `sig = C` have "sig = C" and "(the \<circ> \<tau>' 1) sig \<noteq> Bv False"
        by auto }
    hence "\<And>sig. sig \<in> dom (\<tau>' 1) \<Longrightarrow> (the o \<tau>' 1) sig \<noteq> Bv False \<Longrightarrow> sig = C"
      by auto
    hence "next_event 0 \<tau>' (\<lambda>x. Bv False) \<subseteq> {C}"
      unfolding next_event_def Let_def nt by auto
    have "C \<in> dom (\<tau>' 1)"
      unfolding \<tau>'_def by (simp add: get_trans_trans_upd_cancel)
    moreover have "(the \<circ> \<tau>' 1) C \<noteq> Bv False"
      unfolding \<tau>'_def  using \<open>\<And>sig. sig \<in> dom (\<tau>' 1) \<Longrightarrow> (the \<circ> \<tau>' 1) sig \<noteq> Bv False\<close>
      \<tau>'_def calculation by blast
    ultimately have "{C} \<subseteq> next_event 0 \<tau>' (\<lambda>x. Bv False)"
      unfolding next_event_def Let_def nt by auto
    with `next_event 0 \<tau>' (\<lambda>x. Bv False) \<subseteq> {C}` show ?thesis
      by auto
  qed
  have nb: "add_to_beh (\<lambda>x. Bv False) 0 0 1 =
       0(0 := (Some o (\<lambda>x. Bv False)))" (is "_ = ?beh'")
    unfolding add_to_beh_def by auto
  define beh2 :: "(nat \<Rightarrow> sig \<Rightarrow> val option)" where "beh2 = ?beh'"
  hence snd_cyc: "10, 1, (\<lambda>x. Bv False) (C := Bv True), {C} , beh2, (\<lambda>x. Bv False) \<turnstile> <nand , (\<tau>'(1:=0))> \<leadsto> beh"
    using 1 nt ns ne nb by metis
  thus "get_beh beh 1 C = Some (Bv True)"
  proof (cases)
    case (1 \<tau>'')
    have t''_def: "\<tau>'' = 0"
      unfolding nand_def
      using 1(3) unfolding nand_def by (auto simp add: \<tau>'_def zero_fun_def)
    have nt2: "next_time 1 0 = 2"
      by auto
    moreover have "next_state 1 \<tau>'' ((\<lambda>x. Bv False)(C := Bv True)) = (\<lambda>x. Bv False) (C := Bv True)"
      unfolding next_state_def Let_def t''_def nt2 zero_fun_def zero_option_def
      by auto
    moreover have "next_event 1 \<tau>'' ((\<lambda>x. Bv False)(C := Bv True)) = {}"
      unfolding next_event_def Let_def t''_def nt2
      by (auto simp add: zero_fun_def zero_option_def)
    moreover have "add_to_beh ((\<lambda>x. Bv False)(C := Bv True)) beh2 1 (next_time 1 \<tau>'') =
                   beh2(1 := (Some o (\<lambda>x. Bv False)(C := Bv True)))"
      unfolding add_to_beh_def t''_def nt2 by simp
    moreover have "(0(1 := [C \<mapsto> Bv True]))(1:=0) = 0"
      unfolding zero_fun_def zero_option_def by auto
    ultimately have "(10, 2, (\<lambda>x. Bv False) (C := Bv True), {}, beh2(1 :=(Some o (\<lambda>x. Bv False)(C := Bv True))), (\<lambda>x. Bv False) \<turnstile> <nand, (\<tau>''(2:=0))> \<leadsto> beh)"
      using 1(5) using t''_def by metis
    then show ?thesis
    proof (cases)
      case (1 \<tau>')
      then show ?thesis unfolding quiet_def t''_def zero_fun_def zero_option_def
        by (simp add: fun_upd_idem)
    next
      case 2
      then show ?thesis unfolding quiet_def t''_def
        by (transfer, auto)
    qed auto
  next
    case 2
    then show ?thesis by (auto simp add:quiet_def)
  qed auto
next
  case (2 \<tau>')
  have temp0: "trans_post_raw C (Bv True) (Bv False) (override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}) 0 (Suc 0) =
        0(Suc 0 := [C \<mapsto> Bv True])"
  proof -
    let ?\<tau> = "override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}"
    have "signal_of (Bv False) ?\<tau> C 0 = (Bv False)"
      by (metis (no_types, lifting) greaterThanAtMost_iff less_irrefl_nat override_on_def
      signal_of_zero zero_fun_def)
    hence "post_necessary_raw (Suc 0 - 1) (override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}) 0 C (Bv True) (Bv False)"
      by auto
    hence "trans_post_raw C (Bv True) (Bv False) ?\<tau> 0 (Suc 0) = post_raw C (Bv True) ?\<tau> (Suc 0)"
      unfolding trans_post_raw_def by auto
    also have "... = 0(Suc 0 := [C \<mapsto> Bv True])"
      unfolding post_raw_def by (auto simp add: zero_fun_def zero_option_def)
    finally show ?thesis
      by auto
  qed
  have "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1 , 0> \<longrightarrow>\<^sub>s (0(1 := [C \<mapsto> Bv True]))"
  proof (intro b_seq_exec.intros)
    have "0 , \<lambda>x. Bv False , {A} , 0, \<lambda>x. Bv False  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv (\<not> (False \<and> False))"
      by (intro beval_raw.intros)
    thus " 0 , \<lambda>x. Bv False , {A} , 0, \<lambda>x. Bv False  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv True"
      by auto
  next
    have "signal_of (Bv False) 0 C 1 \<noteq> Bv True"
      by (metis signal_of_empty val.inject(1))
    hence "purge_raw 0 0 1 C (Bv False) (Bv True) = override_on 0 (\<lambda>n. (0 n)(C := None)) {0<..Suc 0}"
      unfolding purge_raw_def Let_def by auto
    thus "inr_post_raw C (Bv True) (Bv False) 0 0 1 = 0(1 := [C \<mapsto> Bv True])"
      using temp0 unfolding inr_post_raw_def by auto
  qed
  hence "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <get_seq nand , 0> \<longrightarrow>\<^sub>s (0(1 := [C \<mapsto> Bv True]))"
    unfolding nand_def by auto
  hence base: "0 , (\<lambda>x. Bv False) , {A} , 0, (\<lambda>x. Bv False) \<turnstile> <nand , 0> \<longrightarrow>\<^sub>c (0(1 := [C \<mapsto> Bv True]))"
    unfolding nand_def
    by (simp add: b_conc_exec.intros(2))
  hence \<tau>'_def: "\<tau>' = (0(1:=[C \<mapsto> Bv True]))"
    using 2  by (simp add: b_conc_exec_deterministic)
  have nt: "next_time 0 \<tau>' = 1"
  proof -
    have "(0(1:=[C \<mapsto> Bv True])) \<noteq> 0"
      by (metis fun_upd_same option.distinct(1) zero_fun_def zero_option_def)
    moreover have "(LEAST n. dom (\<tau>' n) \<noteq> {}) = 1"
      unfolding \<tau>'_def
    proof (rule Least_equality)
      show "dom ((0(1 := [C \<mapsto> Bv True])) 1) \<noteq> {}"
        by auto
    next
      { fix y :: nat
        assume "\<not> 1 \<le> y"
        hence "y = 0"
          by auto
        hence "dom (((\<lambda>_. 0)(1 := [C \<mapsto> Bv True])) y) = {}"
          by (auto simp add: zero_map)
        hence "\<not> dom (((\<lambda>_. 0)(1 := [C \<mapsto> Bv True])) y) \<noteq> {}"
          by auto
        hence "\<not> dom ((0(1 := [C \<mapsto> Bv True])) y) \<noteq> {}"
          by (simp add: zero_fun_def) }
      thus "\<And>y::nat.  dom ((0(1 := [C \<mapsto> Bv True])) y) \<noteq> {} \<Longrightarrow> 1 \<le> y"
        by fastforce
    qed
    ultimately show ?thesis
      unfolding \<tau>'_def next_time_def by auto
  qed
  then show ?thesis 
    using 2 by auto
next
  case 3
  then show ?thesis 
    by (simp add: quiet_def)
next
  case 4
  then show ?thesis by auto
qed

definition nand2 :: "sig conc_stmt" where
  "nand2 = process {A, B} : Bcomp
                            (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1)
                            (Bassign_trans A (Bnand (Bsig A) (Bsig B)) 3)"

definition "test_trans = Pm_fmap (fmap_of_list [(4::nat, [A \<mapsto> Bv True, B \<mapsto> Bv True])])"
definition  "test2 = functional_simulate_fin 2 0 (\<lambda>x. Bv False) {A, B, C} 0 (\<lambda>x. Bv False) nand2 test_trans"

value [code] "to_transaction_sig (get_beh test2) C"

definition nand3 :: "sig conc_stmt" where
  "nand3 = process {A, B} : Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1"

\<comment> \<open>Specific lemmas about @{term "nand"} and @{term "nand3"}\<close>

lemma nand_does_not_modify_AB:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def (get_seq nand) \<tau> \<tau>'"
  shows "\<And>i. i \<ge> t \<Longrightarrow> s \<noteq> C \<Longrightarrow> \<tau> i s = \<tau>' i s"
  using b_seq_exec_modifies_local assms unfolding nand_def
  by (metis conc_stmt.sel(4) empty_set list.simps(15) signals_in.simps(3) singletonD)

lemma nand3_does_not_modify_AB:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def (get_seq nand3) \<tau> \<tau>'"
  shows "\<And>i. i \<ge> t \<Longrightarrow> s \<noteq> C \<Longrightarrow> \<tau> i s =  \<tau>' i s"
  using b_seq_exec_modifies_local assms unfolding nand3_def
  by (metis conc_stmt.sel(4) empty_set list.simps(15) signals_in.simps(2) singletonD)

lemma nand_does_not_modify_AB':
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def (get_seq nand) \<tau> \<tau>'"
  shows "\<And>i. s \<noteq> C \<Longrightarrow> \<tau> i s =  \<tau>' i s"
  using assms unfolding nand_def
  by (metis assms(2) b_seq_exec_preserve_trans_removal nand_does_not_modify_AB not_le)

lemma nand3_does_not_modify_AB':
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def (get_seq nand3) \<tau> \<tau>'"
  shows "\<And>i. s \<noteq> C \<Longrightarrow> \<tau> i s = \<tau>' i s"
  using assms unfolding nand3_def
  by (metis assms(2) b_seq_exec_preserve_trans_removal nand3_does_not_modify_AB not_le)

lemma maxtime_maxtime_bigstep:
  assumes "maxtime, maxtime, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <nand3, \<tau>> \<leadsto> beh"
  shows "get_beh beh = \<theta>"
proof -
  have "(maxtime, \<sigma>, \<theta>, \<tau>) = beh"
    using assms bau by blast
  then show ?thesis
    by force
qed 

lemma t_strictly_increasing:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <nand3, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "\<tau>' \<noteq> 0"
  shows "t < next_time t \<tau>'"
proof (cases "A \<in> \<gamma> \<or> B \<in> \<gamma>")
  case True
  then obtain x where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b x"
    by (metis assms(1) conc_cases(1) disjnt_insert1 nand3_def seq_cases_trans)
  hence \<tau>'_def: "\<tau>' = trans_post_raw C x (\<sigma> C) \<tau> t 1"
    using assms unfolding nand3_def
    by (meson True b_seq_exec.intros(5) b_seq_exec_deterministic conc_cases(1) disjnt_insert1)
  hence " \<tau>' t = 0"
    using assms(2) by (auto simp add: trans_post_raw_def post_raw_def preempt_raw_def)
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least assms b_conc_exec_preserve_trans_removal
    by (metis dual_order.strict_implies_order)
  show "t < next_time t \<tau>'"
  proof (rule ccontr)
    assume "\<not> t < next_time t \<tau>'"
    hence "t = next_time t \<tau>'"
      using `t \<le> next_time t \<tau>'` by auto
    hence least: "(LEAST n. dom (\<tau>' n) \<noteq> {}) = t"
      using `\<tau>' \<noteq> 0` unfolding next_time_def  by presburger
    have "\<exists>n. \<tau>' n \<noteq> 0"
      using `\<tau>' \<noteq> 0` by (metis (full_types) next_time_def lessI next_time_at_least
      not_le)
    hence 0: "\<exists>n. dom (\<tau>' n) \<noteq> {}"
    proof -
      { assume "dom (0::sig \<Rightarrow> val option) \<noteq> {}"
        then have ?thesis
          by (metis \<open>\<tau>' t = 0\<close>) }
      then show ?thesis
        using \<open>\<exists>n. \<tau>' n \<noteq> 0\<close> by force
    qed
    have "dom (\<tau>' t) \<noteq> {}"
      using LeastI_ex[OF 0] unfolding least by auto
    with `\<tau>' t = 0` show "False"
      by (metis dom_eq_empty_conv zero_map)
  qed
next
  case False
  hence \<tau>'_def: "\<tau>' = \<tau>"
    using assms unfolding nand3_def by auto
  have "\<tau>' t = 0"
    unfolding \<tau>'_def using assms(2) by auto
  have "next_time t \<tau>' = (LEAST n. dom (\<tau>' n) \<noteq> {})"
    using assms(3) unfolding next_time_def by auto
  also have " (LEAST n. dom (\<tau>' n) \<noteq> {}) \<noteq> t"
  proof (rule ccontr)
    have asm: "\<exists>x. dom (\<tau>' x) \<noteq> {}"
      using `\<tau>' \<noteq> 0`
    proof -
      have "\<exists>n. next_time n \<tau>' < n"
        by (metis next_time_def assms(3) lessI)
      then have "\<exists>n. \<tau>' n \<noteq> 0"
        by (meson next_time_at_least not_le)
      moreover
      { assume "\<exists>s n. \<tau>' n s \<noteq> None"
        then have ?thesis
          by (metis (no_types) dom_empty dom_eq_singleton_conv dom_fun_upd fun_upd_idem_iff
          option.distinct(1)) }
      ultimately show ?thesis
        using \<open>\<tau>' t = 0\<close> by fastforce
    qed
    assume "\<not> (LEAST n. dom (\<tau>' n) \<noteq> {}) \<noteq> t"
    hence "dom (\<tau>' t) \<noteq> {}"
      using LeastI_ex[where P="\<lambda>x. dom (\<tau>' x) \<noteq> {}"] asm by auto
    hence "\<tau>' t \<noteq> 0"
      by (metis dom_eq_empty_conv zero_map)
    with `\<tau>' t = 0` show "False" by auto
  qed
  finally have "next_time t \<tau>' \<noteq> t"
    by auto
  have *: "\<And>n. n < t \<Longrightarrow> \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal[OF assms(1-2)] by auto
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *, of "t"] by auto
  with `next_time t \<tau>' \<noteq> t` show ?thesis by auto
qed

lemma beh_res2:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "t < maxtime" and "cs = nand3"
  assumes "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
  shows   "\<And>n. n \<le> t \<Longrightarrow> (\<theta>(t:= Some o \<sigma>)) n = get_beh beh n"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  have *: "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal[OF 1(3) 1(8)] by auto
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *, of "t"] by auto
  have "\<tau>' = 0 \<or> \<tau>' \<noteq> 0" by auto
  moreover
  { assume "\<tau>' = 0"
    hence "next_time t \<tau>' = t + 1"
      unfolding next_time_def by auto
    moreover have " next_state t \<tau>' \<sigma> = \<sigma>"
      unfolding next_state_def Let_def
      `next_time t \<tau>' = t + 1` `\<tau>' = 0` override_on_def
      by (auto simp add: zero_fun_def zero_option_def)
    moreover hence "next_event t \<tau>' \<sigma> = {}"
      unfolding next_event_def next_state_def Let_def `next_time t \<tau>' = t + 1` `\<tau>' = 0`
      by (auto simp add: zero_fun_def zero_option_def)
    moreover hence "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = \<theta>(t := (Some o \<sigma>))"
      unfolding `next_time t \<tau>' = t + 1` add_to_beh_def by auto
    ultimately have ul: " maxtime, t + 1, \<sigma>, {}, \<theta>(t :=(Some o \<sigma>)), def \<turnstile> <cs, (\<tau>'(t + 1 := 0))> \<leadsto> res"
      using 1(5) by auto
    have "t + 1 < maxtime \<or> maxtime = t + 1"
      using "1.hyps"(4) \<open>next_time t \<tau>' = t + 1\<close> by linarith
    moreover
    { assume "t + 1 < maxtime"
      have "get_beh res = (\<theta>(t := Some o \<sigma>))(t + 1 := Some \<circ> \<sigma>)"
        using case_quiesce[OF `t + 1 < maxtime` _ ul] unfolding `\<tau>' = 0` quiet_def
        by (simp add: fun_upd_idem zero_fun_def)
      hence ?case
        using `n \<le> t` fun_upd_def by auto }
    moreover
    { assume "maxtime = t + 1"
      hence "get_beh res = \<theta> (t := Some o \<sigma>)"
        using ul "1.prems"(4) maxtime_maxtime_bigstep by blast
      hence ?case  by metis }
    ultimately have ?case
      by auto }
  moreover
  { assume "\<tau>' \<noteq> 0"
    hence "t < next_time t \<tau>'"
      using t_strictly_increasing[OF _ 1(8) `\<tau>' \<noteq> 0`] 1(3) unfolding `cs = nand3` by auto
    hence ind1: "n \<le> next_time t \<tau>'"
      using `n \<le> t` by auto
    have ind2: "(\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>  (\<tau>'(next_time t \<tau>' := 0)) n = 0) "
      by (simp add: nat_less_le next_time_at_least2)
    have "next_time t \<tau>' < maxtime \<or> maxtime = next_time t \<tau>'"
      using "1.hyps"(4) nat_less_le by blast
    moreover
    { assume ind3: "next_time t \<tau>' < maxtime"
      have h2: "\<And>n. next_time t \<tau>' \<le> n \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = 0"
        unfolding add_to_beh_def using "1.prems"(5) \<open>t \<le> next_time t \<tau>'\<close> by auto
      have " ((add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))(next_time t \<tau>' := Some \<circ> next_state t \<tau>' \<sigma>)) n = get_beh res n"
        using 1(6)[OF ind1 ind2 ind3 `cs = nand3` h2] by blast
      hence ?case
        using `n \<le> t` `t < next_time t \<tau>'` unfolding add_to_beh_def
        by (metis (full_types) fun_upd_apply le_antisym less_irrefl_nat less_or_eq_imp_le) }
    moreover
    { assume "maxtime = next_time t \<tau>'"
      have "t < next_time t \<tau>'"
        using `t < maxtime` `maxtime = next_time t \<tau>'` by auto
      have ?case
        using borderline_big_step[OF 1(5) 1(3) order.strict_implies_order[OF `t < maxtime`] `maxtime = next_time t \<tau>'` 1(11) _ ind1]
        `t < next_time t \<tau>'` unfolding add_to_beh_def  using nat_less_le
        by presburger }
    ultimately have ?case by auto }
  ultimately show ?case by blast
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> res cs)
  show ?case
    using 2(3) by transfer' auto
next
  case (3 t maxtime \<theta> res \<sigma> \<gamma> cs \<tau>)
  then show ?case by auto
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed 

(* lemma 
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "t \<le> maxtime" and "cs = nand3"
  assumes "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
  shows   "\<And>n. n \<le> t \<Longrightarrow> (\<theta>(t:= Some o \<sigma>)) n = get_beh beh n" *)

theorem nand3_correctness_ind:
  assumes "maxtime, t, \<sigma>, \<gamma>, beh, def \<turnstile> <cs, ctrans> \<leadsto> res"
  assumes "cs = nand3" and "maxtime = Suc i"
  assumes "\<And>n. n \<le> t \<Longrightarrow>  ctrans n = 0"
  assumes "\<And>s. s \<in> dom (ctrans t) \<Longrightarrow> \<sigma> s = the ( ctrans t s)"
  assumes "\<And>n. t \<le> n \<Longrightarrow>  beh n = 0"
  assumes "t \<le> i" and "A \<notin> \<gamma> \<and> B \<notin> \<gamma> \<Longrightarrow> bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))"
  assumes "\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig ctrans C) n = 0"
  assumes "conc_wt \<Gamma> cs" and "styping \<Gamma> \<sigma>" and "ttyping \<Gamma> beh" and "ttyping \<Gamma> ctrans" and "\<Gamma> C = Bty" and "styping \<Gamma> def"
  (* shows "bval_of (signal_of (def C) (get_beh res) C (Suc i)) \<longleftrightarrow> \<not> (bval_of (signal_of (\<sigma> A) ctrans A i) \<and> bval_of (signal_of (\<sigma> B) ctrans B i))" *)
  shows "bval_of (get_state res C) \<longleftrightarrow> \<not> (bval_of (signal_of (\<sigma> A) ctrans A i) \<and> bval_of (signal_of (\<sigma> B) ctrans B i))"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  have "t \<le> Suc i"
    using `t \<le> i` by auto
  have *: "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using "1.hyps"(3) "1.prems"(3) b_conc_exec_preserve_trans_removal  by (metis nat_less_le)
  hence **: "\<And>n. dom (\<tau>' n) \<noteq> {} \<Longrightarrow> t \<le> n"
    using zero_map by force
  hence "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *] by auto
  have h0: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow> (\<tau>' (next_time t \<tau>' := 0)) n = 0"
    using b_conc_exec_preserve_trans_removal[OF _ `\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0`]
    `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'`  by (simp add: nat_less_le next_time_at_least2)
  have h0': "\<And>n. n < next_time t \<tau>' \<Longrightarrow> \<tau>' n = 0"
  proof -
    fix n
    assume "n < next_time t \<tau>'"
    hence "n < t \<or> t \<le> n \<and> n < next_time t \<tau>'"
      using `t \<le> next_time t \<tau>'` by auto
    moreover
    { assume "n < t"
      hence " \<tau>' n = 0"
        using b_conc_exec_preserve_trans_removal[OF _ `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`]
        `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` by auto }
    moreover
    { assume "t \<le> n \<and> n < next_time t \<tau>'"
      hence " \<tau>' n = 0"
        using `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'`  using next_time_at_least2 by blast }
    ultimately show " \<tau>' n = 0"
      by auto
  qed
  have h1: "\<And>s. s \<in> dom ((\<tau>'(next_time t \<tau>':=0)) (next_time t \<tau>')) \<Longrightarrow>
                                        next_state t \<tau>' \<sigma> s = the ( (\<tau>'(next_time t \<tau>':=0)) (next_time t \<tau>') s)"
    unfolding next_state_def Let_def
    by (simp add: zero_fun_def zero_option_def)
  have h1': "\<And>s. s \<in> dom ( \<tau>' (next_time t \<tau>')) \<Longrightarrow>
                                        next_state t \<tau>' \<sigma> s = the ( \<tau>' (next_time t \<tau>') s)"
    unfolding next_state_def Let_def by auto
  have h2: "\<And>n. next_time t \<tau>' \<le> n \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = 0"
    unfolding add_to_beh_def
    using "1.prems"(5) \<open>t \<le> next_time t \<tau>'\<close> by auto
  { assume asm: "A \<notin> next_event t \<tau>' \<sigma> \<and> B \<notin> next_event t \<tau>' \<sigma> "
    have sigA: "next_state t \<tau>' \<sigma> A = \<sigma> A" and sigB: "next_state t \<tau>' \<sigma> B = \<sigma> B"
      using next_state_fixed_point asm by metis+
    hence "next_event t \<tau>' \<sigma> = {C} \<or> next_event t \<tau>' \<sigma> = {}"
    proof -
      have "\<And>S Sa. B \<in> S \<or> S \<subseteq> insert C Sa \<or> A \<in> S"
        by (metis (full_types) insertI1 sig.exhaust subset_eq)
      then show ?thesis
        by (meson asm subset_singleton_iff)
    qed
    moreover
    { assume "next_event t \<tau>' \<sigma> = {}"
      hence "C \<notin> next_event t \<tau>' \<sigma>"
        by auto
      hence sigC: "next_state t \<tau>' \<sigma> C = \<sigma> C"
        using next_state_fixed_point[OF `C \<notin> next_event t \<tau>' \<sigma>`]
        by auto
      have " A \<notin> \<gamma> \<and> B \<notin> \<gamma>  \<or> \<not> ( A \<notin> \<gamma> \<and> B \<notin> \<gamma> )" by auto
      moreover
      { assume " A \<notin> \<gamma> \<and> B \<notin> \<gamma> "
        hence " bval_of (\<sigma> C) = (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
          using `A \<notin> \<gamma> \<and> B \<notin> \<gamma> \<Longrightarrow> bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))` by auto
        hence " bval_of (next_state t \<tau>' \<sigma> C) = (\<not> (bval_of (next_state t \<tau>' \<sigma> A) \<and> bval_of (next_state t \<tau>' \<sigma> B)))"
          using sigA sigB sigC by auto }
      moreover
      { assume "\<not> ( A \<notin> \<gamma> \<and> B \<notin> \<gamma> )"
        have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
        proof (intro beval_raw.intros)
          have "seq_wt \<Gamma> (get_seq nand3)"
            using `conc_wt \<Gamma> cs` `cs = nand3`
            by (metis conc_stmt.distinct(1) conc_stmt.sel(4) conc_wt.cases nand3_def)
          hence "bexp_wt \<Gamma> (Bnand (Bsig A) (Bsig B)) (\<Gamma> C)"
            using seq_wt_cases(4)  by (metis conc_stmt.sel(4) nand3_def)
          hence "\<Gamma> A = Bty" and "\<Gamma> B = Bty"
            using bexp_wt_cases
            by (metis (full_types) "1.prems"(10) assms(13) assms(14) beval_raw.intros(1) beval_raw_preserve_well_typedness styping_def)+
          with `styping \<Gamma> \<sigma>` have "type_of (\<sigma> A) = Bty" and "type_of (\<sigma> B) = Bty"
            by (simp add: styping_def)+
          hence "is_Bv (\<sigma> A)" and "is_Bv (\<sigma> B)"
            by (metis ty.distinct(1) type_of.simps(2) val.collapse(2))+
          thus "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (\<sigma> A))" and
               "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (\<sigma> B))"
            using val.collapse(1)  by (simp add: beval_raw.intros(1))+
        qed
        hence "t , \<sigma> , \<gamma> , \<theta> , def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 , \<tau>> \<longrightarrow>\<^sub>s
                              trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
          by (simp add: b_seq_exec.intros(5))
        hence "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
          unfolding `cs = nand3` nand3_def
          by (simp add: \<open>\<not> (A \<notin> \<gamma> \<and> B \<notin> \<gamma>)\<close> b_conc_exec.intros(2))
        hence \<tau>'_def: "\<tau>' = trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
          using `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
          nand3_def  by (simp add: b_conc_exec_deterministic)
        have "(bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))) \<or>  (\<not> bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
          by auto
        moreover
        { assume "\<not> bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))"
          have "to_trans_raw_sig \<tau> C = 0"
            using `\<And>n. t < n \<Longrightarrow> (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
            unfolding to_trans_raw_sig_def zero_fun_def zero_option_def
            by (meson leI)
          hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
            unfolding to_trans_raw_sig_def by (metis zero_map)
          hence "post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)"
            by (metis "1.prems"(3) Nat.add_0_right \<open>(\<not> bval_of (\<sigma> C)) = (\<not> (bval_of (\<sigma> A) \<and> bval_of
            (\<sigma> B)))\<close> signal_of_def val.sel(1) zero_fun_def)
          hence "\<tau>' \<noteq> 0"
            by (metis \<open>(\<not> bval_of (\<sigma> C)) = (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))\<close> \<tau>'_def
            trans_post_raw_imply_neq_map_empty val.sel(1) zero_less_one)
          hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
            unfolding next_time_def by auto
          also have "... = t + 1"
          proof (rule Least_equality)
            show "dom ( \<tau>' (t + 1)) \<noteq> {}"
              using `post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)`
              unfolding \<tau>'_def trans_post_raw_def preempt_raw_def post_raw_def
              by (auto simp add: zero_fun_def zero_option_def)
          next
            have " \<tau>' t = 0"
              by (metis "1" \<open>\<tau>' \<noteq> 0\<close> \<open>t \<le> next_time t \<tau>'\<close> fun_upd_apply h0
              less_not_refl2 t_strictly_increasing)
            thus "\<And>y. dom (\<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
              using **
              by (metis Suc_eq_plus1 Suc_le_eq dom_eq_empty_conv nat_less_le zero_map)
          qed
          finally have "next_time t \<tau>' = t + 1"
            by auto
          moreover have " \<tau>' (t + 1) C = Some (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))))"
            using `post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)`
            unfolding \<tau>'_def  unfolding trans_post_raw_def post_raw_def
            by (auto split:option.split simp add: zero_fun_def zero_option_def)
          ultimately have "next_state t \<tau>' \<sigma> C = (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))))"
            unfolding next_state_def Let_def  by (simp add: domIff)
          hence " next_state t \<tau>' \<sigma> C = Bv (\<not> (bval_of (next_state t \<tau>' \<sigma> A) \<and> bval_of (next_state t \<tau>' \<sigma> B)))"
            using sigA sigB sigC by auto }
        moreover
        { assume "bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))"
          hence " next_state t \<tau>' \<sigma> C = Bv (\<not> (bval_of (next_state t \<tau>' \<sigma> A) \<and> bval_of (next_state t \<tau>' \<sigma> B)))"
            using sigA sigB sigC
            by (smt "1.prems"(10) assms(14) styping_def ty.simps(3) type_of.simps(2) val.exhaust_sel) }
        ultimately have " next_state t \<tau>' \<sigma> C = Bv (\<not> (bval_of (next_state t \<tau>' \<sigma> A) \<and> bval_of (next_state t \<tau>' \<sigma> B)))"
          by auto }
      ultimately have "next_state t \<tau>' \<sigma> C = Bv (\<not> (bval_of (next_state t \<tau>' \<sigma> A) \<and> bval_of (next_state t \<tau>' \<sigma> B)))"
        by (smt "1.prems"(10) assms(14) sigC styping_def ty.simps(3) type_of.simps(2) val.exhaust_sel) }
    moreover
    { assume "next_event t \<tau>' \<sigma> = {C}"
      hence "C \<in> dom ( \<tau>' (next_time t \<tau>'))"
        unfolding next_event_def Let_def by transfer' auto
      have " A \<notin> \<gamma> \<and> B \<notin> \<gamma>  \<or> \<not> ( A \<notin> \<gamma> \<and> B \<notin> \<gamma> )" by auto
      moreover
      { assume "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
        hence "\<tau>' = \<tau>"
          using ` t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
          nand3_def by auto
        have "\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0"
          using `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` 1(9)
           unfolding to_trans_raw_sig_def  by (metis le_neq_implies_less zero_fun_def)
        with `t \<le> next_time t \<tau>'`
        have "C \<notin> dom ( \<tau>' (next_time t \<tau>'))"
          using 1(8) unfolding `\<tau>' = \<tau>` next_time_def  unfolding to_trans_raw_sig_def
          by (simp add: domIff zero_option_def)
        with `C \<in> dom ( \<tau>' (next_time t \<tau>'))` have "False" by auto
        hence "next_state t \<tau>' \<sigma> C = Bv (\<not> (bval_of (next_state t \<tau>' \<sigma> A) \<and> bval_of (next_state t \<tau>' \<sigma> B)))"
          by auto }
      moreover
      { assume "\<not> ( A \<notin> \<gamma> \<and> B \<notin> \<gamma> )"
        have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
        proof (intro beval_raw.intros)
          have "seq_wt \<Gamma> (get_seq nand3)"
            using `conc_wt \<Gamma> cs` `cs = nand3`
            by (metis conc_stmt.distinct(1) conc_stmt.sel(4) conc_wt.cases nand3_def)
          hence "bexp_wt \<Gamma> (Bnand (Bsig A) (Bsig B)) (\<Gamma> C)"
            using seq_wt_cases(4)  by (metis conc_stmt.sel(4) nand3_def)
          hence "\<Gamma> A = Bty" and "\<Gamma> B = Bty"
            using bexp_wt_cases
            by (metis (full_types) "1.prems"(10) assms(13) assms(14) beval_raw.intros(1) beval_raw_preserve_well_typedness styping_def)+
          with `styping \<Gamma> \<sigma>` have "type_of (\<sigma> A) = Bty" and "type_of (\<sigma> B) = Bty"
            by (simp add: styping_def)+
          hence "is_Bv (\<sigma> A)" and "is_Bv (\<sigma> B)"
            by (metis ty.distinct(1) type_of.simps(2) val.collapse(2))+
          thus "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (\<sigma> A))" and
               "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (\<sigma> B))"
            using val.collapse(1)  by (simp add: beval_raw.intros(1))+
        qed
        hence "t , \<sigma> , \<gamma> , \<theta> , def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 , \<tau>> \<longrightarrow>\<^sub>s
                              trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
          by (simp add: b_seq_exec.intros(5))
        hence "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
          unfolding `cs = nand3` nand3_def
          by (simp add: \<open>\<not> (A \<notin> \<gamma> \<and> B \<notin> \<gamma>)\<close> b_conc_exec.intros(2))
        hence \<tau>'_def: "\<tau>' = trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
          using `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
          nand3_def  by (simp add: b_conc_exec_deterministic)
        have "\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0"
          using `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` 1(9)
          by (metis leI to_trans_raw_sig_def zero_fun_def)
        have "\<not> bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))"
        proof (rule ccontr)
          assume "\<not> (\<not> bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
          hence "bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))"
            by auto
          moreover have "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
            using `\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
            by (transfer', auto simp add: to_trans_raw_sig_def zero_fun_def zero_option_def )
          ultimately have "\<not> post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)"
            using post_necessary_raw_correctness
            by (smt "1.prems"(10) "1.prems"(3) Nat.add_0_right assms(14) signal_of_def styping_def
            ty.simps(3) type_of.simps(2) val.exhaust_sel zero_fun_def)
          hence "to_trans_raw_sig \<tau>' C = 0"
            using `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)` `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
            unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def to_trans_raw_sig_def
            zero_fun_def zero_option_def zero_map by auto
          with `C \<in> dom ( \<tau>' (next_time t \<tau>'))` have " \<tau>' (next_time t \<tau>') C \<noteq> 0"
            by (metis domIff fun_upd_same zero_fun_def zero_upd)
          hence " (to_trans_raw_sig \<tau>' C) (next_time t \<tau>') \<noteq> 0"
            unfolding next_time_def  unfolding to_trans_raw_sig_def by auto
          with `to_trans_raw_sig \<tau>' C = 0` show False
            unfolding next_time_def  unfolding to_trans_raw_sig_def
            by (metis zero_fun_def)
        qed
        have "to_trans_raw_sig \<tau> C = 0"
          using `\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          unfolding to_trans_raw_sig_def zero_fun_def zero_option_def  by (meson linear)
        hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
          unfolding to_trans_raw_sig_def  by (metis zero_fun_def zero_option_def)
        hence "post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)"
          by (metis "1.prems"(3) Nat.add_0_right \<open>(\<not> bval_of (\<sigma> C)) = (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma>
          B)))\<close> signal_of_def val.sel(1) zero_fun_def)
        hence "\<tau>' \<noteq> 0"
          by (metis \<open>C \<in> dom (\<tau>' (next_time t \<tau>'))\<close> domIff zero_fun_def zero_option_def)
        hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
          unfolding next_time_def by auto
        also have "... = t + 1"
        proof (rule Least_equality)
          show "dom ( \<tau>' (t + 1)) \<noteq> {}"
            using `post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)`
            unfolding \<tau>'_def trans_post_raw_def post_raw_def
            by (auto simp add: zero_fun_def zero_option_def)
        next
          have " \<tau>' t = 0"
            using "1.hyps"(3) "1.prems"(1) "1.prems"(3) \<open>\<tau>' \<noteq> 0\<close> next_time_at_least2 t_strictly_increasing
            by blast
          thus "\<And>y. dom ( \<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
            using **
            by (metis Suc_eq_plus1 Suc_le_eq dom_eq_empty_conv nat_less_le zero_map)
        qed
        finally have "next_time t \<tau>' = t + 1"
          by auto
        moreover have " \<tau>' (t + 1) C = Some (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))))"
          using `post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)`
          unfolding \<tau>'_def trans_post_raw_def post_raw_def
          by (auto split:option.split simp add: zero_fun_def zero_option_def)
        ultimately have "next_state t \<tau>' \<sigma> C = (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))))"
          unfolding next_state_def Let_def  by (simp add: domIff)
        hence " next_state t \<tau>' \<sigma> C = Bv (\<not> (bval_of (next_state t \<tau>' \<sigma> A) \<and> bval_of (next_state t \<tau>' \<sigma> B)))"
          using sigA sigB by auto }
      ultimately have " next_state t \<tau>' \<sigma> C = Bv (\<not> (bval_of (next_state t \<tau>' \<sigma> A) \<and> bval_of (next_state t \<tau>' \<sigma> B)))"
        by auto }
    ultimately have "next_state t \<tau>' \<sigma> C = Bv (\<not> (bval_of (next_state t \<tau>' \<sigma> A) \<and> bval_of (next_state t \<tau>' \<sigma> B)))"
      by auto
    hence "bval_of (next_state t \<tau>' \<sigma> C) = (\<not> (bval_of (next_state t \<tau>' \<sigma> A) \<and> bval_of (next_state t \<tau>' \<sigma> B)))"
      by simp }
  note h3 = this

  have h4': "\<And>n. next_time t \<tau>' < n \<Longrightarrow>  (to_trans_raw_sig \<tau>' C) n = 0"
  proof -
    fix n
    assume "next_time t \<tau>' < n"
    have "\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0"
      using `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` 1(9)
       unfolding to_trans_raw_sig_def by (metis leI zero_fun_def)
    have "A \<in> \<gamma> \<or> B \<in> \<gamma> \<or> (A \<notin> \<gamma> \<and> B \<notin> \<gamma>)"
      by auto
    moreover
    { assume "A \<in> \<gamma> \<or> B \<in> \<gamma>"
      have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
      proof (intro beval_raw.intros)
        have "seq_wt \<Gamma> (get_seq nand3)"
          using `conc_wt \<Gamma> cs` `cs = nand3`
          by (metis conc_stmt.distinct(1) conc_stmt.sel(4) conc_wt.cases nand3_def)
        hence "bexp_wt \<Gamma> (Bnand (Bsig A) (Bsig B)) (\<Gamma> C)"
          using seq_wt_cases(4)  by (metis conc_stmt.sel(4) nand3_def)
        hence "\<Gamma> A = Bty" and "\<Gamma> B = Bty"
          using bexp_wt_cases
          by (metis (full_types) "1.prems"(10) assms(13) assms(14) beval_raw.intros(1) beval_raw_preserve_well_typedness styping_def)+
        with `styping \<Gamma> \<sigma>` have "type_of (\<sigma> A) = Bty" and "type_of (\<sigma> B) = Bty"
          by (simp add: styping_def)+
        hence "is_Bv (\<sigma> A)" and "is_Bv (\<sigma> B)"
          by (metis ty.distinct(1) type_of.simps(2) val.collapse(2))+
        thus "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (\<sigma> A))" and
             "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (\<sigma> B))"
          using val.collapse(1)  by (simp add: beval_raw.intros(1))+
      qed
      hence "t , \<sigma> , \<gamma> , \<theta> , def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 , \<tau>> \<longrightarrow>\<^sub>s
                            trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
        by (simp add: b_seq_exec.intros(5))
      hence "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
        unfolding `cs = nand3` nand3_def
        by (simp add: \<open>A \<in> \<gamma> \<or> B \<in> \<gamma>\<close> b_conc_exec.intros(2))
      hence \<tau>'_def: "\<tau>' = trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
        using `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
        nand3_def  by (simp add: b_conc_exec_deterministic)
      have "(bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))) \<or> (\<not> bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
        by auto
      moreover
      { assume "bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))"
        moreover have "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
          using `\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          by (transfer', auto simp add: to_trans_raw_sig_def zero_fun_def zero_option_def )
        ultimately have "\<not> post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)"
          using post_necessary_raw_correctness
          by (smt "1.prems"(10) "1.prems"(3) add.right_neutral assms(14) signal_of_def styping_def
          ty.simps(3) type_of.simps(2) val.exhaust_sel zero_fun_def)
        hence "to_trans_raw_sig \<tau>' C = 0"
          using `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)` `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          unfolding \<tau>'_def trans_post_raw_def preempt_raw_def post_raw_def to_trans_raw_sig_def
          zero_fun_def zero_option_def zero_map by auto
        hence " (to_trans_raw_sig \<tau>' C) n = 0"
          by (simp add: zero_fun_def) }
      moreover
      { assume "(\<not> bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
        have "to_trans_raw_sig \<tau> C = 0"
          using `\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
           unfolding to_trans_raw_sig_def zero_fun_def zero_option_def
           by (meson linear)
        hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
          unfolding to_trans_raw_sig_def
          by (metis zero_fun_def zero_option_def)
        hence "post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)"
          by (metis "1.prems"(3) Nat.add_0_right \<open>(\<not> bval_of (\<sigma> C)) = (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma>
          B)))\<close> signal_of_def val.sel(1) zero_fun_def)
        hence "\<tau>' \<noteq> 0"
          by (metis One_nat_def \<tau>'_def cancel_comm_monoid_add_class.diff_cancel lessI signal_of_def
          trans_post_raw_imply_neq_map_empty zero_option_def)
        hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
          unfolding next_time_def by auto
        also have "... = t + 1"
        proof (rule Least_equality)
          show "dom ( \<tau>' (t + 1)) \<noteq> {}"
            using `post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)`
            unfolding \<tau>'_def  trans_post_raw_def post_raw_def
            by (auto simp add: zero_fun_def zero_option_def)
        next
          have " \<tau>' t = 0"
            using "1.hyps"(3) "1.prems"(1) "1.prems"(3) \<open>\<tau>' \<noteq> 0\<close> h0' t_strictly_increasing by auto
          thus "\<And>y. dom ( \<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
            using **
            by (metis Suc_eq_plus1 Suc_le_eq dom_eq_empty_conv nat_less_le zero_map)
        qed
        finally have "next_time t \<tau>' = t + 1"
          by auto
        hence " (to_trans_raw_sig \<tau>' C) n = 0"
          using `next_time t \<tau>' < n` unfolding \<tau>'_def  next_time_def
          trans_post_raw_def to_trans_raw_sig_def post_raw_def preempt_raw_def
          by (simp add: zero_option_def) }
      ultimately have " (to_trans_raw_sig \<tau>' C) n = 0"
        by auto }
    moreover
    { assume "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
      hence \<tau>'_def: "\<tau>' = \<tau>"
        using `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3` nand3_def
        by auto
      hence " (to_trans_raw_sig \<tau>' C) n = 0"
        using `t \<le> next_time t \<tau>'` `next_time t \<tau>' < n` `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0`
        by (metis le_less_trans) }
    ultimately show " (to_trans_raw_sig \<tau>' C) n = 0"
      by auto
  qed
  hence h4: "\<And>n. next_time t \<tau>' < n \<Longrightarrow>  (to_trans_raw_sig (\<tau>'(next_time t \<tau>' :=0)) C) n = 0"
    by (simp add: to_trans_raw_sig_def)
  have h5: "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
    using `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0` unfolding rem_curr_trans_def by  auto
  have "ttyping \<Gamma> \<tau>'"
    using conc_stmt_preserve_type_correctness[OF `conc_wt \<Gamma> cs` `styping \<Gamma> \<sigma>` `ttyping \<Gamma> \<theta>` `styping \<Gamma> def` `ttyping \<Gamma> \<tau>`
    `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'`]
    by auto
  have " styping \<Gamma> (next_state t \<tau>' \<sigma>)"
    using next_state_preserve_styping[OF `styping \<Gamma> \<sigma>` `ttyping \<Gamma> \<tau>'`] by auto
  have "ttyping \<Gamma> (\<tau>'(next_time t \<tau>' := 0))"
    using ttyping_rem_curr_trans[OF `ttyping \<Gamma> \<tau>'`] by auto
  have "ttyping \<Gamma> (add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))"
    using add_to_beh_preserve_type_correctness  using "1.prems"(10) "1.prems"(11) by blast
  have IH: " next_time t \<tau>' \<le> i \<Longrightarrow>
             bval_of (get_state res C) \<longleftrightarrow>
             \<not> (bval_of (signal_of (next_state t \<tau>' \<sigma> A) (\<tau>'(next_time t \<tau>' := 0)) A i) \<and>
                    bval_of (signal_of (next_state t \<tau>' \<sigma> B) (\<tau>'(next_time t \<tau>' := 0)) B i))"
    using 1(6)[OF `cs = nand3` `maxtime = Suc i` h0 h1 h2 _ h3 h4 `conc_wt \<Gamma> cs` `styping \<Gamma> (next_state t \<tau>' \<sigma>)`
               `ttyping \<Gamma> (add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))` `ttyping \<Gamma> (\<tau>'(next_time t \<tau>' := 0))` `\<Gamma> C = Bty` `styping \<Gamma> def`]
    by metis
  have "i < next_time t \<tau>' \<or> next_time t \<tau>' \<le> i"
    by auto
  moreover
  { assume "i < next_time t \<tau>'"
    have "t \<noteq> next_time t \<tau>'"
    proof (rule ccontr)
      assume "\<not> t \<noteq> next_time t \<tau>'" hence "t = next_time t \<tau>'" by auto
      hence "i < t"  using `i < next_time t \<tau>'` by auto
      with `t \<le> i` show False by auto
    qed

    have "A \<notin> \<gamma> \<and> B \<notin> \<gamma> \<or> A \<in> \<gamma> \<or> B \<in> \<gamma>" by auto
    moreover
    { assume "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
      hence \<tau>'_def: "\<tau>' = \<tau>"
        using `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3` nand3_def
        by auto
      have "signal_of (\<sigma> A) \<tau> A i = \<sigma> A" and "signal_of (\<sigma> B) \<tau> B i = \<sigma> B"
        using signal_of2_init[OF `t \<le> i`, of "\<tau>" _ "\<sigma>"] `i < next_time t \<tau>'` 1(10) 1(9)
        unfolding \<tau>'_def by auto
      note no_trans_c = 1(14)
      moreover have " \<tau> t = 0"
        by (simp add: "1.prems"(3))
      ultimately have 13: "\<And>n. t \<le> n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0"
         unfolding to_trans_raw_sig_def
        by (metis dual_order.order_iff_strict zero_fun_def)
      note next_big_step = 1(5)
      have "next_time t \<tau>' < maxtime \<or> next_time t \<tau>' = maxtime" 
        using `next_time t \<tau>' \<le> maxtime` by auto
      moreover
      { assume "next_time t \<tau>' < maxtime"
        hence pre: "\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n =  get_beh res n"
          using   beh_res[OF next_big_step h0] by auto
        hence "\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (\<theta>(t:=(Some o \<sigma>))) n =  get_beh res n"
          using`t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` unfolding add_to_beh_def by auto
        hence *: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>
             ((add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))(next_time t \<tau>' := Some \<circ> next_state t \<tau>' \<sigma>)) n =  get_beh res n"
          using beh_res2[OF next_big_step h0 `next_time t \<tau>' < maxtime` `cs = nand3` h2]
          by auto
        have "Suc i \<le> next_time t \<tau>'"
          using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` by auto
        hence "Suc i < next_time t \<tau>' \<or> Suc i = next_time t \<tau>'"
          by auto
        moreover have "\<not> Suc i < next_time t \<tau>'"
          using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` `maxtime = Suc i` by linarith
        ultimately have "Suc i = next_time t \<tau>'"
          by auto
        hence **: "signal_of (def C) (get_beh res) C (Suc i) =
               signal_of (def C) ((add_to_beh \<sigma> \<theta> t (next_time t \<tau>'))(next_time t \<tau>' := Some \<circ> next_state t \<tau>' \<sigma>)) C (Suc i)"
          using "1.prems"(1) "1.prems"(2) h0 h2 maxtime_maxtime_bigstep next_big_step \<open>next_time t \<tau>' < maxtime\<close> 
          by linarith
        define t' where "t' = next_time t \<tau>'"
        define \<sigma>' where "\<sigma>' = next_state t \<tau>' \<sigma>"
        define \<theta>' where "\<theta>' = add_to_beh \<sigma> \<theta> t (next_time t \<tau>')"
        hence "signal_of (def C) (get_beh res) C (Suc i) = signal_of (def C) (\<theta>' (t' := (Some o \<sigma>'))) C (Suc i)"
          unfolding t'_def \<sigma>'_def \<theta>'_def using ** by auto
        also have "... = \<sigma>' C"
          by (metis \<open>Suc i = next_time t \<tau>'\<close> fun_upd_same t'_def trans_some_signal_of)
        finally have "signal_of (def C) (get_beh res) C (Suc i) = \<sigma>' C"
          by auto
        also have "... = \<sigma> C"
        proof -
          have "C \<notin> dom (\<tau> (i + 1))"
            using 13 `t \<le> Suc i`  unfolding to_trans_raw_sig_def
            by (auto simp add: zero_map zero_option_def)
          moreover have *: "(next_time t \<tau>) = i + 1"
            using `Suc i = next_time t \<tau>'` unfolding \<tau>'_def by auto
          ultimately show ?thesis
            unfolding \<sigma>'_def next_state_def \<tau>'_def * Let_def by auto
        qed
        finally have "signal_of (def C) (get_beh res) C (Suc i) = \<sigma> C"
          by auto
        moreover have "bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))"
          using 1(13) `A \<notin> \<gamma> \<and> B \<notin> \<gamma>` by auto
        ultimately have ?case
          using `signal_of (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of (\<sigma> B) \<tau> B i = \<sigma> B` 
          using "1.prems"(2) \<open>Suc i = next_time t \<tau>'\<close> \<open>next_time t \<tau>' < maxtime\<close> by linarith }
      moreover
      { assume "maxtime = next_time t \<tau>'"
        hence pre: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n =  get_beh res n"
          using borderline_big_step[OF next_big_step `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` order.strict_implies_order[OF `t < maxtime`]
          `maxtime = next_time t \<tau>'` 1(11)]
          by auto
        have "Suc i = next_time t \<tau>'"
          using `maxtime = Suc i` `maxtime = next_time t \<tau>'` by auto
        hence "Suc i = next_time t \<tau>"
          unfolding \<tau>'_def by auto
        hence "signal_of (def C) (get_beh res) C (Suc i) =
               signal_of (def C) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) C (Suc i)"
          using \<open>maxtime = next_time t \<tau>'\<close> bau next_big_step "1.prems"(1) maxtime_maxtime_bigstep 
          by auto
        also have "... =  signal_of (def C) (\<theta> (t:= (Some o \<sigma>))) C (Suc i)"
          unfolding add_to_beh_def using `t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` by auto
        also have "... = \<sigma> C"
        proof -
          have "inf_time (to_trans_raw_sig (\<theta>(t := Some o \<sigma>))) C (Suc i) = Some t"
            using inf_time_update[OF 1(11)]  using \<open>t \<le> Suc i\<close> by simp
          thus ?thesis
            unfolding to_signal_def comp_def
            by (simp add: lookup_update to_trans_raw_sig_def)
        qed
        finally have "signal_of (def C) (get_beh res) C (Suc i) = \<sigma> C"
          by auto
        moreover have "bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))"
          using 1(13) `A \<notin> \<gamma> \<and> B \<notin> \<gamma>` by auto
        moreover have "get_state res  = next_state t \<tau>' \<sigma>"
          using 1(5) unfolding \<open>maxtime = next_time t \<tau>'\<close> 
        proof -
          assume "next_time t \<tau>', next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , add_to_beh \<sigma> \<theta> t (next_time t \<tau>'), def \<turnstile> <cs , \<tau>' (next_time t \<tau>' := 0)> \<leadsto> res"
          then have "(maxtime, next_state t \<tau> \<sigma>, add_to_beh \<sigma> \<theta> t maxtime, \<tau>(maxtime := 0)) = res"
            using \<open>maxtime = next_time t \<tau>'\<close> \<tau>'_def bau by blast
          then show ?thesis
            using \<tau>'_def by force
        qed
        moreover have "next_state t \<tau>' \<sigma> C = \<sigma> C"
          by (metis "13" \<open>t \<le> next_time t \<tau>'\<close> \<tau>'_def domIff next_state_def override_on_def
          to_trans_raw_sig_def zero_option_def)
        ultimately have ?case
          using `signal_of (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of (\<sigma> B) \<tau> B i = \<sigma> B` by simp }
      ultimately have ?case by auto }
    moreover
    { assume "A \<in> \<gamma> \<or> B \<in> \<gamma>"
      have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
      proof (intro beval_raw.intros)
        have "seq_wt \<Gamma> (get_seq nand3)"
          using `conc_wt \<Gamma> cs` `cs = nand3`
          by (metis conc_stmt.distinct(1) conc_stmt.sel(4) conc_wt.cases nand3_def)
        hence "bexp_wt \<Gamma> (Bnand (Bsig A) (Bsig B)) (\<Gamma> C)"
          using seq_wt_cases(4)  by (metis conc_stmt.sel(4) nand3_def)
        hence "\<Gamma> A = Bty" and "\<Gamma> B = Bty"
          using bexp_wt_cases
          by (metis (full_types) "1.prems"(10) assms(13) assms(14) beval_raw.intros(1) beval_raw_preserve_well_typedness styping_def)+
        with `styping \<Gamma> \<sigma>` have "type_of (\<sigma> A) = Bty" and "type_of (\<sigma> B) = Bty"
          by (simp add: styping_def)+
        hence "is_Bv (\<sigma> A)" and "is_Bv (\<sigma> B)"
          by (metis ty.distinct(1) type_of.simps(2) val.collapse(2))+
        thus "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (\<sigma> A))" and
             "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (\<sigma> B))"
          using val.collapse(1)  by (simp add: beval_raw.intros(1))+
      qed
      hence "t , \<sigma> , \<gamma> , \<theta> , def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 , \<tau>> \<longrightarrow>\<^sub>s
                            trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
        by (simp add: b_seq_exec.intros(5))
      hence "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
        unfolding `cs = nand3` nand3_def
        by (simp add: \<open>A \<in> \<gamma> \<or> B \<in> \<gamma>\<close> b_conc_exec.intros(2))
      hence \<tau>'_def: "\<tau>' = trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
        using `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` unfolding `cs = nand3`
        nand3_def  by (simp add: b_conc_exec_deterministic)
      have "(bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))) \<or> (\<not> bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
        by auto
      moreover
      { assume "bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))"
        moreover have "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  (\<tau>(t:=0)) i C = None)"
          using `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          by (auto simp add: to_trans_raw_sig_def zero_fun_def zero_option_def )
        ultimately have "\<not> post_necessary_raw 0 (\<tau>(t:=0)) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)"
          using post_necessary_raw_correctness `bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))`
          by (smt "1.prems"(10) "1.prems"(3) Nat.add_0_right add_Suc_right assms(14)
          fun_upd_idem_iff le_add2 order_refl plus_1_eq_Suc signal_of_def styping_def ty.simps(3)
          type_of.simps(2) val.exhaust_sel zero_option_def)
        hence "\<not> post_necessary_raw 0 \<tau> t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)"
          by (metis "1.prems"(3) fun_upd_triv order_refl)
        hence "to_trans_raw_sig \<tau>' C = 0"
          using `(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  (\<tau>(t:=0)) i C = None)`
          `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          unfolding \<tau>'_def trans_post_raw_def post_raw_def preempt_raw_def to_trans_raw_sig_def
                    zero_fun_def zero_option_def zero_map comp_def by auto
        have "next_time t \<tau> = next_time t \<tau>'"
        proof (cases "\<tau> = 0")
          case True
          hence "next_time t \<tau> = t + 1"
            unfolding next_time_def by auto
          have "\<tau>' = 0"
            using True `to_trans_raw_sig \<tau>' C = 0` `\<not> post_necessary_raw 0 (\<tau>(t:=0)) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)`
            unfolding \<tau>'_def
            by (auto simp add: zero_map zero_fun_def zero_option_def to_trans_raw_sig_def
                trans_post_raw_def preempt_raw_def)
          hence "next_time t \<tau>' = t + 1"
            by auto
          then show ?thesis
            using `next_time t \<tau> = t + 1` by auto
        next
          case False
          hence "next_time t \<tau> = (LEAST n. dom ( \<tau> n) \<noteq> {})"
            unfolding next_time_def by auto
          from `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          have lookC: " (to_trans_raw_sig \<tau> C) = 0"
            unfolding to_trans_raw_sig_def
            by (intro ext, metis leI zero_fun_def)
          hence " (to_trans_raw_sig \<tau> A) \<noteq> 0 \<or> (to_trans_raw_sig \<tau> B) \<noteq> 0"
            using False  unfolding to_trans_raw_sig_def
            unfolding zero_map zero_fun_def by (metis sig.exhaust)
          moreover have lookA: " (to_trans_raw_sig \<tau>' A) =  (to_trans_raw_sig \<tau> A)"
            unfolding \<tau>'_def trans_post_raw_def preempt_raw_def to_trans_raw_sig_def post_raw_def
            by auto
          moreover have lookB: " (to_trans_raw_sig \<tau>' B) =  (to_trans_raw_sig \<tau> B)"
            unfolding \<tau>'_def trans_post_raw_def preempt_raw_def to_trans_raw_sig_def post_raw_def
            by auto
          ultimately have "\<tau>' \<noteq> 0"
            by (auto simp add: to_trans_raw_sig_def zero_map zero_fun_def zero_option_def)
          hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
            unfolding next_time_def by auto
          also have "... = (LEAST n. dom (\<tau> n) \<noteq> {})"
            apply (rule LEAST_ext)
            using lookA lookB lookC `to_trans_raw_sig \<tau>' C = 0`
            unfolding to_trans_raw_sig_def zero_map zero_fun_def zero_option_def
            by (smt Collect_empty_eq dom_def sig.exhaust)
          finally show ?thesis
            by (simp add: \<open>next_time t \<tau> = (LEAST n. dom (\<tau> n) \<noteq> {})\<close>)
        qed
        hence "signal_of (\<sigma> A) \<tau> A i = \<sigma> A" and "signal_of (\<sigma> B) \<tau> B i = \<sigma> B"
          using  1(10) `i < next_time t \<tau>'`
          by (metis "1.prems"(3) "1.prems"(6) h5 nat_less_le not_le signal_of2_init)+
        note next_big_step = 1(5)
        have "next_time t \<tau>' < maxtime \<or> maxtime = next_time t \<tau>'" 
          by (simp add: "1.hyps"(4) nat_less_le)
        moreover
        { assume "next_time t \<tau>' < maxtime"
          hence pre: "\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n =  get_beh res n"
            using  beh_res[OF next_big_step h0] by auto
          hence "\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (\<theta> (t := (Some o \<sigma>))) n =  get_beh res n"
            using`t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` unfolding add_to_beh_def by auto
          hence *: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>
               ((add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (next_time t \<tau>' := Some \<circ> next_state t \<tau>' \<sigma>)) n =  get_beh res n"
            using beh_res2[OF next_big_step h0 `next_time t \<tau>' < maxtime` `cs = nand3` h2]
            by auto
          have "Suc i \<le> next_time t \<tau>'"
            using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` by auto
          hence "Suc i < next_time t \<tau>' \<or> Suc i = next_time t \<tau>'"
            by auto
          moreover have  "\<not> Suc i < next_time t \<tau>'"
            using `i < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` `maxtime = Suc i` by auto
          ultimately have "Suc i = next_time t \<tau>'"
            by auto
          hence **: "signal_of (def C) (get_beh res) C (Suc i) =
                 signal_of (def C) ((add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) (next_time t \<tau>' := Some \<circ> next_state t \<tau>' \<sigma>)) C (Suc i)"
            using "1.prems"(1) "1.prems"(2) h0 h2 maxtime_maxtime_bigstep next_big_step 
            using \<open>next_time t \<tau>' < maxtime\<close> by linarith
          define t' where "t' = next_time t \<tau>'"
          define \<sigma>' where "\<sigma>' = next_state t \<tau>' \<sigma>"
          define \<theta>' where "\<theta>' = add_to_beh \<sigma> \<theta> t (next_time t \<tau>')"
          hence "signal_of (def C) (get_beh res) C (Suc i) = signal_of (def C) (\<theta>'(t' := (Some o \<sigma>'))) C (Suc i)"
            unfolding t'_def \<sigma>'_def \<theta>'_def using ** by auto
          also have "... = \<sigma>' C"
            by (metis \<open>Suc i = next_time t \<tau>'\<close> fun_upd_same t'_def trans_some_signal_of)
          finally have "signal_of (def C) (get_beh res) C (Suc i) = \<sigma>' C"
            by auto
          also have "... = \<sigma> C"
          proof -
            have "\<And>n. C \<notin> dom ( \<tau>' n)"
              using `to_trans_raw_sig \<tau>' C = 0`   unfolding to_trans_raw_sig_def
              by (metis domIff fun_upd_idem_iff zero_fun_def zero_upd)
            thus ?thesis
              unfolding \<sigma>'_def next_state_def \<tau>'_def Let_def  by simp
          qed
          finally have "signal_of (def C) (get_beh res) C (Suc i) = \<sigma> C"
            by auto
          hence ?case
            using `signal_of (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of (\<sigma> B) \<tau> B i = \<sigma> B`
            `bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))` 
            using "1.prems"(2) \<open>Suc i = next_time t \<tau>'\<close> \<open>next_time t \<tau>' < maxtime\<close> by linarith }
        moreover
        { assume "maxtime = next_time t \<tau>'"
          hence pre: "\<And>n. n \<le> next_time t \<tau>' \<Longrightarrow>  (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n =  get_beh res n"
            using borderline_big_step[OF next_big_step `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` order.strict_implies_order[OF `t < maxtime`] 
                    `maxtime = next_time t \<tau>'` 1(11)]
            by auto
          have "Suc i = next_time t \<tau>'"
            using `maxtime = Suc i` `maxtime = next_time t \<tau>'` by auto
          hence "signal_of (def C) (get_beh res) C (Suc i) =
                 signal_of (def C) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) C (Suc i)"
            using \<open>maxtime = next_time t \<tau>'\<close> bau next_big_step "1.prems"(1) maxtime_maxtime_bigstep 
            by auto
          also have "... =  signal_of (def C) (\<theta>(t := (Some o \<sigma>))) C (Suc i)"
            unfolding add_to_beh_def using `t \<le> next_time t \<tau>'` `t \<noteq> next_time t \<tau>'` by auto
          also have "... = \<sigma> C"
          proof -
            have "inf_time (to_trans_raw_sig (\<theta>(t := Some o \<sigma>))) C (Suc i) = Some t"
              using inf_time_update[OF 1(11)]  using \<open>t \<le> Suc i\<close> by simp
            thus ?thesis
              unfolding to_signal_def comp_def
              by (simp add: lookup_update to_trans_raw_sig_def)
          qed
          finally have "signal_of (def C) (get_beh res) C (Suc i) = \<sigma> C"
            by auto
          have "get_state res = next_state t \<tau>' \<sigma>"
            using next_big_step unfolding \<open>maxtime = next_time t \<tau>'\<close>
            by (metis "1.prems"(1) \<open>maxtime = next_time t \<tau>'\<close> b_simulate_fin.intros(4)
            b_simulate_fin_deterministic comp_eq_dest_lhs fst_conv snd_conv)
          have "next_state t \<tau>' \<sigma> C = \<sigma> C"
            by (metis (mono_tags, hide_lams) \<open>to_trans_raw_sig \<tau>' C = 0\<close> domIff next_state_def
            override_on_def to_trans_raw_sig_def zero_fun_def zero_option_def)
          hence ?case
            using `signal_of (\<sigma> A) \<tau> A i = \<sigma> A` `signal_of (\<sigma> B) \<tau> B i = \<sigma> B` `bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))`
            using \<open>get_state res = next_state t \<tau>' \<sigma>\<close> by auto }
        ultimately have ?case by auto }
      moreover
      { assume "(\<not> bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
        have "to_trans_raw_sig \<tau> C = 0"
          using `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
          unfolding to_trans_raw_sig_def zero_fun_def zero_option_def  by (meson le_less_linear)
        hence "(\<forall>i\<ge>t. i \<le> t + 1 \<longrightarrow>  \<tau> i C = None)"
          unfolding to_trans_raw_sig_def zero_fun_def zero_option_def by metis
        hence post_nec: "post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)"
          by (metis "1.prems"(3) Nat.add_0_right \<open>(\<not> bval_of (\<sigma> C)) = (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma>
          B)))\<close> le_add1 signal_of_def val.sel(1) zero_option_def)
        hence "\<tau>' \<noteq> 0"
          by (metis One_nat_def \<tau>'_def add_diff_cancel_left' plus_1_eq_Suc signal_of_def
          trans_post_raw_imply_neq_map_empty zero_less_one zero_option_def)
        hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
          unfolding next_time_def by auto
        also have "... = t + 1"
        proof (rule Least_equality)
          show "dom ( \<tau>' (t + 1)) \<noteq> {}"
            using `post_necessary_raw 0 ( \<tau>) t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)`
            unfolding \<tau>'_def trans_post_raw_def preempt_raw_def post_raw_def
            by (auto simp add: zero_fun_def zero_option_def)
        next
          { fix y
            assume "\<not> t + 1 \<le> y" hence "y < t + 1" by auto
            hence "dom ( \<tau>' y) = {}"
              using 1(9) unfolding \<tau>'_def  trans_post_raw_def preempt_raw_def post_raw_def
              by (auto simp add:zero_map) }
          thus "\<And>y. dom ( \<tau>' y) \<noteq> {} \<Longrightarrow> t + 1 \<le> y"
            by auto
        qed
        finally have "next_time t \<tau>' = t + 1"
          by auto
        with `i < next_time t \<tau>'` have "i < t + 1" by auto
        with `t \<le> i` have "i = t" by auto
        hence "signal_of (\<sigma> A) \<tau> A i = signal_of (\<sigma> A) \<tau> A t"
          by auto
        also have "... = \<sigma> A"
        proof -
          consider "inf_time (to_trans_raw_sig \<tau>) A t = None" |  ta where "inf_time (to_trans_raw_sig \<tau>) A t = Some ta"
            by blast
          thus ?thesis
          proof (cases)
            case 1
            then show ?thesis unfolding to_signal_def comp_def by auto
          next
            case 2
            have "t = ta"
            proof (rule ccontr)
              assume "t \<noteq> ta"
              with 2 have "ta \<le> t" by (auto dest!:inf_time_at_most)
              with `t \<noteq> ta` have "ta < t" by auto
              hence "\<tau> ta = 0"
                using 1(9) by auto
              have "ta \<in> dom (to_trans_raw_sig \<tau> A)"
                by (metis "2" \<open>i = t\<close> dom_is_keys inf_time_some_exists)
              hence "(to_trans_raw_sig \<tau> A) ta \<noteq> 0"
                 unfolding to_trans_raw_sig_def by (metis domIff zero_fun_def zero_map)
              hence "\<tau> ta \<noteq> 0"
                 unfolding to_trans_raw_sig_def by (metis zero_fun_def)
              thus False
                using `\<tau> ta = 0` by auto
            qed
            hence "inf_time (to_trans_raw_sig \<tau>) A t = Some t"
              using 2 by auto
            hence "t \<in> dom (to_trans_raw_sig \<tau> A)"
              by (metis Femto_VHDL_raw.keys_def dom_def inf_time_some_exists zero_option_def)
            hence "A \<in> dom (\<tau> t)"
               unfolding to_trans_raw_sig_def by auto
            hence "the ((to_trans_raw_sig \<tau> A) t) = \<sigma> A"
              using 1(10)  unfolding to_trans_raw_sig_def by auto
            then show ?thesis
              using `inf_time (to_trans_raw_sig \<tau>) A t = Some t` unfolding to_signal_def comp_def
              by auto
          qed
        qed
        finally have sigA: "signal_of (\<sigma> A) \<tau> A i = \<sigma> A"
          by auto
        have "signal_of (\<sigma> B) \<tau> B i = signal_of (\<sigma> B) \<tau> B t"
          using `i = t` by auto
        also have "... = \<sigma> B"
        proof -
        consider "inf_time (to_trans_raw_sig \<tau>) B t = None" |  ta where "inf_time (to_trans_raw_sig \<tau>) B t = Some ta"
          by blast
        thus ?thesis
        proof (cases)
          case 1
          then show ?thesis unfolding to_signal_def comp_def by auto
        next
          case 2
          have "t = ta"
          proof (rule ccontr)
            assume "t \<noteq> ta"
            with 2 have "ta \<le> t" by (auto dest!:inf_time_at_most)
            with `t \<noteq> ta` have "ta < t" by auto
            hence "\<tau> ta = 0"
              using 1(9) by auto
            have "ta \<in> dom ((to_trans_raw_sig \<tau> B))"
              by (metis "2" Femto_VHDL_raw.keys_def dom_def inf_time_some_exists zero_option_def)
            hence "(to_trans_raw_sig \<tau> B) ta \<noteq> 0"
              unfolding to_trans_raw_sig_def
              by (metis domIff zero_fun_def zero_map)
            hence "\<tau> ta \<noteq> 0"
              unfolding to_trans_raw_sig_def
              by (metis zero_fun_def)
            thus False
              using `\<tau> ta = 0` by auto
          qed
          hence "inf_time (to_trans_raw_sig \<tau>) B t = Some t"
            using 2 by auto
          hence "t \<in> dom ((to_trans_raw_sig \<tau> B))"
            by (metis Femto_VHDL_raw.keys_def dom_def inf_time_some_exists zero_option_def)
          hence "B \<in> dom (\<tau> t)"
            unfolding to_trans_raw_sig_def by auto
          hence "the ((to_trans_raw_sig \<tau> B) t) = \<sigma> B"
            using 1(10) unfolding to_trans_raw_sig_def by auto
          then show ?thesis
            using `inf_time (to_trans_raw_sig \<tau>) B t = Some t` unfolding to_signal_def comp_def
            by auto
        qed
        qed
        finally have sigB: "signal_of (\<sigma> B) \<tau> B i = \<sigma> B"
          by auto
        note next_big_step = 1(5)
        have "next_time t \<tau>' = maxtime"
          using `next_time t \<tau>' = t + 1` `maxtime = Suc i` `i = t` by auto
        have "get_state res = next_state t \<tau>' \<sigma>"
          using next_big_step unfolding \<open>next_time t \<tau>' = maxtime\<close> 
        proof -
          assume "maxtime, maxtime , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , add_to_beh \<sigma> \<theta> t maxtime, def \<turnstile> <cs , \<tau>' (maxtime := 0)> \<leadsto> res"
          then have "(maxtime, next_state t \<tau>' \<sigma>, add_to_beh \<sigma> \<theta> t maxtime, \<tau>'(maxtime := 0)) = res"
            using bau by blast
          then show ?thesis
            by force
        qed
        have "\<tau>' = post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) \<tau> (t + 1)"
          unfolding \<tau>'_def trans_post_raw_def using post_nec by auto
        hence "\<tau>' (next_time t \<tau>') C = Some (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))))"
          by (metis \<open>next_time t \<tau>' = t + 1\<close> fun_upd_same post_raw_def)
        hence "next_state t \<tau>' \<sigma> C = Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
          unfolding next_state_def Let_def 
          by (simp add: domIff)
        hence ?case
          using \<open>get_state res = next_state t \<tau>' \<sigma>\<close> sigA sigB by auto }
      ultimately have ?case by auto }
    ultimately have ?case by auto }
  moreover
  { assume "next_time t \<tau>' \<le> i"
    with IH have IH': "bval_of (get_state res C) = 
      (\<not> (bval_of (signal_of (next_state t \<tau>' \<sigma> A) (\<tau>'(next_time t \<tau>' := 0)) A i) \<and>
          bval_of (signal_of (next_state t \<tau>' \<sigma> B) (\<tau>'(next_time t \<tau>' := 0)) B i)))"
      by auto
    have Anot: "A \<notin> set (signals_from cs)"
      unfolding `cs = nand3` nand3_def by auto
    have "signal_of (\<sigma> A) \<tau> A i = signal_of (next_state t \<tau>' \<sigma> A) \<tau>' A i"
      using b_conc_exec_does_not_modify_signals2[OF h5 `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` Anot `next_time t \<tau>' \<le> i`]
      unfolding `cs = nand3` nand3_def by auto
    also have "... = signal_of (next_state t \<tau>' \<sigma> A) (\<tau>'(next_time t \<tau>' := 0)) A i"
      using h0' h1' by(intro sym[OF signal_of_rem_curr_trans_at_t])
    finally have "signal_of (next_state t \<tau>' \<sigma> A) (\<tau>'(next_time t \<tau>':=0)) A i  = signal_of (\<sigma> A) \<tau> A i"
      by auto

    have Bnot: "B \<notin> set (signals_from cs)"
      unfolding `cs = nand3` nand3_def by auto
    have " signal_of (\<sigma> B) \<tau> B i = signal_of (next_state t \<tau>' \<sigma> B) \<tau>' B i"
      using b_conc_exec_does_not_modify_signals2[OF h5 `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` Bnot `next_time t \<tau>' \<le> i`]
      unfolding `cs = nand3` nand3_def by auto
    also have "... = signal_of (next_state t \<tau>' \<sigma> B) (\<tau>'(next_time t \<tau>' := 0)) B i"
      using h0' h1' by(intro sym[OF signal_of_rem_curr_trans_at_t])
    finally have "signal_of (next_state t \<tau>' \<sigma> B) (\<tau>'(next_time t \<tau>' := 0)) B i  = signal_of (\<sigma> B) \<tau> B i"
      by auto
    hence ?case
      using `signal_of (next_state t \<tau>' \<sigma> A) (\<tau>'(next_time t \<tau>' := 0)) A i  = signal_of (\<sigma> A) \<tau> A i` IH'
      by auto }
  ultimately show ?case by auto
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  have "\<tau> = 0"
    using `quiet \<tau> \<gamma>` unfolding quiet_def by metis
  hence *: "signal_of (\<sigma> A) \<tau> A i = \<sigma> A" and **: "signal_of (\<sigma> B) \<tau> B i = \<sigma> B"
    unfolding to_signal_def by auto
  have "inf_time (to_trans_raw_sig (\<theta>(t:=Some o \<sigma>))) C (Suc i) = Some t"
    unfolding to_signal_def to_trans_raw_sig_def
  proof -
    have 0: "t \<in> keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C)"
      unfolding keys_def by (auto simp add: zero_option_def)
    moreover have 1: "t \<le> Suc i"
      using 3 by auto
    ultimately have "\<exists>k\<in>Femto_VHDL_raw.keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C). k \<le> Suc i"
      by auto
    hence "inf_time (\<lambda>sig n. (\<theta>(t := Some \<circ> \<sigma>)) n sig) C (Suc i) =
            Some (GREATEST k. k \<in> Femto_VHDL_raw.keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C) \<and> k \<le> Suc i)"
      unfolding inf_time_def by auto
    also have "... = Some t"
    proof (unfold option.inject, intro Greatest_equality)
      show "t \<in> Femto_VHDL_raw.keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C) \<and> t \<le> Suc i"
        using 0 1 by auto
    next
      { fix y
        assume "\<not> y \<le> t" hence "t < y" by auto
        hence "y \<notin> keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C)"
          using 3(7) by (auto simp add: keys_def zero_map zero_option_def)
        hence "\<not> (y \<in> Femto_VHDL_raw.keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C) \<and> y \<le> Suc i)"
          by auto }
      thus "\<And>y. y \<in> Femto_VHDL_raw.keys (\<lambda>n. (\<theta>(t := Some \<circ> \<sigma>)) n C) \<and> y \<le> Suc i \<Longrightarrow> y \<le> t"
        by auto
    qed
    finally show "inf_time (\<lambda>sig n. (\<theta>(t := Some \<circ> \<sigma>)) n sig) C (Suc i) = Some t"
      by auto
  qed
  hence "signal_of (def C) (\<theta>(t := Some \<circ> \<sigma>)) C (Suc i) = \<sigma> C"
    unfolding to_signal_def comp_def to_trans_raw_sig_def by auto
  moreover have "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
    using `quiet \<tau> \<gamma>` unfolding quiet_def  by (metis emptyE)
  ultimately show ?case
    using 3(9) * **  by (metis comp_apply fst_conv snd_conv)
next
  case (4 t maxtime \<sigma> \<gamma> def cs \<tau>)
  then show ?case by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  hence "t + 1 \<le> maxtime"
    by auto
  have " A \<notin> \<gamma> \<and> B \<notin> \<gamma> \<or> \<not> ( A \<notin> \<gamma> \<and> B \<notin> \<gamma>)"
    by auto
  moreover
  { assume " \<not> (A \<notin> \<gamma> \<and> B \<notin> \<gamma>)"
    hence "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1) \<tau> \<tau>'"
      using 2(3)  by (metis "2.prems"(1) conc_cases(1) disjnt_insert1 nand3_def)
    have "\<exists>v. t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> (Bnand (Bsig A) (Bsig B)) \<longrightarrow>\<^sub>b v"
      using beval_raw_progress 2 
      by (meson \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> seq_cases_trans)
    have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> (Bnand (Bsig A) (Bsig B)) \<longrightarrow>\<^sub>b Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
      apply (intro beval_raw.intros(12))
      by (metis (no_types, lifting) "2.prems"(1) "2.prems"(10) "2.prems"(11) "2.prems"(14)
      "2.prems"(9) \<open>\<exists>v. t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b v\<close> assms(14) beval_cases(1)
      beval_cases(9) beval_raw_preserve_well_typedness conc_stmt.sel(4) conc_stmt.simps(4)
      conc_wt.cases nand3_def seq_wt_cases(4) ty.simps(3) type_of.simps(2) val.collapse(1)
      val.disc(1))+    
    hence \<tau>'_def: "\<tau>' = trans_post_raw C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C) \<tau> t 1"
      using 2(3) unfolding `cs = nand3` nand3_def 
      by (meson \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>
      b_seq_exec.intros(5) b_seq_exec_deterministic)
    have "bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))"
    proof (rule ccontr)
      assume " bval_of (\<sigma> C) \<noteq> (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
      hence  "\<not>  bval_of (\<sigma> C) \<longleftrightarrow> (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))"
        by auto
      hence "post_necessary_raw 0 \<tau> t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)"
        by (metis "2.prems"(3) Nat.add_0_right signal_of_def val.sel(1) zero_fun_def)
      hence "next_time t \<tau>' = t + 1"
        using \<tau>'_def unfolding trans_post_raw_def
        by (metis (mono_tags, lifting) "2.hyps"(1) "2.hyps"(4) Nat.add_0_right One_nat_def Suc_leI
        add_Suc_right cancel_comm_monoid_add_class.diff_cancel fun_upd_same le_less_trans lessI
        option.simps(3) post_raw_def until_next_time_zero zero_fun_def zero_option_def)
      thus "False"
        using "2.hyps"(4) \<open>t + 1 \<le> maxtime\<close> by linarith
    qed 
    hence "\<not> post_necessary_raw 0 \<tau> t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)"
      unfolding post_necessary_raw_correctness 
      by (smt "2.prems"(10) "2.prems"(3) Nat.add_0_right assms(14) styping_def ty.simps(3)
      type_of.simps(2) val.exhaust_sel zero_fun_def zero_option_def)
    have "next_time t \<tau> = next_time t \<tau>'"
    proof (cases "\<tau> = 0")
      case True
      hence "next_time t \<tau> = t + 1"
        unfolding next_time_def by auto
      have "\<tau>' = 0"
        using True `\<not> post_necessary_raw 0 \<tau> t C (Bv (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)`
        unfolding \<tau>'_def
        by (auto simp add: zero_map zero_fun_def zero_option_def to_trans_raw_sig_def
            trans_post_raw_def preempt_raw_def)
      hence "next_time t \<tau>' = t + 1"
        by auto
      then show ?thesis
        using `next_time t \<tau> = t + 1` by auto
    next
      case False
      hence "next_time t \<tau> = (LEAST n. dom ( \<tau> n) \<noteq> {})"
        unfolding next_time_def by auto
      from `\<And>n. t < n \<Longrightarrow>  (to_trans_raw_sig \<tau> C) n = 0` `\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0`
      have lookC: " (to_trans_raw_sig \<tau> C) = 0"
        unfolding to_trans_raw_sig_def
        by (intro ext, metis leI zero_fun_def)
      hence " (to_trans_raw_sig \<tau> A) \<noteq> 0 \<or> (to_trans_raw_sig \<tau> B) \<noteq> 0"
        using False  unfolding to_trans_raw_sig_def
        unfolding zero_map zero_fun_def by (metis sig.exhaust)
      moreover have lookA: " (to_trans_raw_sig \<tau>' A) =  (to_trans_raw_sig \<tau> A)"
        unfolding \<tau>'_def trans_post_raw_def preempt_raw_def to_trans_raw_sig_def post_raw_def
        by auto
      moreover have lookB: " (to_trans_raw_sig \<tau>' B) =  (to_trans_raw_sig \<tau> B)"
        unfolding \<tau>'_def trans_post_raw_def preempt_raw_def to_trans_raw_sig_def post_raw_def
        by auto
      ultimately have "\<tau>' \<noteq> 0"
        by (auto simp add: to_trans_raw_sig_def zero_map zero_fun_def zero_option_def)
      hence "next_time t \<tau>' = (LEAST n. dom ( \<tau>' n) \<noteq> {})"
        unfolding next_time_def by auto
      also have "... = (LEAST n. dom (\<tau> n) \<noteq> {})"
        apply (rule LEAST_ext)
        using lookA lookB lookC  unfolding to_trans_raw_sig_def zero_map zero_fun_def zero_option_def
        by (metis (mono_tags, lifting) One_nat_def \<open>\<not> post_necessary_raw 0 \<tau> t C (Bv (\<not> (bval_of (\<sigma>
        A) \<and> bval_of (\<sigma> B)))) (\<sigma> C)\<close> \<tau>'_def add_diff_cancel_left' fun_upd_triv plus_1_eq_Suc
        preempt_raw_def trans_post_raw_def)
      finally show ?thesis
        by (simp add: \<open>next_time t \<tau> = (LEAST n. dom (\<tau> n) \<noteq> {})\<close>)
    qed    
    hence "signal_of (\<sigma> A) \<tau> A i = \<sigma> A" and "signal_of (\<sigma> B) \<tau> B i = \<sigma> B"
      using  2(10) 
      by (metis "2.hyps"(4) "2.prems"(2) le_Suc_eq le_less_trans next_time_at_least2 signal_of_def zero_fun_def)+
    hence ?case
      by (simp add: \<open>bval_of (\<sigma> C) = (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))\<close>) }
  moreover
  { assume "A \<notin> \<gamma> \<and> B \<notin> \<gamma>"
    hence "bval_of (\<sigma> C) \<longleftrightarrow> \<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B))"
      using 2 by auto 
    hence \<tau>'_def: "\<tau>' = \<tau>"
      using 2(3) \<open>A \<notin> \<gamma> \<and> B \<notin> \<gamma>\<close> unfolding `cs = nand3` nand3_def by auto
    have "signal_of (\<sigma> A) \<tau> A i = \<sigma> A" and "signal_of (\<sigma> B) \<tau> B i = \<sigma> B"
      by (metis "2.hyps"(4) "2.prems"(2) \<tau>'_def dual_order.strict_trans less_Suc_eq_le
      next_time_at_least2 signal_of_def zero_fun_def)+
    hence ?case
      by (simp add: \<open>bval_of (\<sigma> C) = (\<not> (bval_of (\<sigma> A) \<and> bval_of (\<sigma> B)))\<close>) }
  ultimately show ?case 
    by auto
qed

lemma signal_of2_cong_neq_none_at_0:
  assumes " (to_trans_raw_sig \<tau> sig) 0 \<noteq> None"
  shows "signal_of def1 \<tau> sig i = signal_of def2 \<tau> sig i"
proof -
  have "inf_time (to_trans_raw_sig \<tau>) sig i \<noteq> None"
  proof (rule ccontr)
    assume "\<not> inf_time (to_trans_raw_sig \<tau>) sig i \<noteq> None"
    hence "inf_time (to_trans_raw_sig \<tau>) sig i = None"
      by auto
    hence "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau> sig) k = 0"
      by (auto dest!: inf_time_noneE2)
    hence " (to_trans_raw_sig \<tau> sig) 0 = 0"
      by auto
    with assms show "False"
      by (simp add: zero_option_def)
  qed
  thus ?thesis
    unfolding to_signal_def comp_def by auto
qed

theorem nand3_correctness:
  assumes "b_simulate (Suc i) def nand3 \<tau> res"
  assumes "to_trans_raw_sig \<tau> C = 0"
  assumes "conc_wt \<Gamma> nand3" and "styping \<Gamma> def" and "\<Gamma> C = Bty" and "ttyping \<Gamma> \<tau>"
  shows "bval_of (get_state res C) \<longleftrightarrow>
          \<not> (bval_of (signal_of (def A) \<tau> A i) \<and> bval_of (signal_of (def B) \<tau> B i))"
proof (cases " \<tau> 0 = 0")
  case True
  have "seq_wt \<Gamma> (get_seq nand3)"
    using `conc_wt \<Gamma> nand3`
    by (metis conc_stmt.distinct(1) conc_stmt.sel(4) conc_wt.cases nand3_def)
  hence "bexp_wt \<Gamma> (Bnand (Bsig A) (Bsig B)) (\<Gamma> C)"
    using seq_wt_cases(4)  by (metis conc_stmt.sel(4) nand3_def)
  hence "\<Gamma> A = Bty" and "\<Gamma> B = Bty"
    using bexp_wt_cases  by (smt assms(5) bexp.distinct bexp.inject(1) bexp_wt.cases)+
  hence "is_Bv (def A)" and "is_Bv (def B)"
    by (metis assms(4) styping_def ty.simps(3) type_of.simps(2) val.collapse(2))+
  hence "0 , def , {} , 0, def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (def A))" and
        "0 , def , {} , 0, def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (def B))"
    by (auto intro!: beval_raw.intros)
  hence "0 , def , {} , 0, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b (Bv (\<not> (bval_of (def A) \<and> bval_of (def B))))" (is "_, _, _, _, _ \<turnstile> _ \<longrightarrow>\<^sub>b ?x")
    by (intro beval_raw.intros)
  hence "0, def, {}, 0, def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1, \<tau>> \<longrightarrow>\<^sub>s trans_post_raw C ?x (def C) \<tau> 0 1"
    by (simp add: b_seq_exec.intros(5))
  let ?\<tau>' = "trans_post_raw C ?x (def C) \<tau> 0 1"
  have "init' 0 def {} 0 def nand3 \<tau> ?\<tau>'"
    unfolding nand3_def
    by (meson \<open>0 , def , {} , 0 , def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 , \<tau>> \<longrightarrow>\<^sub>s
    trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1\<close> init'.intros(1))
  have "ttyping \<Gamma> ?\<tau>'"
    using trans_post_preserve_type_correctness[OF _ `ttyping \<Gamma> \<tau>`]
    by (simp add: assms(5))
  hence "styping \<Gamma> (next_state 0 ?\<tau>' def)"
    using next_state_preserve_styping[OF `styping \<Gamma> def`]  by blast
  have "ttyping \<Gamma> (add_to_beh def 0 0 (next_time 0 ?\<tau>'))"
    using add_to_beh_preserve_type_correctness[OF `styping \<Gamma> def` `ttyping \<Gamma> ?\<tau>'`]
    by (metis add_to_beh_preserve_type_correctness assms(4) bot_nat_def domIff ttyping_def
    zero_fun_def zero_map)
  have "ttyping \<Gamma> (?\<tau>'(next_time 0 ?\<tau>' := 0)) "
    using `ttyping \<Gamma> ?\<tau>'`  ttyping_rem_curr_trans by blast
  have "Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) \<noteq> def C \<or>
        Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) = def C"
    by auto
  moreover
  { assume "Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) = def C"
    hence "?\<tau>' =  preempt_raw C \<tau> 1"
      unfolding trans_post_raw_def
      by (metis True add.left_neutral cancel_comm_monoid_add_class.diff_cancel signal_of_zero
      zero_fun_def)
    also have "... = \<tau>"
    proof (rule, rule)
      fix time sig
      have "sig = C \<or> sig \<noteq> C"
        by auto
      moreover
      { assume "sig = C"
        hence "preempt_raw C \<tau> 1 time C = None"
          unfolding preempt_raw_def using True
          by (metis (full_types) assms(2) fun_upd_idem_iff to_trans_raw_sig_def zero_fun_def zero_option_def)
        also have "... = \<tau> time C"
          using assms(2) unfolding to_trans_raw_sig_def  by (metis zero_map)
        finally have "preempt_raw C \<tau> 1 time sig = \<tau> time sig"
          using `sig = C` by auto }
      moreover
      { assume "sig \<noteq> C"
        hence "preempt_raw C \<tau> 1 time sig = \<tau> time sig"
          unfolding preempt_raw_def by auto }
      ultimately show "preempt_raw C \<tau> 1 time sig = \<tau> time sig"
        by auto
    qed
    finally have "?\<tau>' = \<tau>"
      by auto
    hence bigstep: "(Suc i),
           next_time 0 \<tau> ,
           next_state 0 \<tau> def ,
           next_event 0 \<tau> def ,
           add_to_beh def 0 0 (next_time 0 \<tau>), def
        \<turnstile> <nand3 , \<tau>(next_time 0 \<tau> := 0)> \<leadsto> res"
      using bsimulate_obt_big_step[OF assms(1) `init' 0 def {} 0 def nand3 \<tau> ?\<tau>'`] `?\<tau>' = \<tau>` by auto
    have s1: "\<And>n. n \<le> next_time 0 \<tau> \<Longrightarrow> (\<tau>(next_time 0 \<tau> := 0)) n = 0"
      by (simp add: nat_less_le next_time_at_least2)
    have s2: "\<And>s. s \<in> dom ((\<tau>(next_time 0 \<tau> := 0)) (next_time 0 \<tau>)) \<Longrightarrow>
                              next_state 0 \<tau> def s = the ((\<tau>(next_time 0 \<tau> := 0)) (next_time 0 \<tau>) s)"
      by (simp add: zero_fun_def zero_option_def)
    have s3: "\<And>n. next_time 0 \<tau> \<le> n \<Longrightarrow> add_to_beh def 0 0 (next_time 0 \<tau>) n = 0"
      by (simp add: add_to_beh_def zero_fun_def)
    have s4: "A \<notin> next_event 0 \<tau> def \<and> B \<notin> next_event 0 \<tau> def \<Longrightarrow>
              bval_of (next_state 0 \<tau> def C) = (\<not> (bval_of (next_state 0 \<tau> def A) \<and> bval_of (next_state 0 \<tau> def B)))"
      by (smt One_nat_def Suc_le_mono True \<open>Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) = def C\<close>
      \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 = \<tau>\<close>
      \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 = preempt_raw C \<tau>
      1\<close> add_diff_cancel_left' domIff fun_upd_same le0 le_Suc_eq next_state_def
      next_state_fixed_point override_on_def plus_1_eq_Suc preempt_raw_def val.sel(1) zero_fun_def
      zero_option_def)
    have s5: "\<And>n. next_time 0 \<tau> < n \<Longrightarrow> to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0)) C n = 0"
      by (metis assms(2) fun_upd_apply to_trans_raw_sig_def zero_fun_def)
    have "styping \<Gamma> (next_state 0 \<tau> def)"
      using \<open>styping \<Gamma> (next_state 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B))))
      (def C) \<tau> 0 1) def)\<close> \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau>
      0 1 = \<tau>\<close> by auto
    have "ttyping \<Gamma> (add_to_beh def 0 0 (next_time 0 \<tau>))"
      using \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 = \<tau>\<close>
      \<open>ttyping \<Gamma> (add_to_beh def 0 0 (next_time 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and>
      bval_of (def B)))) (def C) \<tau> 0 1)))\<close> by auto
    have "ttyping \<Gamma> (\<tau>(next_time 0 \<tau> := 0))"
      using \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 = \<tau>\<close>
      \<open>ttyping \<Gamma> ((trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1)
      (next_time 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1) :=
      0))\<close> by auto
    hence * : "next_time 0 \<tau> \<le> i \<Longrightarrow>
               bval_of (get_state res C)  =
           (\<not> (bval_of (signal_of (next_state 0 \<tau> def A) (\<tau>(next_time 0 \<tau> := 0)) A i) \<and>
               bval_of (signal_of (next_state 0 \<tau> def B) (\<tau>(next_time 0 \<tau> := 0)) B i)))"
      using nand3_correctness_ind[OF bigstep _ _ s1 s2 s3 _ s4 s5 `conc_wt \<Gamma> nand3` `styping \<Gamma> (next_state 0 \<tau> def)`
       `ttyping \<Gamma> (add_to_beh def 0 0 (next_time 0 \<tau>))` `ttyping \<Gamma> (\<tau>(next_time 0 \<tau> := 0))` `\<Gamma> C = Bty` `styping \<Gamma> def`]
      by metis
    moreover have "next_time 0 \<tau> \<le> i \<Longrightarrow> signal_of (next_state 0 \<tau> def A) (\<tau>(next_time 0 \<tau> := 0)) A i = signal_of (def A) \<tau> A i"
    proof (cases "inf_time (to_trans_raw_sig \<tau>) A i = None")
      assume "next_time 0 \<tau> \<le> i"
      case True
      hence "signal_of (def A) \<tau> A i = def A"
        by (metis inf_time_noneE2 signal_of_def to_trans_raw_sig_def)
      have "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) A i= None"
        using True  by (metis inf_time_rem_curr_trans option.simps(3) rem_curr_trans_to_trans_raw_sig)
      hence "signal_of (next_state 0 \<tau> def A) (\<tau>(next_time 0 \<tau>:= 0)) A i = next_state 0 \<tau> def A"
        by (metis inf_time_noneE2 signal_of_def to_trans_raw_sig_def)
      have "\<tau> (next_time 0 \<tau>) A = None"
        using True `next_time 0 \<tau> \<le> i`
        by (metis inf_time_noneE2 to_trans_raw_sig_def zero_option_def)
      hence "next_state 0 \<tau> def A = def A"
        unfolding next_state_def Let_def
        by (simp add: domIff)
      thus ?thesis
        using \<open>signal_of (def A) \<tau> A i = def A\<close> \<open>signal_of (next_state 0 \<tau> def A) (\<tau>(next_time 0 \<tau>
        := 0)) A i = next_state 0 \<tau> def A\<close> by auto
    next
      assume "next_time 0 \<tau> \<le> i"
      case False
      then obtain ta where infA: "inf_time (to_trans_raw_sig \<tau>) A i = Some ta"
        by auto
      hence "\<tau> ta A \<noteq> None"
        by (metis Femto_VHDL_raw.keys_def domIff dom_def inf_time_some_exists to_trans_raw_sig_def
        zero_option_def)
      hence "next_time 0 \<tau> \<le> ta"
        by (metis next_time_at_least2 not_le zero_map)
      have "signal_of (def A) \<tau> A i = the (\<tau> ta A)"
        using infA unfolding to_signal_def comp_def to_trans_raw_sig_def by auto
      have "next_time 0 \<tau> = ta \<or> next_time 0 \<tau> < ta"
        using `next_time 0 \<tau> \<le> ta` by auto
      moreover
      { assume "next_time 0 \<tau> = ta"
        hence "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) A i = None"
          using infA
          by (metis inf_time_rem_curr_trans_at_t next_time_at_least2 rem_curr_trans_to_trans_raw_sig
          to_trans_raw_sig_def zero_fun_def zero_option_def)
        hence "signal_of (next_state 0 \<tau> def A) (\<tau>(next_time 0 \<tau> := 0)) A i = next_state 0 \<tau> def A"
          unfolding to_signal_def comp_def by auto
        also have "... = the (\<tau> ta A)"
          unfolding next_state_def Let_def comp_def `next_time 0 \<tau> = ta`
          by (simp add: \<open>\<tau> ta A \<noteq> None\<close> domIff)
        also have "... = signal_of (def A) \<tau> A i"
          using \<open>signal_of (def A) \<tau> A i = the (\<tau> ta A)\<close> by auto
        finally have ?thesis
          by auto }
      moreover
      { assume "next_time 0 \<tau> < ta"
        hence "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) A i = Some ta"
          using infA
          by (metis inf_time_rem_curr_trans nat_less_le option.inject rem_curr_trans_to_trans_raw_sig)
        hence ?thesis
          by (metis \<open>signal_of (def A) \<tau> A i = the (\<tau> ta A)\<close> calculation(2) fun_upd_apply o_def
          option.case(2) to_signal_def to_trans_raw_sig_def) }
      ultimately show ?thesis
        by auto
    qed
    moreover have "next_time 0 \<tau> \<le> i \<Longrightarrow> signal_of (next_state 0 \<tau> def B) (\<tau>(next_time 0 \<tau> := 0)) B i = signal_of (def B) \<tau> B i"
    proof (cases "inf_time (to_trans_raw_sig \<tau>) B i = None")
      assume "next_time 0 \<tau> \<le> i"
      case True
      hence "signal_of (def B) \<tau> B i = def B"
        by (metis inf_time_noneE2 signal_of_def to_trans_raw_sig_def)
      have "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) B i= None"
        using True  by (metis inf_time_rem_curr_trans option.simps(3) rem_curr_trans_to_trans_raw_sig)
      hence "signal_of (next_state 0 \<tau> def B) (\<tau>(next_time 0 \<tau>:= 0)) B i = next_state 0 \<tau> def B"
        by (metis inf_time_noneE2 signal_of_def to_trans_raw_sig_def)
      have "\<tau> (next_time 0 \<tau>) B = None"
        using True `next_time 0 \<tau> \<le> i`
        by (metis inf_time_noneE2 to_trans_raw_sig_def zero_option_def)
      hence "next_state 0 \<tau> def B = def B"
        unfolding next_state_def Let_def
        by (simp add: domIff)
      thus ?thesis
        using \<open>signal_of (def B) \<tau> B i = def B\<close> \<open>signal_of (next_state 0 \<tau> def B) (\<tau>(next_time 0 \<tau>
        := 0)) B i = next_state 0 \<tau> def B\<close> by auto
    next
      assume "next_time 0 \<tau> \<le> i"
      case False
      then obtain ta where infB: "inf_time (to_trans_raw_sig \<tau>) B i = Some ta"
        by auto
      hence "\<tau> ta B \<noteq> None"
        by (metis Femto_VHDL_raw.keys_def domIff dom_def inf_time_some_exists to_trans_raw_sig_def
        zero_option_def)
      hence "next_time 0 \<tau> \<le> ta"
        by (metis next_time_at_least2 not_le zero_map)
      have "signal_of (def B) \<tau> B i = the (\<tau> ta B)"
        using infB unfolding to_signal_def comp_def to_trans_raw_sig_def by auto
      have "next_time 0 \<tau> = ta \<or> next_time 0 \<tau> < ta"
        using `next_time 0 \<tau> \<le> ta` by auto
      moreover
      { assume "next_time 0 \<tau> = ta"
        hence "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) B i = None"
          using infB
          by (metis inf_time_rem_curr_trans_at_t next_time_at_least2 rem_curr_trans_to_trans_raw_sig
          to_trans_raw_sig_def zero_fun_def zero_option_def)
        hence "signal_of (next_state 0 \<tau> def B) (\<tau>(next_time 0 \<tau> := 0)) B i = next_state 0 \<tau> def B"
          unfolding to_signal_def comp_def by auto
        also have "... = the (\<tau> ta B)"
          unfolding next_state_def Let_def comp_def `next_time 0 \<tau> = ta`
          by (simp add: \<open>\<tau> ta B \<noteq> None\<close> domIff)
        also have "... = signal_of (def B) \<tau> B i"
          using \<open>signal_of (def B) \<tau> B i = the (\<tau> ta B)\<close> by auto
        finally have ?thesis
          by auto }
      moreover
      { assume "next_time 0 \<tau> < ta"
        hence "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) B i = Some ta"
          using infB
          by (metis inf_time_rem_curr_trans nat_less_le option.inject rem_curr_trans_to_trans_raw_sig)
        hence ?thesis
          by (metis \<open>signal_of (def B) \<tau> B i = the (\<tau> ta B)\<close> calculation(2) fun_upd_apply o_def
          option.case(2) to_signal_def to_trans_raw_sig_def) }
      ultimately show ?thesis
        by auto
    qed
    ultimately have IR: "next_time 0 \<tau> \<le> i \<Longrightarrow>  bval_of (get_state res C) =
           (\<not> (bval_of (signal_of (def A) \<tau> A i) \<and>  bval_of (signal_of (def B) \<tau> B i)))"
      by auto
    { assume "i < next_time 0 \<tau>"
      hence "signal_of (def A) \<tau> A i = def A" and "signal_of (def B) \<tau> B i = def B"
        by (metis dual_order.strict_trans2 next_time_at_least2 signal_of_def zero_fun_def)+
      have "\<And>n. n < next_time 0 \<tau> \<Longrightarrow> get_beh res n = ((add_to_beh def 0 0 (next_time 0 \<tau>))(next_time 0 \<tau> := Some \<circ> next_state 0 \<tau> def)) n"
      proof -
        fix n :: nat
        assume a1: "n < next_time 0 \<tau>"
        then have f2: "\<forall>f fa. f(0 := Some \<circ> (fa::sig \<Rightarrow> val)) = add_to_beh fa f 0 (next_time 0 \<tau>)"
          by (simp add: add_to_beh_def)
        then have f3: "Suc i, next_time 0 \<tau> , next_state 0 \<tau> def , {s. def s \<noteq> next_state 0 \<tau> def s} , 0 (0 := Some \<circ> def), def \<turnstile> <nand3 , \<tau> (next_time 0 \<tau> := 0)> \<leadsto> res"
          by (metis bigstep next_event_alt_def)
        then have "next_time 0 \<tau> < Suc i \<or> next_time 0 \<tau> = Suc i"
          using bau by blast
        then show "get_beh res n = ((add_to_beh def 0 0 (next_time 0 \<tau>)) (next_time 0 \<tau> := Some \<circ> next_state 0 \<tau> def)) n"
          using f3 f2 a1 \<open>i < next_time 0 \<tau>\<close> maxtime_maxtime_bigstep by auto
      qed
      have "0 < next_time 0 \<tau>"
        using `i < next_time 0 \<tau>` by auto
      have "Suc i < next_time 0 \<tau> \<or> Suc i = next_time 0 \<tau>"
        using `i < next_time 0 \<tau>` by auto
      moreover
      { assume "Suc i < next_time 0 \<tau>"
        have "False"
        proof -
          have "\<not> next_time 0 \<tau> < Suc i"
            by (simp add: \<open>Suc i < next_time 0 \<tau>\<close> leD le_less)
          then have "next_time 0 \<tau> = Suc i"
            using bau bigstep by blast
          then show ?thesis
            using \<open>Suc i < next_time 0 \<tau>\<close> by linarith
        qed }
      ultimately have "Suc i = next_time 0 \<tau>"
        by auto
      hence bigstep': "Suc i, Suc i , next_state 0 \<tau> def , next_event 0 \<tau> def , add_to_beh def 0 0 (next_time 0 \<tau>), def \<turnstile> <nand3 , \<tau>(next_time 0 \<tau> := 0)> \<leadsto> res"
        using bigstep by auto
      have "get_beh res = (add_to_beh def 0 0 (next_time 0 \<tau>))"
        using maxtime_maxtime_bigstep[OF bigstep'] by auto
      have "get_state res = next_state 0 \<tau> def"
      proof -
        have "(Suc i, next_state 0 \<tau> def, add_to_beh def 0 0 (next_time 0 \<tau>), \<tau>(next_time 0 \<tau> := 0)) = res"
          using bau bigstep' by blast
        then show ?thesis
          by force
      qed
      hence " bval_of (get_state res C)  =
         (\<not> (bval_of (signal_of (def A) \<tau> A i) \<and>  bval_of (signal_of (def B) \<tau> B i)))"
        by (metis One_nat_def Suc_leI \<open>0 < next_time 0 \<tau>\<close> \<open>Bv (\<not> (bval_of (def A) \<and> bval_of (def
        B))) = def C\<close> \<open>signal_of (def A) \<tau> A i = def A\<close> \<open>signal_of (def B) \<tau> B i = def B\<close>
        \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 = \<tau>\<close>
        \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 = preempt_raw
        C \<tau> 1\<close> domIff fun_upd_same next_state_def override_on_apply_notin preempt_raw_def
        val.sel(1)) }
    hence ?thesis
      using IR  le_less_linear by blast }
  moreover
  { assume "Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) \<noteq> def C"
    hence ntime: "next_time 0 ?\<tau>' = 1"
    proof -
      have "?\<tau>' \<noteq> 0"
      proof (intro trans_post_raw_imply_neq_map_empty[where sig="C" and def="def C" and \<tau>="\<tau>" and t="0" and dly="1"])
        show "trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 = trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1"
          by auto
      next
        show "\<forall>i\<le>0 + (1 - 1). \<tau> i C = None \<Longrightarrow> Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) \<noteq> def C"
          using True `Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) \<noteq> def C`
          by auto
      qed (auto)
      hence "next_time 0 ?\<tau>' = (LEAST n. dom ( ?\<tau>' n) \<noteq> {})"
        unfolding next_time_def by auto
      also have "... = 1"
      proof (rule Least_equality)
        show "dom ( ?\<tau>' 1) \<noteq> {}"
          using True `Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) \<noteq> def C`
          by (smt add.commute add.right_neutral cancel_comm_monoid_add_class.diff_cancel
          dom_eq_empty_conv fun_upd_same option.simps(3) post_raw_def signal_of_zero
          trans_post_raw_def zero_fun_def)
      next
        { fix y :: nat
          assume "y < 1"
          hence "dom ( ?\<tau>' y) = {}"
            using True by (metis dom_eq_empty_conv le_zero_eq less_one
            trans_post_preserve_trans_removal_nonstrict zero_fun_def zero_option_def) }
        thus "\<And>y. dom (?\<tau>' y) \<noteq> {} \<Longrightarrow> 1 \<le> y"
          using le_less_linear by auto
      qed
      finally show "next_time 0 ?\<tau>' = 1"
        by auto
    qed
    have ind1: "\<And>n. n < next_time 0 ?\<tau>' \<Longrightarrow>  ?\<tau>' n = 0"
      using True unfolding `next_time 0 ?\<tau>' = 1`
      by (auto simp add: trans_post_raw_def preempt_raw_def post_raw_def)
    hence ind1': "\<And>n. n \<le> next_time 0 ?\<tau>' \<Longrightarrow>  (?\<tau>'(next_time 0 ?\<tau>' := 0)) n = 0"
      by simp
    have ind2: "\<And>s. s \<in> dom ( ?\<tau>' (next_time 0 ?\<tau>')) \<Longrightarrow>
                          next_state 0 ?\<tau>' def s = the ( ?\<tau>' (next_time 0 ?\<tau>') s)"
      unfolding next_state_def `next_time 0 ?\<tau>' = 1` Let_def by auto
    have ind2': "\<And>s. s \<in> dom ( (?\<tau>'(next_time 0 ?\<tau>' := 0)) (next_time 0 ?\<tau>')) \<Longrightarrow>
                          next_state 0 ?\<tau>' def s = the ( (?\<tau>'(next_time 0 ?\<tau>' := 0)) (next_time 0 ?\<tau>') s)"
      by (simp add: zero_fun_def zero_option_def)
    have ind3: "\<And>n. next_time 0 ?\<tau>' \<le> n \<Longrightarrow>  (add_to_beh def 0 0 (next_time 0 ?\<tau>')) n = 0"
      unfolding ntime add_to_beh_def by (auto simp add: zero_map zero_option_def zero_fun_def)
    have Cin: "C \<in> dom ( ?\<tau>' (next_time 0 ?\<tau>'))"
      using True unfolding `next_time 0 ?\<tau>' = 1`  `Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) \<noteq> def C`
      by (metis (no_types, lifting) \<open>Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) \<noteq> def C\<close> add.commute
      add_cancel_right_right add_diff_cancel_left' domIff fun_upd_same option.simps(3) post_raw_def
      signal_of_zero trans_post_raw_def zero_fun_def)
    { assume "A \<notin> next_event 0 ?\<tau>' def \<and> B \<notin> next_event 0 ?\<tau>' def"
      hence "A \<notin> dom ( ?\<tau>' (next_time 0 ?\<tau>')) \<or> the ( ?\<tau>' (next_time 0 ?\<tau>') A) = (def A)"
        and "B \<notin> dom ( ?\<tau>' (next_time 0 ?\<tau>')) \<or> the ( ?\<tau>' (next_time 0 ?\<tau>') B) = (def B)"
        unfolding next_event_def ntime Let_def by auto
      moreover have "next_state 0 ?\<tau>' def C = Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))"
        using Cin unfolding next_state_def ntime Let_def
        by (auto simp add: trans_post_raw_def preempt_raw_def post_raw_def)
      ultimately have "bval_of (next_state 0 ?\<tau>' def C) \<longleftrightarrow>
                                       \<not> (bval_of (next_state 0 ?\<tau>' def A) \<and> bval_of (next_state 0 ?\<tau>' def B))"
        by (metis \<open>A \<notin> next_event 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B))))
        (def C) \<tau> 0 1) def \<and> B \<notin> next_event 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def
        B)))) (def C) \<tau> 0 1) def\<close> next_state_fixed_point val.sel(1)) }
    note ind4 = this
    have ind5: "\<And>n. next_time 0 ?\<tau>' < n \<Longrightarrow>  (to_trans_raw_sig ?\<tau>' C) n = 0"
      unfolding ntime by (auto simp add: trans_post_raw_def to_trans_raw_sig_def zero_option_def
      preempt_raw_def post_raw_def)
    have ind5': "\<And>n. next_time 0 ?\<tau>' < n \<Longrightarrow>  (to_trans_raw_sig (?\<tau>'(next_time 0 ?\<tau>' := 0)) C) n = 0"
      by (metis ind5 less_numeral_extra(4) ntime rem_curr_trans_to_trans_raw_sig
      trans_value_same_except_at_removed)
    hence bigstep: "(Suc i),
           next_time 0 ?\<tau>' ,
           next_state 0 ?\<tau>' def ,
           next_event 0 ?\<tau>' def ,
           add_to_beh def 0 0 (next_time 0 ?\<tau>'), def
        \<turnstile> <nand3 , ?\<tau>'(next_time 0 ?\<tau>' := 0)> \<leadsto> res"
      using bsimulate_obt_big_step[OF assms(1) `init' 0 def {} 0 def nand3 \<tau> ?\<tau>'`] by auto
    have *: "1 \<le> i \<Longrightarrow>
       bval_of (get_state res C) \<longleftrightarrow>
    \<not> (bval_of (signal_of (next_state 0 ?\<tau>' def A) (?\<tau>'(1:=0)) A i) \<and>
       bval_of (signal_of (next_state 0 ?\<tau>' def B) (?\<tau>'(1:=0)) B i))"
      using nand3_correctness_ind[OF bigstep _ _ ind1' ind2' ind3 _ ind4 ind5' `conc_wt \<Gamma> nand3` `styping \<Gamma> (next_state 0 ?\<tau>' def)`
      `ttyping \<Gamma> (add_to_beh def 0 0 (next_time 0 ?\<tau>'))` `ttyping \<Gamma> (?\<tau>'(next_time 0 ?\<tau>' := 0))` `\<Gamma> C = Bty` `styping \<Gamma> def`]
      unfolding ntime by auto
    moreover have "1 \<le> i \<Longrightarrow> signal_of (next_state 0 ?\<tau>' def A) ?\<tau>' A i = signal_of (def A) ?\<tau>' A i"
    proof (cases "inf_time (to_trans_raw_sig ?\<tau>') A i = None")
      case True
      assume "1 \<le> i"
      have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig ?\<tau>' A) k = 0"
        using True by (auto dest!: inf_time_noneE2)
      hence " (to_trans_raw_sig ?\<tau>' A) 1 = 0"
        using `1 \<le> i` by auto
      hence "A \<notin> dom ( ?\<tau>' 1)"
         unfolding trans_post_raw_def to_trans_raw_sig_def
        by (simp add: domIff zero_option_def)
      have "signal_of (next_state 0 ?\<tau>' def A) ?\<tau>' A i = next_state 0 ?\<tau>' def A"
        using True unfolding to_signal_def comp_def by auto
      also have "... = def A"
        using `A \<notin> dom ( ?\<tau>' 1)` unfolding next_state_def ntime Let_def by auto
      finally have 0: "signal_of (next_state 0 ?\<tau>' def A) ?\<tau>' A i = def A"
        by auto
      have 1: "signal_of (def A) ?\<tau>' A i = def A"
        using True unfolding to_signal_def comp_def by auto
      then show ?thesis
        using 0 1 by auto
    next
      case False
      then obtain ta where "inf_time (to_trans_raw_sig ?\<tau>') A i = Some ta"
        by auto
      then show ?thesis
        unfolding to_signal_def comp_def by auto
    qed
    moreover have "signal_of (next_state 0 ?\<tau>' def A) ?\<tau>' A i =   signal_of (next_state 0 ?\<tau>' def A) (?\<tau>'(1 := 0)) A i"
      apply (intro sym[OF signal_of_rem_curr_trans_at_t[where \<tau>="?\<tau>'" and \<sigma>="next_state 0 ?\<tau>' def"]])
      using ind1 ind2 unfolding ntime by auto
    moreover have "1 \<le> i \<Longrightarrow> signal_of (next_state 0 ?\<tau>' def B) ?\<tau>' B i = signal_of (def B) ?\<tau>' B i"
    proof (cases "inf_time (to_trans_raw_sig ?\<tau>') B i = None")
      case True
      assume "1 \<le> i"
      have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig ?\<tau>' B) k = 0"
        using True by (auto dest!: inf_time_noneE2)
      hence " (to_trans_raw_sig ?\<tau>' B) 1 = 0"
        using `1 \<le> i` by auto
      hence "B \<notin> dom ( ?\<tau>' 1)"
         unfolding trans_post_raw_def to_trans_raw_sig_def by (simp add: domIff zero_option_def)
      have "signal_of (next_state 0 ?\<tau>' def B) ?\<tau>' B i = next_state 0 ?\<tau>' def B"
        using True unfolding to_signal_def comp_def by auto
      also have "... = def B"
        using `B \<notin> dom ( ?\<tau>' 1)` unfolding next_state_def ntime Let_def by auto
      finally have 0: "signal_of (next_state 0 ?\<tau>' def B) ?\<tau>' B i = def B"
        by auto
      have 1: "signal_of (def B) ?\<tau>' B i = def B"
        using True unfolding to_signal_def comp_def by auto
      then show ?thesis
        using 0 1 by auto
    next
      case False
      then obtain ta where "inf_time (to_trans_raw_sig ?\<tau>') B i = Some ta"
        by auto
      then show ?thesis
        unfolding to_signal_def comp_def by auto
    qed
    moreover have "signal_of (next_state 0 ?\<tau>' def B) ?\<tau>' B i = signal_of (next_state 0 ?\<tau>' def B) (?\<tau>'(1:=0)) B i"
      apply(intro sym[OF signal_of_rem_curr_trans_at_t[where \<sigma>="next_state 0 ?\<tau>' def"]])
      using ind1 ntime ind2 by auto
    ultimately have IR: "1 \<le> i \<Longrightarrow> bval_of (get_state res C) \<longleftrightarrow>
                                              \<not> (bval_of (signal_of (def A) ?\<tau>' A i) \<and> bval_of (signal_of (def B) ?\<tau>' B i))"
      by auto
    have " ?\<tau>' 0 = 0"
      using True by (simp add: trans_post_raw_def post_raw_def preempt_raw_def)
    have "signal_of (def A) ?\<tau>' A 0 = def A"
      by (metis \<open>?\<tau>' 0 = 0\<close> signal_of_zero zero_fun_def)
    have "signal_of (def B) ?\<tau>' B 0 = def B"
      by (metis \<open>?\<tau>' 0 = 0\<close> signal_of_zero zero_fun_def)
    have "1 \<le> next_time 0 ?\<tau>'"
      unfolding ntime by auto
    have "next_time 0 ?\<tau>' \<le> Suc i"
      unfolding ntime by auto
    hence "next_time 0 ?\<tau>' < Suc i \<or> next_time 0 ?\<tau>' = Suc i"
      by auto
    moreover
    { assume "next_time 0 ?\<tau>' < Suc i"
      have " get_beh res 1 = ((add_to_beh def 0 0 (next_time 0 ?\<tau>')) (next_time 0 ?\<tau>' := Some \<circ> next_state 0 ?\<tau>' def)) 1"
        using beh_res2[OF bigstep ind1' `next_time 0 ?\<tau>' < Suc i` _ ind3 `1 \<le> next_time 0 ?\<tau>'`]
        by auto
      also have "... =  ((add_to_beh def 0 0 1)(1 := (Some o next_state 0 ?\<tau>' def))) 1"
        unfolding ntime by auto
      also have "... = Some o next_state 0 ?\<tau>' def"
        by simp
      finally have " get_beh res 1  = Some o next_state 0 ?\<tau>' def"
        by auto
      hence "signal_of (def C) (get_beh res) C 1 = next_state 0 ?\<tau>' def C"
        by (meson trans_some_signal_of)
      also have "... = Bv (\<not> (bval_of (signal_of (def A) ?\<tau>' A 0) \<and> bval_of (signal_of (def B) ?\<tau>' B 0)))"
        unfolding `signal_of (def A) ?\<tau>' A 0 = def A` `signal_of (def B) ?\<tau>' B 0 = def B`
        by (smt Cin Suc_eq_plus1 True \<open>Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) \<noteq> def C\<close>
        add.right_neutral add_diff_cancel_left' fun_upd_same next_state_def ntime o_apply option.sel
        override_on_def plus_1_eq_Suc post_raw_def signal_of_zero trans_post_raw_def zero_fun_def)
      finally have IR0: "bval_of (signal_of (def C) (get_beh res) C 1) \<longleftrightarrow> \<not> (bval_of (signal_of (def A) ?\<tau>' A 0) \<and> bval_of (signal_of (def B) ?\<tau>' B 0))"
        by auto
      have "signal_of (def A) ?\<tau>' A i = signal_of (def A) \<tau> A i" and "signal_of (def B) ?\<tau>' B i = signal_of (def B) \<tau> B i"
        using signal_of_trans_post   by (metis sig.distinct(3))(meson sig.simps(6) signal_of_trans_post)
      hence ?thesis
        using IR IR0  using le_less_linear
        using \<open>next_time 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau>
        0 1) < Suc i\<close> ntime by auto }
    moreover
    { assume "next_time 0 ?\<tau>' = Suc i"
      hence bigstep': "Suc i, Suc i, next_state 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1)
                    def , next_event 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1)
                           def , add_to_beh def 0 0
                                  (next_time 0
                                    (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0
                                      1)), def \<turnstile> <nand3 , (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1)
        (next_time 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1) := 0)> \<leadsto> res"
        using bigstep by auto
      have "get_state res = next_state 0 ?\<tau>' def"
        by (rule bau[OF bigstep']) auto
      hence ?thesis
        by (smt Cin Suc_eq_plus1 True \<open>Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) \<noteq> def C\<close>
        \<open>next_time 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1) =
        Suc i\<close> \<open>styping \<Gamma> (next_state 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def
        B)))) (def C) \<tau> 0 1) def)\<close> add_cancel_right_right add_diff_cancel_left' assms(5) comp_apply
        fun_upd_same next_state_def ntime option.sel override_on_def plus_1_eq_Suc post_raw_def
        signal_of_zero styping_def trans_post_raw_def ty.distinct(1) type_of.simps(2)
        val.exhaust_sel val.inject(1) zero_fun_def) }
    ultimately have ?thesis
      by auto }
  ultimately show ?thesis
    by auto
next
  case False
  have "seq_wt \<Gamma> (get_seq nand3)"
    using `conc_wt \<Gamma> nand3`
    by (metis conc_stmt.distinct(1) conc_stmt.sel(4) conc_wt.cases nand3_def)
  hence "bexp_wt \<Gamma> (Bnand (Bsig A) (Bsig B)) (\<Gamma> C)"
    using seq_wt_cases(4)  by (metis conc_stmt.sel(4) nand3_def)
  hence "\<Gamma> A = Bty" and "\<Gamma> B = Bty"
    using bexp_wt_cases  by (smt assms(5) bexp.distinct bexp.inject(1) bexp_wt.cases)+
  hence "is_Bv (def A)" and "is_Bv (def B)"
    by (metis assms(4) styping_def ty.simps(3) type_of.simps(2) val.collapse(2))+
  hence "0 , def , {} , 0, def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (def A))" and
        "0 , def , {} , 0, def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (def B))"
    by (auto intro!: beval_raw.intros)
  hence "0 , def , {} , 0, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b (Bv (\<not> (bval_of (def A) \<and> bval_of (def B))))" (is "_, _, _, _, _ \<turnstile> _ \<longrightarrow>\<^sub>b ?x")
    by (intro beval_raw.intros)  
  hence "0, def, {}, 0, def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1, \<tau>> \<longrightarrow>\<^sub>s trans_post_raw C ?x (def C) \<tau> 0 1"
    by (simp add: b_seq_exec.intros(5))
  let ?\<tau>' = "trans_post_raw C ?x (def C) \<tau> 0 1"
  have "init' 0 def {} 0 def nand3 \<tau> ?\<tau>'"
    unfolding nand3_def
    by (meson \<open>0 , def , {} , 0 , def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 , \<tau>> \<longrightarrow>\<^sub>s
    trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1\<close> init'.intros(1))
  have "Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) \<noteq> def C \<or>
        Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) = def C"
    by auto
  moreover
  { assume "Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) \<noteq> def C"
    hence "post_necessary_raw 0 \<tau> 0 C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C)"
      by (metis add.left_neutral assms(2) signal_of_zero to_trans_raw_sig_def zero_fun_def)
    hence " ?\<tau>' 1 C = Some ?x"
      unfolding trans_post_raw_def
      by (auto simp add: trans_post_raw_def post_raw_def)
    hence ntime: "next_time 0 ?\<tau>' = 0"
    proof -
      have "?\<tau>' \<noteq> 0"
        by (metis \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 1 C =
        Some (Bv (\<not> (bval_of (def A) \<and> bval_of (def B))))\<close> option.simps(3) zero_fun_def
        zero_option_def)
      hence "next_time 0 ?\<tau>' = (LEAST n. dom ( ?\<tau>' n) \<noteq> {})"
        unfolding next_time_def by auto
      also have "... = 0"
      proof (rule Least_equality)
        show "dom (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 0) \<noteq> {}"
          using False by (auto simp add: trans_post_raw_def zero_fun_def zero_option_def
          preempt_raw_def post_raw_def)
      next
        { fix y :: nat
          assume "y < 0"
          hence "False" by auto
          hence "dom (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 0) = {}"
            by auto }
        thus "\<And>y. dom (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 y) \<noteq> {} \<Longrightarrow> 0 \<le> y "
          using le_less_linear by auto
      qed
      finally show "next_time 0 ?\<tau>' = 0"
        by auto
    qed
    have "?\<tau>' = post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> 1"
      using \<open>post_necessary_raw 0 \<tau> 0 C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C)\<close>
      unfolding trans_post_raw_def by auto
    define t' where "t' = next_time 0 ?\<tau>'"
    hence t'_def': "t' = 0"
      using ntime by auto

    define \<sigma>' where "\<sigma>' = next_state 0 ?\<tau>' def"
    hence "\<sigma>' C = def C"
      using assms(2)  unfolding next_state_def `next_time 0 ?\<tau>' = 0`
      unfolding to_trans_raw_sig_def Let_def trans_post_raw_def preempt_raw_def post_raw_def
      by (smt One_nat_def add.right_neutral discrete domIff next_time_def not_add_less2
      override_on_def plus_1_eq_Suc t'_def t'_def' zero_fun_def zero_less_one zero_option_def)      
    have "styping \<Gamma> \<sigma>'"
      using next_state_preserve_styping 
      by (simp add: next_state_preserve_styping \<sigma>'_def assms(4) assms(5) assms(6)
      trans_post_preserve_type_correctness)
    define \<gamma>' where "\<gamma>' = next_event 0 ?\<tau>' def"
    define \<theta>' where "\<theta>' = add_to_beh def (0 :: sig trans_raw) 0 t'"
    hence "\<theta>' = 0"
      unfolding t'_def' add_to_beh_def by auto
    hence bigstep: "(Suc i), t' , \<sigma>' , \<gamma>', \<theta>', def \<turnstile> <nand3 , (?\<tau>' (t':=0))> \<leadsto> res"
      using bsimulate_obt_big_step[OF assms(1) `init' 0 def {} 0 def nand3 \<tau> ?\<tau>'`]
      unfolding \<sigma>'_def \<gamma>'_def \<theta>'_def t'_def by auto
    hence bigstep': "(Suc i), 0 , \<sigma>' , \<gamma>', 0, def \<turnstile> <nand3 , (?\<tau>' (t':=0))> \<leadsto> res"
      unfolding t'_def' `\<theta>' = 0` by auto
    have "?\<tau>' (t':=0)\<noteq> 0"
      by (metis \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 1 C =
      Some (Bv (\<not> (bval_of (def A) \<and> bval_of (def B))))\<close> fun_upd_apply option.simps(3) t'_def'
      zero_fun_def zero_neq_one zero_option_def)
    hence "\<not> quiet (?\<tau>' (t':=0)) \<gamma>'"
      unfolding quiet_def by auto
    moreover have "0 < Suc i"
      by auto
    obtain \<tau>'' where cyc: "0 , \<sigma>' , \<gamma>' , 0, def \<turnstile> <nand3 , (?\<tau>' (t':=0))> \<longrightarrow>\<^sub>c \<tau>''" 
      apply (rule bau[OF bigstep'])
      using calculation by blast+ 
    have "next_time 0 \<tau>'' \<le> Suc i \<or> Suc i < next_time 0 \<tau>''"
      by auto
    moreover
    { assume "next_time 0 \<tau>'' \<le> Suc i"
      have bigstep'': "(Suc i), next_time 0 \<tau>'' , next_state 0 \<tau>'' \<sigma>' , next_event 0 \<tau>'' \<sigma>' , add_to_beh \<sigma>' 0 0 (next_time 0 \<tau>''), def \<turnstile>
                    <nand3 , \<tau>'' (next_time 0 \<tau>'' := 0) > \<leadsto> res"
        apply (rule bau[OF bigstep'])
        using `next_time 0 \<tau>'' \<le> Suc i` b_conc_exec_deterministic cyc apply blast
        using \<open>next_time 0 \<tau>'' \<le> Suc i\<close> bigstep' case_bau cyc less_or_eq_imp_le apply blast
        using calculation apply blast
        by blast
      define \<sigma>'' where "\<sigma>'' = next_state 0 \<tau>'' \<sigma>'"
      define \<gamma>'' where "\<gamma>'' = next_event 0 \<tau>'' \<sigma>'"
      define \<theta>'' where "\<theta>'' = add_to_beh \<sigma>' 0 0 (next_time 0 \<tau>'')"
      have bigstep3 : "(Suc i), next_time 0 \<tau>'' , \<sigma>'' , \<gamma>'' , \<theta>'', def \<turnstile> <nand3 , \<tau>''(next_time 0 \<tau>'' :=0)> \<leadsto> res"
        using bigstep'' unfolding \<sigma>''_def \<gamma>''_def \<theta>''_def by auto
      have ind1: "\<And>n. n < next_time 0 ?\<tau>' \<Longrightarrow>  ?\<tau>' n = 0"
        unfolding `next_time 0 ?\<tau>' = 0` by (auto simp add: trans_post_raw_def)
      have ind1': "\<And>n. n < next_time 0 \<tau>'' \<Longrightarrow>  \<tau>'' n = 0"
      proof (cases "\<tau>'' = 0")
        case True
        hence "next_time 0 \<tau>'' = 1"
          by auto
        then show "\<And>n. n < next_time 0 \<tau>'' \<Longrightarrow>  \<tau>'' n = 0"
          using Least_le  next_time_at_least2 by blast
      next
        case False
        hence "next_time 0 \<tau>'' = (LEAST n. dom ( \<tau>'' n) \<noteq> {})"
          unfolding next_time_def by auto
        then show "\<And>n. n < next_time 0 \<tau>'' \<Longrightarrow>  \<tau>'' n = 0"
          using Least_le  next_time_at_least2 by blast
      qed
      hence ind1'': "\<And>n. n \<le> next_time 0 \<tau>'' \<Longrightarrow>  (\<tau>''(next_time 0 \<tau>'' := 0)) n = 0"
        by simp
      have ind2: "\<And>s. s \<in> dom ( ?\<tau>' (next_time 0 ?\<tau>')) \<Longrightarrow>
                            next_state 0 ?\<tau>' def s = the ( ?\<tau>' (next_time 0 ?\<tau>') s)"
        unfolding next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
      have ind2': "\<And>s. s \<in> dom ( \<tau>'' (next_time 0 \<tau>'')) \<Longrightarrow>
                            \<sigma>'' s = the ( \<tau>'' (next_time 0 \<tau>'') s)"
        unfolding next_state_def Let_def \<sigma>''_def by auto
      have ind2'': "\<And>s. s \<in> dom ( (\<tau>''(next_time 0 \<tau>'' := 0)) (next_time 0 \<tau>'')) \<Longrightarrow> \<sigma>'' s = the ( (\<tau>''(next_time 0 \<tau>'' := 0)) (next_time 0 \<tau>'') s)"
        by (simp add: zero_fun_def zero_option_def)
      have ind3: "\<And>n. next_time 0 ?\<tau>' \<le> n \<Longrightarrow>  (add_to_beh def 0 0 (next_time 0 ?\<tau>')) n = 0"
        unfolding ntime add_to_beh_def by (auto simp add: zero_fun_def)
      have ind3': "\<And>n. next_time 0 \<tau>'' \<le> n \<Longrightarrow>  \<theta>'' n = 0"
        unfolding \<theta>''_def add_to_beh_def by  (auto simp add: zero_fun_def)
      consider (either) "A \<in> \<gamma>' \<or> B \<in> \<gamma>'" | (none) "A \<notin> \<gamma>' \<and> B \<notin> \<gamma>'"
        by auto
      hence ?thesis
      proof (cases)
        case either
        have "styping \<Gamma> (next_state 0 ?\<tau>' def)"
          by (intro next_state_preserve_styping) (auto simp add: assms(4-6) trans_post_preserve_type_correctness)
        hence "is_Bv (\<sigma>' A)" and "is_Bv (\<sigma>' B)"
          using `\<Gamma> A = Bty` `\<Gamma> B = Bty`
          by (metis \<sigma>'_def styping_def ty.distinct(1) type_of.simps(2) val.collapse(2))+
        hence "0 , \<sigma>' , \<gamma>' , 0, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b (Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B))))"
          by (metis beval_raw.intros(1) beval_raw.intros(12) val.collapse(1))
        hence "0 , \<sigma>' , \<gamma>' , 0 , def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1 , ?\<tau>'(t' := 0)> \<longrightarrow>\<^sub>s
                                       trans_post_raw C (Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))) (\<sigma>' C) (?\<tau>' (t':=0)) 0 1"
          by (simp add: b_seq_exec.intros(5))
        hence  "0 , \<sigma>' , \<gamma>' , 0 , def \<turnstile> <nand3 , ?\<tau>'(t' := 0)> \<longrightarrow>\<^sub>c  trans_post_raw C (Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))) (\<sigma>' C) (?\<tau>' (t':=0)) 0 1"
          unfolding nand3_def
          by (simp add: b_conc_exec.intros(2) either)
        hence \<tau>''_def: "\<tau>'' = trans_post_raw C (Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))) (\<sigma>' C) (?\<tau>' (0:=0)) 0 1"
          using cyc  by (simp add: b_conc_exec_deterministic t'_def')
        have "(bval_of (\<sigma>' C) \<longleftrightarrow> \<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B))) \<or>
              (\<not> bval_of (\<sigma>' C) \<longleftrightarrow> \<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))"
          by auto
        moreover
        { assume "\<not> bval_of (\<sigma>' C) \<longleftrightarrow> \<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B))"
          hence nec: "post_necessary_raw 0 (?\<tau>' (0:=0)) 0 C (Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))) (\<sigma>' C)"
            by (metis add.left_neutral fun_upd_same signal_of_zero val.sel(1) zero_fun_def)
          hence "\<tau>'' \<noteq> 0"
            by (metis \<tau>''_def add.left_neutral fun_upd_same signal_of_zero trans_post_raw_imply_neq_map_empty zero_fun_def zero_less_one)
          hence "next_time 0 \<tau>'' = (LEAST n. dom ( \<tau>'' n) \<noteq> {})"
            unfolding next_time_def by auto
          also have "... = 1"
          proof (rule Least_equality)
            show "dom ( \<tau>'' 1) \<noteq> {}"
              using nec  unfolding \<tau>''_def   unfolding trans_post_raw_def post_raw_def
              by (auto simp add: zero_fun_def zero_option_def )
          next
            { fix y :: nat
              assume "y < 1"
              hence "y = 0" by auto
              have "dom ( \<tau>'' y) = {}" unfolding `y = 0` \<tau>''_def
                unfolding trans_post_raw_def  post_raw_def preempt_raw_def
                by (simp add: dom_def zero_map) }
            thus "\<And>y. dom ( \<tau>'' y) \<noteq> {} \<Longrightarrow> 1 \<le> y "
              using le_less_linear by auto
          qed
          finally have "next_time 0 \<tau>'' = 1"
            by auto
          { assume "A \<notin> next_event 0 \<tau>'' \<sigma>' \<and> B \<notin> next_event 0 \<tau>'' \<sigma>'"
            hence "A \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') A) = \<sigma>' A"
              and "B \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') B) = \<sigma>' B"
              unfolding next_event_def ntime Let_def by auto
            hence helper: "\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)) \<longleftrightarrow>  \<not> (bval_of (next_state 0 \<tau>'' \<sigma>' A) \<and> bval_of (next_state 0 \<tau>'' \<sigma>' B))"
              unfolding next_state_def Let_def  by (simp add: override_on_def)
            have "next_state 0 \<tau>'' \<sigma>' C = (let m =  \<tau>'' (next_time 0 \<tau>'') in override_on \<sigma>' (the \<circ> m) (dom m)) C"
              unfolding next_state_def by auto
            also have "... = (let m =  \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
              unfolding `next_time 0 \<tau>'' = 1` by auto
            also have "... = Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))"
              unfolding \<tau>''_def   unfolding trans_post_raw_def preempt_raw_def Let_def post_raw_def
              by (smt add.left_neutral cancel_comm_monoid_add_class.diff_cancel comp_apply domIff
              fun_upd_same nec option.sel option.simps(3) override_on_def signal_of_zero zero_fun_def)
            finally have "next_state 0 \<tau>'' \<sigma>' C = Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))"
              by auto
            hence "next_state 0 \<tau>'' \<sigma>' C = Bv (\<not> (bval_of (next_state 0 \<tau>'' \<sigma>' A) \<and> bval_of (next_state 0 \<tau>'' \<sigma>' B)))"
              using helper by auto }
          hence  ind4': "A \<notin> \<gamma>'' \<and> B \<notin> \<gamma>'' \<Longrightarrow> bval_of (\<sigma>'' C) \<longleftrightarrow> (\<not> (bval_of (\<sigma>'' A) \<and> bval_of (\<sigma>'' B)))"
            unfolding \<gamma>''_def \<sigma>''_def by auto
          have "\<And>n. 1 < n \<Longrightarrow>  (to_trans_raw_sig \<tau>'' C) n = 0"
            unfolding \<tau>''_def   unfolding trans_post_raw_def to_trans_raw_sig_def post_raw_def
            preempt_raw_def by (simp add: zero_option_def )
          hence ind5': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig \<tau>'' C) n = 0"
            unfolding `next_time 0 \<tau>'' = 1` by auto
          hence ind5'': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig (\<tau>''(next_time 0 \<tau>'' := 0)) C) n = 0"
            by (simp add: to_trans_raw_sig_def)
          have "styping \<Gamma> \<sigma>''"
            unfolding \<sigma>''_def
            by (metis \<open>styping \<Gamma> (next_state 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def
            B)))) (def C) \<tau> 0 1) def)\<close> \<sigma>'_def \<tau>''_def assms(5) assms(6) next_state_preserve_styping
            trans_post_preserve_type_correctness ttyping_rem_curr_trans type_of.simps(1))
          have "ttyping \<Gamma> \<theta>''"
            unfolding \<theta>''_def
            by (metis \<open>styping \<Gamma> (next_state 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def
            B)))) (def C) \<tau> 0 1) def)\<close> \<sigma>'_def add_to_beh_preserve_type_correctness dom_eq_empty_conv
            empty_iff ttyping_def zero_fun_def zero_option_def)
          have "ttyping \<Gamma> (\<tau>''(next_time 0 \<tau>'' := 0))"
            by (simp add: \<tau>''_def assms(5) assms(6) trans_post_preserve_type_correctness
            ttyping_rem_curr_trans)
          have *: "1 \<le> i \<Longrightarrow>
             bval_of (get_state res C) =
         (\<not> (bval_of (signal_of (\<sigma>'' A) (\<tau>''(next_time 0 \<tau>'' := 0)) A i) \<and> bval_of (signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'' := 0)) B i)))"
            using nand3_correctness_ind[OF bigstep3 _ _ ind1'' ind2'' ind3' _ ind4' ind5'' ` conc_wt \<Gamma> nand3` `styping \<Gamma> \<sigma>''`
                                           `ttyping \<Gamma> \<theta>''` `ttyping \<Gamma> (\<tau>''(next_time 0 \<tau>'' := 0))` `\<Gamma> C = Bty` `styping \<Gamma> def`]
            unfolding `next_time 0 \<tau>'' = 1` by auto
          moreover have "1 \<le> i \<Longrightarrow> signal_of (\<sigma>'' A) \<tau>'' A i = signal_of (\<sigma>' A) \<tau>'' A i"
          proof (cases "inf_time (to_trans_raw_sig \<tau>'') A i = None")
            case True
            assume "1 \<le> i"
            have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' A) k = 0"
              using True by (auto dest!: inf_time_noneE2)
            hence " (to_trans_raw_sig \<tau>'' A) 1 = 0"
              using `1 \<le> i` by auto
            hence "A \<notin> dom ( \<tau>'' 1)"
               unfolding trans_post_raw_def to_trans_raw_sig_def
              by (simp add: domIff zero_option_def)
            have "signal_of (\<sigma>'' A) \<tau>'' A i = next_state 0 \<tau>'' \<sigma>' A"
              using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
            also have "... = \<sigma>' A"
              using `A \<notin> dom ( \<tau>'' 1)` unfolding next_state_def
              by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
            finally have 0: "signal_of (\<sigma>'' A) \<tau>'' A i = \<sigma>' A"
              by auto
            have 1: "signal_of (\<sigma>' A) \<tau>'' A i = \<sigma>' A"
              using True unfolding to_signal_def comp_def by auto
            then show ?thesis
              using 0 1 by auto
          next
            case False
            then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') A i = Some ta"
              by auto
            then show ?thesis
              unfolding to_signal_def comp_def by auto
          qed
          moreover have "signal_of (\<sigma>'' A) (\<tau>''(next_time 0 \<tau>'':=0)) A i =
                         signal_of (\<sigma>'' A) \<tau>'' A i"
            apply (intro signal_of_rem_curr_trans_at_t) using ind1' ind2' by auto
          moreover have "1 \<le> i \<Longrightarrow> signal_of (\<sigma>'' B) \<tau>'' B i = signal_of (\<sigma>' B) \<tau>'' B i"
          proof (cases "inf_time (to_trans_raw_sig \<tau>'') B i = None")
            case True
            assume "1 \<le> i"
            have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' B) k = 0"
              using True by (auto dest!: inf_time_noneE2)
            hence " (to_trans_raw_sig \<tau>'' B) 1 = 0"
              using `1 \<le> i` by auto
            hence "B \<notin> dom ( \<tau>'' 1)"
               unfolding trans_post_raw_def to_trans_raw_sig_def
              by (simp add: domIff zero_option_def)
            have "signal_of (\<sigma>'' B) \<tau>'' B i = next_state 0 \<tau>'' \<sigma>' B"
              using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
            also have "... = \<sigma>' B"
              using `B \<notin> dom ( \<tau>'' 1)` unfolding next_state_def
              by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
            finally have 0: "signal_of (\<sigma>'' B) \<tau>'' B i = \<sigma>' B"
              by auto
            have 1: "signal_of (\<sigma>' B) \<tau>'' B i = \<sigma>' B"
              using True unfolding to_signal_def comp_def by auto
            then show ?thesis
              using 0 1 by auto
          next
            case False
            then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') B i = Some ta"
              by auto
            then show ?thesis
              unfolding to_signal_def comp_def by auto
          qed
          moreover have "signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'':=0)) B i =
                         signal_of (\<sigma>'' B) \<tau>'' B i"
            apply (intro signal_of_rem_curr_trans_at_t) using ind1' ind2' by auto
          ultimately have IR: "1 \<le> i \<Longrightarrow> bval_of (get_state res C) \<longleftrightarrow>
                                                \<not> (bval_of (signal_of (\<sigma>' A) \<tau>'' A i) \<and> bval_of (signal_of (\<sigma>' B) \<tau>'' B i))"
            by auto
          have " \<tau>'' 0 = 0"
            unfolding \<tau>''_def  by (auto simp add: trans_post_raw_def preempt_raw_def post_raw_def)
          have sA: "signal_of (\<sigma>' A) \<tau>'' A 0 = \<sigma>' A"
            by (metis \<open>\<tau>'' 0 = 0\<close> signal_of_zero zero_fun_def)
          have sB: "signal_of (\<sigma>' B) \<tau>'' B 0 = \<sigma>' B"
            by (metis \<open>\<tau>'' 0 = 0\<close> signal_of_zero zero_fun_def)
          have "next_time 0 \<tau>'' \<le> Suc i" and "1 \<le> next_time 0 \<tau>''"
            unfolding `next_time 0 \<tau>'' = 1` by auto   
          have "\<sigma>'' C = (let m =  \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
            unfolding \<sigma>''_def next_state_def `next_time 0 \<tau>'' = 1` by auto
          also have "... = Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))"
            unfolding \<tau>''_def Let_def trans_post_raw_def post_raw_def preempt_raw_def
            by (smt Nat.add_0_right One_nat_def Suc_eq_plus1 cancel_comm_monoid_add_class.diff_cancel
            comp_apply domIff fun_upd_same nec option.sel option.simps(3) override_on_def signal_of_zero
            zero_fun_def)
          also have "... = Bv (\<not> (bval_of (signal_of (\<sigma>' A) \<tau>'' A 0) \<and> bval_of (signal_of (\<sigma>' B) \<tau>'' B 0)))"
            using sA sB by auto
          finally have IR0: "bval_of (\<sigma>'' C) \<longleftrightarrow> \<not> (bval_of (signal_of (\<sigma>' A) \<tau>'' A 0) \<and> bval_of (signal_of (\<sigma>' B) \<tau>'' B 0))"
            by auto   
          have "signal_of (\<sigma>' A) \<tau>'' A i = signal_of (\<sigma>' A) (?\<tau>'(0:=0)) A i"
            unfolding \<tau>''_def  using signal_of_trans_post by fastforce
          also have "... = signal_of (\<sigma>' A) ?\<tau>' A i"
            by (smt \<sigma>'_def comp_apply next_state_def ntime override_on_def signal_of2_rem_curr_trans_at_0)
          also have "... = signal_of (\<sigma>' A) \<tau> A i"
            using signal_of_trans_post by fastforce
          also have "... = signal_of (def A) \<tau> A i"
          proof -
            have " (to_trans_raw_sig \<tau> A) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> A) 0 = None"
              by auto
            moreover
            { assume " (to_trans_raw_sig \<tau> A) 0 \<noteq> None"
              hence ?thesis
                by (meson signal_of2_cong_neq_none_at_0) }
            moreover
            { assume " (to_trans_raw_sig \<tau> A) 0 = None"
              hence "A \<notin> dom ( ?\<tau>' 0)"
                unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def
                by auto
              hence "\<sigma>' A = def A"
                unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
              hence ?thesis by auto }
            ultimately show ?thesis by auto
          qed
          finally have hel: "signal_of (\<sigma>' A) \<tau>'' A i = signal_of (def A) \<tau> A i"
            by auto
          have "signal_of (\<sigma>' B) \<tau>'' B i = signal_of (\<sigma>' B) (?\<tau>'(0:=0)) B i"
            unfolding \<tau>''_def  using signal_of_trans_post by fastforce
          also have "... = signal_of (\<sigma>' B) ?\<tau>' B i"
            using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def by metis
          also have "... = signal_of (\<sigma>' B) \<tau> B i"
            using signal_of_trans_post by fastforce
          also have "... = signal_of (def B) \<tau> B i"
          proof -
            have " (to_trans_raw_sig \<tau> B) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> B) 0 = None"
              by auto
            moreover
            { assume " (to_trans_raw_sig \<tau> B) 0 \<noteq> None"
              with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
            moreover
            { assume " (to_trans_raw_sig \<tau> B) 0 = None"
              hence "B \<notin> dom ( ?\<tau>' 0)"
                 unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def by auto
              hence "\<sigma>' B = def B"
                unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
              hence ?thesis by auto }
            ultimately show ?thesis by auto
          qed
          finally have "signal_of (\<sigma>' B) \<tau>'' B i = signal_of (def B) \<tau> B i"
            by auto
          then have ?thesis
          proof -
            { assume "1 \<noteq> i"
              { assume "\<not> (1::nat) < 1"
                moreover
                { assume "snd res \<noteq> (\<sigma>'', \<theta>'', \<tau>''(1 := 0)) \<and> \<not> (1::nat) < 1"
                  then have "(1, \<sigma>'', \<theta>'', \<tau>''(1 := 0)) \<noteq> res \<and> \<not> (1::nat) < 1"
                    by (metis snd_conv)
                  then have "\<not> 1, 1 , \<sigma>'' , \<gamma>'' , \<theta>'', def \<turnstile> <nand3 , \<tau>'' (1 := 0)> \<leadsto> res"
                    using bau by blast
                  then have "Suc i \<noteq> 1"
                    using \<open>next_time 0 \<tau>'' = 1\<close> bigstep3 by force }
                ultimately have "Suc i = 1 \<and> 0 = i \<longrightarrow> \<not> bval_of (to_signal (\<sigma>' B) (to_trans_raw_sig \<tau>'') B i) \<and> bval_of (get_time (snd res) C) \<or> \<not> bval_of (to_signal (\<sigma>' A) (to_trans_raw_sig \<tau>'') A i) \<and> bval_of (get_time (snd res) C) \<or> (\<not> bval_of (get_time (snd res) C) \<and> bval_of (to_signal (\<sigma>' A) (to_trans_raw_sig \<tau>'') A i)) \<and> bval_of (to_signal (\<sigma>' B) (to_trans_raw_sig \<tau>'') B i)"
                  by (metis (no_types) IR0 comp_apply fst_conv) }
              then have "Suc i = 1 \<longrightarrow> \<not> bval_of (to_signal (\<sigma>' B) (to_trans_raw_sig \<tau>'') B i) \<and> bval_of (get_time (snd res) C) \<or> \<not> bval_of (to_signal (\<sigma>' A) (to_trans_raw_sig \<tau>'') A i) \<and> bval_of (get_time (snd res) C) \<or> (\<not> bval_of (get_time (snd res) C) \<and> bval_of (to_signal (\<sigma>' A) (to_trans_raw_sig \<tau>'') A i)) \<and> bval_of (to_signal (\<sigma>' B) (to_trans_raw_sig \<tau>'') B i) \<or> 1 \<le> i"
                using le_less_linear by blast }
            then show ?thesis
              using IR \<open>next_time 0 \<tau>'' = 1\<close> \<open>signal_of (\<sigma>' B) \<tau>'' B i = signal_of (def B) \<tau> B i\<close> hel le_Suc_eq 
              by force
          qed }
        moreover
        { assume "bval_of (\<sigma>' C) \<longleftrightarrow> \<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B))"
          hence not_nec: "\<not> post_necessary_raw 0 (?\<tau>'(0:=0)) 0 C (Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))) (\<sigma>' C)"
          proof -
            have " (?\<tau>'(0:=0)) 0 C = None"
              by  (auto simp add:zero_map)
            thus ?thesis using post_necessary_raw_correctness `bval_of (\<sigma>' C) \<longleftrightarrow> \<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B))`
              by (smt \<open>\<sigma>' C = def C\<close> add.right_neutral assms(4) assms(5) signal_of_zero styping_def
              ty.distinct(1) type_of.simps(2) val.exhaust_sel zero_option_def)
          qed
          hence lookup: " \<tau>'' = preempt_raw C (?\<tau>'(0:=0)) 1"
            unfolding \<tau>''_def trans_post_raw_def by auto
          hence "to_trans_raw_sig \<tau>'' C = 0"
            unfolding preempt_raw_def to_trans_raw_sig_def
            apply (intro ext)+ by (auto simp add: zero_fun_def zero_option_def)
          { assume "A \<notin> next_event 0 \<tau>'' \<sigma>' \<and> B \<notin> next_event 0 \<tau>'' \<sigma>'"
            hence "A \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') A) = \<sigma>' A"
              and "B \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') B) = \<sigma>' B"
              unfolding next_event_def ntime Let_def by auto
            hence helper: "\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)) \<longleftrightarrow>  \<not> (bval_of (next_state 0 \<tau>'' \<sigma>' A) \<and> bval_of (next_state 0 \<tau>'' \<sigma>' B))"
              unfolding next_state_def Let_def  by (simp add: override_on_def)
            have "next_state 0 \<tau>'' \<sigma>' C = (let m =  \<tau>'' (next_time 0 \<tau>'') in override_on \<sigma>' (the \<circ> m) (dom m)) C"
              unfolding next_state_def by auto
            also have "... = \<sigma>' C"
            proof -
              define m where "m =  \<tau>'' (next_time 0 \<tau>'')"
              hence "C \<notin> dom m"
                using `to_trans_raw_sig \<tau>'' C = 0` unfolding next_time_def
                unfolding to_trans_raw_sig_def  by (metis domIff zero_fun_def zero_option_def)
              thus ?thesis
                unfolding Let_def override_on_def m_def by auto
            qed
            also have "... = Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))"
              using `bval_of (\<sigma>' C) \<longleftrightarrow> \<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B))`
              by (metis fun_upd_same not_nec semiring_normalization_rules(6) signal_of_zero zero_fun_def)
            finally have "bval_of (next_state 0 \<tau>'' \<sigma>' C) \<longleftrightarrow> \<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B))"
              by auto
            hence "bval_of (next_state 0 \<tau>'' \<sigma>' C) \<longleftrightarrow> \<not> (bval_of (next_state 0 \<tau>'' \<sigma>' A) \<and> bval_of (next_state 0 \<tau>'' \<sigma>' B))"
              using helper by auto }
          hence  ind4': "A \<notin> \<gamma>'' \<and> B \<notin> \<gamma>'' \<Longrightarrow> bval_of (\<sigma>'' C) = (\<not> (bval_of (\<sigma>'' A) \<and> bval_of (\<sigma>'' B)))"
            unfolding \<gamma>''_def \<sigma>''_def by auto
          have ind5': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig \<tau>'' C) n = 0"
            using `to_trans_raw_sig \<tau>'' C = 0` by (simp add: zero_fun_def)
          hence ind5'': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig (\<tau>''(next_time 0 \<tau>'':=0)) C) n = 0"
            by (simp add: to_trans_raw_sig_def)
          have "styping \<Gamma> \<sigma>''"
            unfolding \<sigma>''_def
            by (metis \<open>styping \<Gamma> (next_state 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def
            B)))) (def C) \<tau> 0 1) def)\<close> \<sigma>'_def \<tau>''_def assms(5) assms(6) next_state_preserve_styping
            trans_post_preserve_type_correctness ttyping_rem_curr_trans type_of.simps(1))
          have "ttyping \<Gamma> \<theta>''"
            unfolding \<theta>''_def
            by (metis \<open>styping \<Gamma> (next_state 0 (trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def
            B)))) (def C) \<tau> 0 1) def)\<close> \<sigma>'_def add_to_beh_preserve_type_correctness domIff ttyping_def
            zero_fun_def zero_map)
          have "ttyping \<Gamma> (\<tau>''(next_time 0 \<tau>'' := 0))"
            by (simp add: \<tau>''_def assms(5) assms(6) trans_post_preserve_type_correctness ttyping_rem_curr_trans)
          have *: "next_time 0 \<tau>'' \<le> i \<Longrightarrow>
             bval_of (get_state res C) =
         (\<not> (bval_of (signal_of (\<sigma>'' A) (\<tau>''(next_time 0 \<tau>'' := 0)) A i) \<and> bval_of (signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'' := 0)) B i)))"
            using nand3_correctness_ind[OF bigstep3 _ _ ind1'' ind2'' ind3' _ ind4' ind5'' `conc_wt \<Gamma> nand3` `styping \<Gamma> \<sigma>''`
                  `ttyping \<Gamma> \<theta>''` `ttyping \<Gamma> (\<tau>''(next_time 0 \<tau>'' := 0))` ` \<Gamma> C = Bty` `styping \<Gamma> def`]
            by blast
(*           have "next_time 0 \<tau>'' \<le> i"
            using `next_time 0 \<tau>'' < Suc i`  using less_Suc_eq_le sorry *)
          moreover have "next_time 0 \<tau>'' \<le> i \<Longrightarrow> signal_of (\<sigma>'' A) \<tau>'' A i = signal_of (\<sigma>' A) \<tau>'' A i"
          proof (cases "inf_time (to_trans_raw_sig \<tau>'') A i = None")
            case True
            assume "next_time 0 \<tau>'' \<le> i"
            have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' A) k = 0"
              using True by (auto dest!: inf_time_noneE2)
            hence " (to_trans_raw_sig \<tau>'' A) (next_time 0 \<tau>'') = 0"
              using `next_time 0 \<tau>'' \<le> i` by auto
            hence "A \<notin> dom ( \<tau>'' (next_time 0 \<tau>''))"
              unfolding next_time_def  unfolding trans_post_raw_def to_trans_raw_sig_def
              by (simp add: domIff zero_option_def)
            have "signal_of (\<sigma>'' A) \<tau>'' A i = next_state 0 \<tau>'' \<sigma>' A"
              using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
            also have "... = \<sigma>' A"
              using `A \<notin> dom ( \<tau>'' (next_time 0 \<tau>''))` unfolding next_state_def
              by (metis override_on_apply_notin)
            finally have 0: "signal_of (\<sigma>'' A) \<tau>'' A i = \<sigma>' A"
              by auto
            have 1: "signal_of (\<sigma>' A) \<tau>'' A i = \<sigma>' A"
              using True unfolding to_signal_def comp_def by auto
            then show ?thesis
              using 0 1 by auto
          next
            case False
            then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') A i = Some ta"
              by auto
            then show ?thesis
              unfolding to_signal_def comp_def by auto
          qed
          moreover have "signal_of (\<sigma>'' A) (\<tau>''(next_time 0 \<tau>'':=0)) A i = signal_of (\<sigma>'' A) \<tau>'' A i"
            apply (intro signal_of_rem_curr_trans_at_t)
            using ind1' ind2' by auto
          moreover have "(next_time 0 \<tau>'') \<le> i \<Longrightarrow> signal_of (\<sigma>'' B) \<tau>'' B i = signal_of (\<sigma>' B) \<tau>'' B i"
          proof (cases "inf_time (to_trans_raw_sig \<tau>'') B i = None")
            case True
            assume "(next_time 0 \<tau>'') \<le> i"
            have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' B) k = 0"
              using True by (auto dest!: inf_time_noneE2)
            hence " (to_trans_raw_sig \<tau>'' B) (next_time 0 \<tau>'') = 0"
              using `(next_time 0 \<tau>'') \<le> i` by auto
            hence "B \<notin> dom ( \<tau>'' (next_time 0 \<tau>''))"
              unfolding next_time_def  unfolding trans_post_raw_def to_trans_raw_sig_def
              by (simp add: domIff zero_option_def)
            have "signal_of (\<sigma>'' B) \<tau>'' B i = next_state 0 \<tau>'' \<sigma>' B"
              using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
            also have "... = \<sigma>' B"
              using `B \<notin> dom ( \<tau>'' (next_time 0 \<tau>''))` unfolding next_state_def
              by (metis override_on_apply_notin)
            finally have 0: "signal_of (\<sigma>'' B) \<tau>'' B i = \<sigma>' B"
              by auto
            have 1: "signal_of (\<sigma>' B) \<tau>'' B i = \<sigma>' B"
              using True unfolding to_signal_def comp_def by auto
            then show ?thesis
              using 0 1 by auto
          next
            case False
            then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') B i = Some ta"
              by auto
            then show ?thesis
              unfolding to_signal_def comp_def by auto
          qed
          moreover have "signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'' := 0)) B i = signal_of (\<sigma>'' B) \<tau>'' B i"
            apply (intro signal_of_rem_curr_trans_at_t)
            using ind1' ind2' by auto
          ultimately have **: "next_time 0 \<tau>'' \<le> i \<Longrightarrow>
            bval_of (get_state res C) = (\<not> (bval_of (signal_of (\<sigma>' A) \<tau>'' A i) \<and> bval_of (signal_of (\<sigma>' B) \<tau>'' B i)))"
            using "*" by auto
          have "signal_of (\<sigma>' A) \<tau>'' A i = signal_of (\<sigma>' A) (?\<tau>'(0:=0)) A i"
            unfolding \<tau>''_def   using signal_of_trans_post by fastforce
          also have "... = signal_of (\<sigma>' A) ?\<tau>' A i"
            using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
          also have "... = signal_of (\<sigma>' A) \<tau> A i"
            using signal_of_trans_post by fastforce
          also have "... = signal_of (def A) \<tau> A i"
          proof -
            have " (to_trans_raw_sig \<tau> A) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> A) 0 = None"
              by auto
            moreover
            { assume " (to_trans_raw_sig \<tau> A) 0 \<noteq> None"
              with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
            moreover
            { assume " (to_trans_raw_sig \<tau> A) 0 = None"
              hence "A \<notin> dom ((trans_post_raw C ?x (def C) \<tau> 0 1) 0)"
                 unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def
                by auto
              hence "\<sigma>' A = def A"
                unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
              hence ?thesis by auto }
            ultimately show ?thesis by auto
          qed
          finally have hel: "signal_of (\<sigma>' A) \<tau>'' A i = signal_of (def A) \<tau> A i"
            by auto
          have "signal_of (\<sigma>' B) \<tau>'' B i = signal_of (\<sigma>' B) (?\<tau>'(0:=0)) B i"
            unfolding \<tau>''_def using signal_of_trans_post by fastforce
          also have "... = signal_of (\<sigma>' B) ?\<tau>' B i"
            using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
          also have "... = signal_of (\<sigma>' B) \<tau> B i"
            using signal_of_trans_post by fastforce
          also have "... = signal_of (def B) \<tau> B i"
          proof -
              have " (to_trans_raw_sig \<tau> B) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> B) 0 = None"
                by auto
              moreover
              { assume " (to_trans_raw_sig \<tau> B) 0 \<noteq> None"
                with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
              moreover
              { assume " (to_trans_raw_sig \<tau> B) 0 = None"
                hence "B \<notin> dom ( (trans_post_raw C ?x (def C) \<tau> 0 1) 0)"
                   unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def by auto
                hence "\<sigma>' B = def B"
                  unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
                hence ?thesis by auto }
              ultimately show ?thesis by auto
            qed
          finally have hel2: "signal_of (\<sigma>' B) \<tau>'' B i = signal_of (def B) \<tau> B i"
            by auto
          with ** have ?thesis
            using hel hel2  using le_less_linear  
            sorry }
        ultimately show ?thesis by auto
      next
        case none
        hence \<tau>''_def: "\<tau>'' = ?\<tau>'(0:=0)"
          using cyc unfolding nand3_def t'_def' by auto
        moreover have " \<tau> 0 C = None"
          using assms(2)  unfolding to_trans_raw_sig_def  by (metis zero_map)
        have "\<tau>'' \<noteq> 0"
          using `\<tau>'' = ?\<tau>'(0 := 0)`
          using \<open>(trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1) (t' := 0) \<noteq> 0\<close> t'_def' by auto
        hence "next_time 0 \<tau>'' = (LEAST n. dom ( \<tau>'' n) \<noteq> {})"
          unfolding next_time_def by auto
        have "... = 1"
        proof (rule Least_equality)
          show "dom ( \<tau>'' 1) \<noteq> {}"
            using False ` ?\<tau>' 1 C = Some ?x` unfolding \<tau>''_def
            by  auto
        next
          { fix y :: nat
            assume "\<not> 1 \<le> y"
            hence "y < 1" by auto hence "y = 0" by auto
            hence "dom ( \<tau>'' y) = {}"
              unfolding \<tau>''_def   by (auto simp add: trans_post_raw_def zero_map) }
          thus "\<And>y. dom ( \<tau>'' y) \<noteq> {} \<Longrightarrow> 1 \<le> y "
            by auto
        qed
        hence "next_time 0 \<tau>'' = 1"
          by (simp add: \<open>next_time 0 \<tau>'' = (LEAST n. dom (\<tau>'' n) \<noteq> {})\<close>)
        have "\<sigma>' A = def A" and "\<sigma>' B = def B"
          using none unfolding \<gamma>'_def \<sigma>'_def next_event_def Let_def ntime
          by (metis \<gamma>'_def next_state_fixed_point none)+
        { assume "A \<notin> next_event 0 \<tau>'' \<sigma>' \<and> B \<notin> next_event 0 \<tau>'' \<sigma>'"
          hence "A \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') A) = \<sigma>' A"
            and "B \<notin> dom ( \<tau>'' (next_time 0 \<tau>'')) \<or> the ( \<tau>'' (next_time 0 \<tau>'') B) = \<sigma>' B"
            unfolding next_event_def ntime Let_def by auto
          hence helper: "\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)) \<longleftrightarrow>  \<not> (bval_of (next_state 0 \<tau>'' \<sigma>' A) \<and> bval_of (next_state 0 \<tau>'' \<sigma>' B))"
            unfolding next_state_def Let_def  by (simp add: override_on_def)
          have "next_state 0 \<tau>'' \<sigma>' C = (let m =  \<tau>'' (next_time 0 \<tau>'') in override_on \<sigma>' (the \<circ> m) (dom m)) C"
            unfolding next_state_def by auto
          also have "... = (let m =  \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
            unfolding `next_time 0 \<tau>'' = 1` by auto
          also have "... = Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))"
            unfolding \<tau>''_def  `\<sigma>' A = def A` `\<sigma>' B = def B` using False ` ?\<tau>' 1 C = Some ?x`
             unfolding trans_post_raw_def Let_def post_raw_def by (auto simp add:override_on_def)
          finally have "bval_of (next_state 0 \<tau>'' \<sigma>' C) \<longleftrightarrow> \<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B))"
            by auto
          hence "bval_of (next_state 0 \<tau>'' \<sigma>' C) \<longleftrightarrow> \<not> (bval_of (next_state 0 \<tau>'' \<sigma>' A) \<and> bval_of (next_state 0 \<tau>'' \<sigma>' B))"
            using helper by auto }
        hence  ind4': "A \<notin> \<gamma>'' \<and> B \<notin> \<gamma>'' \<Longrightarrow> bval_of (\<sigma>'' C) = (\<not> (bval_of (\<sigma>'' A) \<and> bval_of (\<sigma>'' B)))"
          unfolding \<gamma>''_def \<sigma>''_def by auto
        have "\<And>n. 1 < n \<Longrightarrow>  (to_trans_raw_sig \<tau>'' C) n = 0"
          unfolding \<tau>''_def   unfolding trans_post_raw_def to_trans_raw_sig_def preempt_raw_def
          post_raw_def by (simp add: zero_option_def)
        hence ind5': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig \<tau>'' C) n = 0"
          unfolding `next_time 0 \<tau>'' = 1` by auto
        hence ind5'': "\<And>n. next_time 0 \<tau>'' < n \<Longrightarrow>  (to_trans_raw_sig (\<tau>'' (next_time 0 \<tau>'':=0)) C) n = 0"
          by (simp add: to_trans_raw_sig_def)
        have "styping \<Gamma> \<sigma>''"
          unfolding \<sigma>''_def
          by (simp add: \<sigma>'_def assms(4) assms(5) assms(6) calculation next_state_preserve_styping
          trans_post_preserve_type_correctness ttyping_rem_curr_trans)
        have "ttyping \<Gamma> \<theta>''"
          unfolding \<theta>''_def
          by (metis \<sigma>'_def add_to_beh_preserve_type_correctness assms(4) assms(5) assms(6) domIff
          next_state_preserve_styping trans_post_preserve_type_correctness ttyping_def type_of.simps(1)
          zero_fun_def zero_option_def)
        have "ttyping \<Gamma> (\<tau>''(next_time 0 \<tau>'' := 0))"
          by (simp add: assms(5) assms(6) calculation trans_post_preserve_type_correctness ttyping_rem_curr_trans)
        have *: "1 \<le> i \<Longrightarrow>
           bval_of (get_state res C) =
       (\<not> (bval_of (signal_of (\<sigma>'' A) (\<tau>''(next_time 0 \<tau>'' := 0)) A i) \<and> bval_of (signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'' := 0)) B i)))"
          using nand3_correctness_ind[OF bigstep3 _ _ ind1'' ind2'' ind3' _ ind4' ind5'' `conc_wt \<Gamma> nand3` `styping \<Gamma> \<sigma>''` `ttyping \<Gamma> \<theta>''`
                                        `ttyping \<Gamma> (\<tau>''(next_time 0 \<tau>'' := 0))` `\<Gamma> C = Bty` `styping \<Gamma> def`]
          unfolding `next_time 0 \<tau>'' = 1` by auto
        moreover have "1 \<le> i \<Longrightarrow> signal_of (\<sigma>'' A) \<tau>'' A i = signal_of (\<sigma>' A) \<tau>'' A i"
        proof (cases "inf_time (to_trans_raw_sig \<tau>'') A i = None")
          case True
          assume "1 \<le> i"
          have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' A) k = 0"
            using True by (auto dest!: inf_time_noneE2)
          hence " (to_trans_raw_sig \<tau>'' A) 1 = 0"
            using `1 \<le> i` by auto
          hence "A \<notin> dom ( \<tau>'' 1)"
             unfolding trans_post_raw_def to_trans_raw_sig_def
            by (simp add: domIff zero_option_def)
          have "signal_of (\<sigma>'' A) \<tau>'' A i = next_state 0 \<tau>'' \<sigma>' A"
            using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
          also have "... = \<sigma>' A"
            using `A \<notin> dom ( \<tau>'' 1)` unfolding next_state_def
            by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
          finally have 0: "signal_of (\<sigma>'' A) \<tau>'' A i = \<sigma>' A"
            by auto
          have 1: "signal_of (\<sigma>' A) \<tau>'' A i = \<sigma>' A"
            using True unfolding to_signal_def comp_def by auto
          then show ?thesis
            using 0 1 by auto
        next
          case False
          then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') A i = Some ta"
            by auto
          then show ?thesis
            unfolding to_signal_def comp_def by auto
        qed
        moreover have "signal_of (\<sigma>'' A) (\<tau>'' (next_time 0 \<tau>'':=0)) A i =  signal_of (\<sigma>'' A) \<tau>'' A i"
          apply (intro signal_of_rem_curr_trans_at_t)
          using ind1' ind2' by auto
        moreover have "1 \<le> i \<Longrightarrow> signal_of (\<sigma>'' B) \<tau>'' B i = signal_of (\<sigma>' B) \<tau>'' B i"
        proof (cases "inf_time (to_trans_raw_sig \<tau>'') B i = None")
          case True
          assume "1 \<le> i"
          have "\<forall>k. k \<le> i \<longrightarrow>  (to_trans_raw_sig \<tau>'' B) k = 0"
            using True by (auto dest!: inf_time_noneE2)
          hence " (to_trans_raw_sig \<tau>'' B) 1 = 0"
            using `1 \<le> i` by auto
          hence "B \<notin> dom ( \<tau>'' 1)"
             unfolding trans_post_raw_def to_trans_raw_sig_def
            by (simp add: domIff zero_option_def)
          have "signal_of (\<sigma>'' B) \<tau>'' B i = next_state 0 \<tau>'' \<sigma>' B"
            using True unfolding to_signal_def comp_def \<tau>''_def  by (simp add: \<sigma>''_def \<tau>''_def)
          also have "... = \<sigma>' B"
            using `B \<notin> dom ( \<tau>'' 1)` unfolding next_state_def
            by (metis \<open>next_time 0 \<tau>'' = 1\<close> override_on_apply_notin)
          finally have 0: "signal_of (\<sigma>'' B) \<tau>'' B i = \<sigma>' B"
            by auto
          have 1: "signal_of (\<sigma>' B) \<tau>'' B i = \<sigma>' B"
            using True unfolding to_signal_def comp_def by auto
          then show ?thesis
            using 0 1 by auto
        next
          case False
          then obtain ta where "inf_time (to_trans_raw_sig \<tau>'') B i = Some ta"
            by auto
          then show ?thesis
            unfolding to_signal_def comp_def by auto
        qed
        moreover have "signal_of (\<sigma>'' B) (\<tau>''(next_time 0 \<tau>'':=0)) B i =  signal_of (\<sigma>'' B) \<tau>'' B i"
          apply (intro signal_of_rem_curr_trans_at_t)
          using ind1' ind2' by auto
        ultimately have IR: "1 \<le> i \<Longrightarrow> bval_of (get_state res C) \<longleftrightarrow>
                                              \<not> (bval_of (signal_of (\<sigma>' A) \<tau>'' A i) \<and> bval_of (signal_of (\<sigma>' B) \<tau>'' B i))"
          by auto
        have " \<tau>'' 0 = 0"
          unfolding \<tau>''_def  by (auto simp add: trans_post_raw_def)
        have sA: "signal_of (\<sigma>' A) \<tau>'' A 0 = \<sigma>' A"
          by (metis \<open>\<tau>'' 0 = 0\<close> signal_of_zero zero_fun_def)
        have sB: "signal_of (\<sigma>' B) \<tau>'' B 0 = \<sigma>' B"
          by (metis \<open>\<tau>'' 0 = 0\<close> signal_of_zero zero_fun_def)
        have "next_time 0 \<tau>'' \<le> Suc i" and "1 \<le> next_time 0 \<tau>''"
          unfolding `next_time 0 \<tau>'' = 1` by auto        
        have "\<sigma>'' C = (let m =  \<tau>'' 1 in override_on \<sigma>' (the \<circ> m) (dom m)) C"
          unfolding \<sigma>''_def next_state_def `next_time 0 \<tau>'' = 1` by auto
        also have "... = Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))"
          using ` ?\<tau>' 1 C = Some ?x` unfolding \<tau>''_def Let_def  `\<sigma>' A = def A` `\<sigma>' B = def B`
            unfolding trans_post_raw_def  post_raw_def by (auto simp add: override_on_def)
        also have "... = Bv (\<not> (bval_of (signal_of (\<sigma>' A) \<tau>'' A 0) \<and> bval_of (signal_of (\<sigma>' B) \<tau>'' B 0)))"
          using sA sB by auto
        finally have IR0: "bval_of (\<sigma>'' C) \<longleftrightarrow> \<not> (bval_of (signal_of (\<sigma>' A) \<tau>'' A 0) \<and> bval_of (signal_of (\<sigma>' B) \<tau>'' B 0))"
          by auto
        have "signal_of (\<sigma>' A) \<tau>'' A i = signal_of (\<sigma>' A) (?\<tau>'(0:= 0)) A i"
          unfolding \<tau>''_def by (metis \<tau>''_def sig.distinct(3))
        also have "... = signal_of (\<sigma>' A) ?\<tau>' A i"
          using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
        also have "... = signal_of (\<sigma>' A) \<tau> A i"
          using signal_of_trans_post by fastforce
        also have "... = signal_of (def A) \<tau> A i"
        proof -
          have " (to_trans_raw_sig \<tau> A) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> A) 0 = None"
            by auto
          moreover
          { assume " (to_trans_raw_sig \<tau> A) 0 \<noteq> None"
            with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
          moreover
          { assume " (to_trans_raw_sig \<tau> A) 0 = None"
            hence "A \<notin> dom ( (trans_post_raw C ?x (def C) \<tau> 0 1) 0)"
              unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def
              by auto
            hence "\<sigma>' A = def A"
              unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
            hence ?thesis by auto }
          ultimately show ?thesis by auto
        qed
        finally have hel: "signal_of (\<sigma>' A) \<tau>'' A i = signal_of (def A) \<tau> A i"
          by auto
        have "signal_of (\<sigma>' B) \<tau>'' B i = signal_of (\<sigma>' B) (?\<tau>'(0:=0)) B i"
          unfolding \<tau>''_def  by fastforce
        also have "... = signal_of (\<sigma>' B) ?\<tau>' B i"
          using signal_of2_rem_curr_trans_at_0 ind2 unfolding ntime \<sigma>'_def  by metis
        also have "... = signal_of (\<sigma>' B) \<tau> B i"
          using signal_of_trans_post by fastforce
        also have "... = signal_of (def B) \<tau> B i"
        proof -
          have " (to_trans_raw_sig \<tau> B) 0 \<noteq> None \<or>  (to_trans_raw_sig \<tau> B) 0 = None"
            by auto
          moreover
          { assume " (to_trans_raw_sig \<tau> B) 0 \<noteq> None"
            with signal_of2_cong_neq_none_at_0 have ?thesis by metis }
          moreover
          { assume " (to_trans_raw_sig \<tau> B) 0 = None"
            hence "B \<notin> dom ( (trans_post_raw C ?x (def C) \<tau> 0 1) 0)"
               unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def post_raw_def by auto
            hence "\<sigma>' B = def B"
              unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0` Let_def by auto
            hence ?thesis by auto }
          ultimately show ?thesis by auto
        qed
        finally have "signal_of (\<sigma>' B) \<tau>'' B i = signal_of (def B) \<tau> B i"
          by auto
        then show ?thesis
          using IR IR0 hel le_less_linear \<open>next_time 0 \<tau>'' = 1\<close> \<open>next_time 0 \<tau>'' \<le> Suc i\<close> le_Suc_eq
        proof -
          { assume "1 \<noteq> i"
            { assume "\<not> (1::nat) < 1"
              moreover
              { assume "snd res \<noteq> (\<sigma>'', \<theta>'', \<tau>''(1 := 0)) \<and> \<not> (1::nat) < 1"
                then have "(1, \<sigma>'', \<theta>'', \<tau>''(1 := 0)) \<noteq> res \<and> \<not> (1::nat) < 1"
                  by (meson snd_conv)
                then have "\<not> 1, 1 , \<sigma>'' , \<gamma>'' , \<theta>'', def \<turnstile> <nand3 , \<tau>'' (1 := 0)> \<leadsto> res"
                  using bau by blast
                then have "Suc i \<noteq> 1"
                  using \<open>next_time 0 \<tau>'' = 1\<close> bigstep3 by force }
              ultimately have "Suc i = 1 \<and> 0 = i \<longrightarrow> \<not> bval_of (to_signal (\<sigma>' B) (to_trans_raw_sig \<tau>'') B i) \<and> bval_of (get_time (snd res) C) \<or> \<not> bval_of (to_signal (\<sigma>' A) (to_trans_raw_sig \<tau>'') A i) \<and> bval_of (get_time (snd res) C) \<or> (\<not> bval_of (get_time (snd res) C) \<and> bval_of (to_signal (\<sigma>' A) (to_trans_raw_sig \<tau>'') A i)) \<and> bval_of (to_signal (\<sigma>' B) (to_trans_raw_sig \<tau>'') B i)"
                by (metis IR0 comp_apply fst_conv) }
            then have "Suc i = 1 \<longrightarrow> \<not> bval_of (to_signal (\<sigma>' B) (to_trans_raw_sig \<tau>'') B i) \<and> bval_of (get_time (snd res) C) \<or> \<not> bval_of (to_signal (\<sigma>' A) (to_trans_raw_sig \<tau>'') A i) \<and> bval_of (get_time (snd res) C) \<or> (\<not> bval_of (get_time (snd res) C) \<and> bval_of (to_signal (\<sigma>' A) (to_trans_raw_sig \<tau>'') A i)) \<and> bval_of (to_signal (\<sigma>' B) (to_trans_raw_sig \<tau>'') B i) \<or> 1 \<le> i"
              by simp }
          then show ?thesis
            using IR \<open>next_time 0 \<tau>'' = 1\<close> \<open>signal_of (\<sigma>' B) \<tau>'' B i = signal_of (def B) \<tau> B i\<close> hel le_Suc_eq by force
        qed
      qed }
    moreover
    { assume "Suc i < next_time 0 \<tau>''"
      have "get_state res = \<sigma>'"
        apply (rule bau[OF bigstep'])
        using \<open>Suc i < next_time 0 \<tau>''\<close> b_conc_exec_deterministic cyc not_less by blast auto         
      hence "get_state res C = def C"
        by (simp add: \<open>\<sigma>' C = def C\<close>)
      hence ?thesis
      proof (cases "A \<in> \<gamma>' \<or> B \<in> \<gamma>'")
      case True
      hence "b_seq_exec 0 \<sigma>' \<gamma>' 0 def (get_seq nand3) (?\<tau>' (t':=0)) \<tau>''"
        using cyc  by (metis conc_cases(1) conc_stmt.sel(4) disjnt_insert1 nand3_def)
      hence "is_Bv (\<sigma>' A)" and "is_Bv (\<sigma>' B)"
        by (metis \<open>\<Gamma> A = Bty\<close> \<open>\<Gamma> B = Bty\<close> \<open>styping \<Gamma> \<sigma>'\<close> styping_def ty.distinct(1) type_of.simps(2)
        val.collapse(2))+
      hence "0 , \<sigma>' , \<gamma>' , 0, def  \<turnstile> Bsig A \<longrightarrow>\<^sub>b Bv (bval_of (\<sigma>' A))" and
            "0 , \<sigma>' , \<gamma>' , 0, def  \<turnstile> Bsig B \<longrightarrow>\<^sub>b Bv (bval_of (\<sigma>' B))"
        by (auto intro!: beval_raw.intros)
      hence "0 , \<sigma>' , \<gamma>' , 0, def  \<turnstile> Bnand (Bsig A) (Bsig B) \<longrightarrow>\<^sub>b 
                      (Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B))))" (is "_, _, _, _, _ \<turnstile> _ \<longrightarrow>\<^sub>b ?x'")
        by (intro beval_raw.intros)  
      hence "0, \<sigma>', \<gamma>', 0, def \<turnstile> <Bassign_trans C (Bnand (Bsig A) (Bsig B)) 1, (?\<tau>' (t':=0))> \<longrightarrow>\<^sub>s trans_post_raw C ?x' (\<sigma>' C) (?\<tau>' (t':=0)) 0 1"
        by (simp add: b_seq_exec.intros(5))
      hence \<tau>''_def: "\<tau>'' = trans_post_raw C ?x' (\<sigma>' C) (?\<tau>' (t':=0)) 0 1"
        by (metis \<open>0 , \<sigma>' , \<gamma>' , 0, def \<turnstile> <get_seq nand3 , (trans_post_raw C (Bv (\<not> (bval_of (def A)
        \<and> bval_of (def B)))) (def C) \<tau> 0 1) (t' := 0)> \<longrightarrow>\<^sub>s \<tau>''\<close> b_seq_exec_deterministic
        conc_stmt.sel(4) nand3_def)
      have "post_necessary_raw (1 - 1) (?\<tau>' (t':=0)) 0 C ?x' (\<sigma>' C) \<or>\<not> post_necessary_raw (1 - 1) (?\<tau>' (t':=0)) 0 C ?x' (\<sigma>' C)"
        by auto
      moreover
      { assume "post_necessary_raw (1 - 1) (?\<tau>' (t':=0)) 0 C ?x' (\<sigma>' C)"
        hence "signal_of (\<sigma>' C) (?\<tau>' (t' := 0)) C 0 \<noteq> ?x'"
          by auto
        hence "\<tau>'' = post_raw C ?x' (?\<tau>' (t':=0)) 1"
          unfolding \<tau>''_def trans_post_raw_def by auto
        hence "next_time 0 \<tau>'' = 1"
          by (smt fun_upd_eqD fun_upd_triv less_one nat_less_le next_time_at_least
          next_time_at_least2 next_time_def option.distinct(1) post_raw_def t'_def' zero_fun_def
          zero_option_def) 
        with \<open>Suc i < next_time 0 \<tau>''\<close> have "False"
          by auto
        hence ?thesis
          by auto }
      moreover
      { assume "\<not> post_necessary_raw (1 - 1) (?\<tau>' (t':=0)) 0 C ?x' (\<sigma>' C)"
        hence "signal_of (\<sigma>' C) (?\<tau>' (t':=0)) C 0 = ?x'"
          by auto
        moreover have "signal_of (\<sigma>' C) (?\<tau>' (t':=0)) C 0 = \<sigma>' C"
          unfolding `t' = 0`  by (metis fun_upd_same signal_of_zero zero_fun_def)
        ultimately have "\<sigma>' C = ?x'"
          by auto
        hence "def C = ?x'"
          using \<open>\<sigma>' C = def C\<close> by auto
        hence "\<tau>'' = preempt_raw C (?\<tau>' (t':=0)) 1"
          unfolding \<tau>''_def trans_post_raw_def 
          by (metis \<open>\<sigma>' C = Bv (\<not> (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))\<close> add.left_neutral
          cancel_comm_monoid_add_class.diff_cancel fun_upd_same signal_of_zero t'_def' zero_fun_def)
        have *: "\<And>s. s \<in> {A, B} \<Longrightarrow> \<sigma>' s =  
            (let m = post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> 1 0 in override_on def (the \<circ> m) (dom m)) s"
          unfolding \<sigma>'_def next_state_def `next_time 0 ?\<tau>' = 0`
          using \<open>?\<tau>' = post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> 1\<close> by auto
        have "\<And>n. n < next_time 0 \<tau>'' \<Longrightarrow> \<tau>'' n  = 0"
          using next_time_at_least2 by blast
        hence "\<And>s n. s \<in> {A, B} \<Longrightarrow> n < next_time 0 \<tau>'' \<Longrightarrow> \<tau>'' n s = 0"
          by (simp add: zero_fun_def)
        hence "\<And>s n. s \<in> {A, B} \<Longrightarrow> n < next_time 0 \<tau>'' \<Longrightarrow> (?\<tau>' (t' := 0)) n s = 0"
          unfolding \<open>\<tau>'' = preempt_raw C (?\<tau>' (t':=0)) 1\<close> 
          by (metis \<open>0 , \<sigma>' , \<gamma>' , 0, def \<turnstile> <get_seq nand3 , (trans_post_raw C (Bv (\<not> (bval_of (def
          A) \<and> bval_of (def B)))) (def C) \<tau> 0 1) (t' := 0)> \<longrightarrow>\<^sub>s \<tau>''\<close> \<open>\<tau>'' = preempt_raw C
          ((trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1) (t' := 0))
          1\<close> insertE insert_absorb insert_not_empty nand3_does_not_modify_AB' not_less_zero
          sig.distinct(3) sig.distinct(5))
        hence **: "\<And>s n. s \<in> {A , B} \<Longrightarrow> n < next_time 0 \<tau>'' \<Longrightarrow> (\<tau> (t' := 0)) n s = 0"
          by (metis (mono_tags, hide_lams) assms(2) fun_upd_apply to_trans_raw_sig_def
          trans_post_raw_diff_sig zero_fun_def)
        have "A \<in> dom (?\<tau>' 0) \<or> A \<notin> dom (?\<tau>' 0)"
          by auto
        moreover
        { assume "A \<notin> dom (?\<tau>' 0)"
          hence "A \<notin> dom (\<tau> 0)"
            by (metis domIff sig.distinct(3) to_trans_raw_sig_def trans_post_raw_diff_sig)
          have "\<sigma>' A = def A"
            using * \<open>A \<notin> dom (?\<tau>' 0)\<close> unfolding Let_def 
            using \<open>?\<tau>' = post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> 1\<close> by auto
          also have "... = signal_of (def A) \<tau> A 0"
            using `A \<notin> dom (?\<tau>' 0)` 
            by (metis domIff sig.distinct(3) signal_of_zero to_trans_raw_sig_def
            trans_post_raw_diff_sig zero_option_def)
          also have "... = signal_of (def A) \<tau> A i"
            apply (rule signal_of_less_ind'[THEN sym])
            by (metis "**" Suc_lessD \<open>Suc i < next_time 0 \<tau>''\<close> fun_upd_apply insert_iff
            le_less_trans not_less_eq t'_def') auto
          finally have "\<sigma>' A = signal_of (def A) \<tau> A i"
            by auto }
        moreover
        { assume "A \<in> dom (?\<tau>' 0)"
          hence "A \<in> dom (\<tau> 0)"
            by (metis domIff sig.distinct(3) to_trans_raw_sig_def trans_post_raw_diff_sig)
          hence "\<sigma>' A = the (\<tau> 0 A)"
            by (smt \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 =
            post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> 1\<close> \<sigma>'_def comp_apply
            next_state_def not_one_less_zero ntime override_on_def post_raw_def zero_neq_one)
          also have "... = signal_of (def A) \<tau> A 0"
            using \<open>A \<in> dom (\<tau> 0)\<close> trans_some_signal_of' by fastforce
          also have "... = signal_of (def A) \<tau> A i"
            apply (rule signal_of_less_ind'[THEN sym])
            by (metis "**" Suc_lessD \<open>Suc i < next_time 0 \<tau>''\<close> fun_upd_apply insert_iff
            le_less_trans not_less_eq t'_def') auto
          finally have "\<sigma>' A = signal_of (def A) \<tau> A i"
            by auto }
        ultimately have "\<sigma>' A = signal_of (def A) \<tau> A i"
          by auto
        have "B \<in> dom (?\<tau>' 0) \<or> B \<notin> dom (?\<tau>' 0)"
          by auto
        moreover
        { assume "B \<notin> dom (?\<tau>' 0)"
          hence "B \<notin> dom (\<tau> 0)"
            by (metis domIff sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
          have "\<sigma>' B = def B"
            using * \<open>B \<notin> dom (?\<tau>' 0)\<close> unfolding Let_def 
            using \<open>?\<tau>' = post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> 1\<close> by auto
          also have "... = signal_of (def B) \<tau> B 0"
            using `B \<notin> dom (?\<tau>' 0)` 
            by (metis \<open>B \<notin> dom (\<tau> 0)\<close> domIff signal_of_zero zero_option_def)
          also have "... = signal_of (def B) \<tau> B i"
            apply (rule signal_of_less_ind'[THEN sym])
            by (metis (mono_tags, hide_lams) "**"  Suc_lessD \<open>Suc i < next_time 0 \<tau>''\<close> 
             ex_least_nat_le fun_upd_apply insert_iff le_less_trans
             not_less_zero t'_def' ) auto
          finally have "\<sigma>' B = signal_of (def B) \<tau> B i"
            by auto }
        moreover
        { assume "B \<in> dom (?\<tau>' 0)"
          hence "B \<in> dom (\<tau> 0)"
            by (metis domIff sig.distinct(5) to_trans_raw_sig_def trans_post_raw_diff_sig)
          hence "\<sigma>' B = the (\<tau> 0 B)"
            by (smt \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 =
            post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) \<tau> 1\<close> \<sigma>'_def comp_apply
            next_state_def not_one_less_zero ntime override_on_def post_raw_def zero_neq_one)
          also have "... = signal_of (def B) \<tau> B 0"
            using \<open>B \<in> dom (\<tau> 0)\<close> trans_some_signal_of' by fastforce
          also have "... = signal_of (def B) \<tau> B i"
            apply (rule signal_of_less_ind'[THEN sym])
            by (metis "**" Suc_lessD \<open>Suc i < next_time 0 \<tau>''\<close> fun_upd_apply insert_iff
            le_less_trans not_less_eq t'_def') auto
          finally have "\<sigma>' B = signal_of (def B) \<tau> B i"
            by auto }
        ultimately have "\<sigma>' B = signal_of (def B) \<tau> B i"
          by auto        
        have ?thesis
          using \<open>\<sigma>' A = signal_of (def A) \<tau> A i\<close> \<open>\<sigma>' B = signal_of (def B) \<tau> B i\<close> \<open>\<sigma>' C = Bv (\<not>
          (bval_of (\<sigma>' A) \<and> bval_of (\<sigma>' B)))\<close> \<open>get_state res = \<sigma>'\<close> by auto }
      ultimately show ?thesis 
        by auto        
    next
      case False
      hence "\<tau>'' = ?\<tau>' (t' := 0)"
        using cyc 
        by (metis conc_cases(1) disjnt_empty1 disjnt_insert1 nand3_def)
      hence "next_time 0 \<tau>'' = 1"
        by (smt Suc_lessI \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0
        1 1 C = Some (Bv (\<not> (bval_of (def A) \<and> bval_of (def B))))\<close> cyc fun_upd_same fun_upd_triv
        fun_upd_twist le_zero_eq less_Suc_eq less_one next_time_at_least2 not_gr_zero
        option.simps(3) t'_def' t_strictly_increasing zero_fun_def zero_option_def)
      hence "False"
        using \<open>Suc i < next_time 0 \<tau>''\<close> by linarith
      thus ?thesis
        by auto
    qed }
    ultimately have ?thesis
      by auto }
  moreover
  { assume "Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) = def C"
    hence "\<not> post_necessary_raw 0 \<tau> 0 C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C)"
      by (metis add.left_neutral assms(2) signal_of_zero to_trans_raw_sig_def zero_fun_def)
    hence "?\<tau>' = preempt_raw C \<tau> 1"
      unfolding trans_post_raw_def by auto
    also have "... = \<tau>"
    proof (rule, rule)
      fix time sig
      have "sig = C \<or> sig \<noteq> C"
        by auto
      moreover
      { assume "sig = C"
        hence "preempt_raw C \<tau> 1 time C = None"
          unfolding preempt_raw_def
          by (metis (full_types) assms(2) fun_upd_idem_iff to_trans_raw_sig_def zero_fun_def zero_option_def)
        also have "... = \<tau> time C"
          using assms(2) unfolding to_trans_raw_sig_def  by (metis zero_map)
        finally have "preempt_raw C \<tau> 1 time sig = \<tau> time sig"
          using `sig = C` by auto }
      moreover
      { assume "sig \<noteq> C"
        hence "preempt_raw C \<tau> 1 time sig = \<tau> time sig"
          unfolding preempt_raw_def by auto }
      ultimately show "preempt_raw C \<tau> 1 time sig = \<tau> time sig"
        by auto
    qed
    finally have "?\<tau>' = \<tau>"
      by auto
    hence bigstep: "(Suc i),
           next_time 0 \<tau> ,
           next_state 0 \<tau> def ,
           next_event 0 \<tau> def ,
           add_to_beh def 0 0 (next_time 0 \<tau>), def
        \<turnstile> <nand3 , \<tau>(next_time 0 \<tau> := 0)> \<leadsto> res"
      using bsimulate_obt_big_step[OF assms(1) `init' 0 def {} 0 def nand3 \<tau> ?\<tau>'`] `?\<tau>' = \<tau>` by auto
    have s1: "\<And>n. n \<le> next_time 0 \<tau> \<Longrightarrow> (\<tau>(next_time 0 \<tau> := 0)) n = 0"
      by (simp add: nat_less_le next_time_at_least2)
    have s2: "\<And>s. s \<in> dom ((\<tau>(next_time 0 \<tau> := 0)) (next_time 0 \<tau>)) \<Longrightarrow>
                              next_state 0 \<tau> def s = the ((\<tau>(next_time 0 \<tau> := 0)) (next_time 0 \<tau>) s)"
      by (simp add: zero_fun_def zero_option_def)
    have s3: "\<And>n. next_time 0 \<tau> \<le> n \<Longrightarrow> add_to_beh def 0 0 (next_time 0 \<tau>) n = 0"
      by (simp add: add_to_beh_def zero_fun_def)
    have s4: "A \<notin> next_event 0 \<tau> def \<and> B \<notin> next_event 0 \<tau> def \<Longrightarrow>
              bval_of (next_state 0 \<tau> def C) = (\<not> (bval_of (next_state 0 \<tau> def A) \<and> bval_of (next_state 0 \<tau> def B)))"
      by (smt One_nat_def Suc_leI \<open>Bv (\<not> (bval_of (def A) \<and> bval_of (def B))) = def C\<close> \<open>\<not>
      post_necessary_raw 0 \<tau> 0 C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C)\<close>
      \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 = \<tau>\<close>
      \<open>trans_post_raw C (Bv (\<not> (bval_of (def A) \<and> bval_of (def B)))) (def C) \<tau> 0 1 = preempt_raw C \<tau>
      1\<close> add.left_neutral domD domIff fun_upd_idem_iff le0 nat_less_le next_state_def
      next_state_fixed_point o_apply option.sel override_on_def preempt_raw_def
      trans_some_signal_of' val.sel(1))
    have s5: "\<And>n. next_time 0 \<tau> < n \<Longrightarrow> to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0)) C n = 0"
      by (metis assms(2) fun_upd_apply to_trans_raw_sig_def zero_fun_def)
    have "styping \<Gamma> (next_state 0 \<tau> def)"
      by (simp add: assms(4) assms(6) next_state_preserve_styping)
    have "ttyping \<Gamma> (add_to_beh def 0 0 (next_time 0 \<tau>))"
      by (metis add_to_beh_preserve_type_correctness assms(4) bot_nat_def domIff dom_def ttyping_def
      zero_fun_def zero_option_def)
    have "ttyping \<Gamma> (\<tau>(next_time 0 \<tau> := 0))"
      by (simp add: assms(6) ttyping_rem_curr_trans)
    hence * : "next_time 0 \<tau> \<le> i \<Longrightarrow>
               bval_of (get_state res C) =
           (\<not> (bval_of (signal_of (next_state 0 \<tau> def A) (\<tau>(next_time 0 \<tau> := 0)) A i) \<and>
               bval_of (signal_of (next_state 0 \<tau> def B) (\<tau>(next_time 0 \<tau> := 0)) B i)))"
      using nand3_correctness_ind[OF bigstep _ _ s1 s2 s3 _ s4 s5 `conc_wt \<Gamma> nand3` `styping \<Gamma> (next_state 0 \<tau> def)`
       `ttyping \<Gamma> (add_to_beh def 0 0 (next_time 0 \<tau>))` `ttyping \<Gamma> (\<tau>(next_time 0 \<tau> := 0))` `\<Gamma> C = Bty` `styping \<Gamma> def`]
      by metis
    moreover have "next_time 0 \<tau> \<le> i \<Longrightarrow> signal_of (next_state 0 \<tau> def A) (\<tau>(next_time 0 \<tau> := 0)) A i = signal_of (def A) \<tau> A i"
    proof (cases "inf_time (to_trans_raw_sig \<tau>) A i = None")
      assume "next_time 0 \<tau> \<le> i"
      case True
      hence "signal_of (def A) \<tau> A i = def A"
        by (metis inf_time_noneE2 signal_of_def to_trans_raw_sig_def)
      have "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) A i= None"
        using True  by (metis inf_time_rem_curr_trans option.simps(3) rem_curr_trans_to_trans_raw_sig)
      hence "signal_of (next_state 0 \<tau> def A) (\<tau>(next_time 0 \<tau>:= 0)) A i = next_state 0 \<tau> def A"
        by (metis inf_time_noneE2 signal_of_def to_trans_raw_sig_def)
      have "\<tau> (next_time 0 \<tau>) A = None"
        using True `next_time 0 \<tau> \<le> i`
        by (metis inf_time_noneE2 to_trans_raw_sig_def zero_option_def)
      hence "next_state 0 \<tau> def A = def A"
        unfolding next_state_def Let_def
        by (simp add: domIff)
      thus ?thesis
        using \<open>signal_of (def A) \<tau> A i = def A\<close> \<open>signal_of (next_state 0 \<tau> def A) (\<tau>(next_time 0 \<tau>
        := 0)) A i = next_state 0 \<tau> def A\<close> by auto
    next
      assume "next_time 0 \<tau> \<le> i"
      case False
      then obtain ta where infA: "inf_time (to_trans_raw_sig \<tau>) A i = Some ta"
        by auto
      hence "\<tau> ta A \<noteq> None"
        by (metis Femto_VHDL_raw.keys_def domIff dom_def inf_time_some_exists to_trans_raw_sig_def
        zero_option_def)
      hence "next_time 0 \<tau> \<le> ta"
        by (metis next_time_at_least2 not_le zero_map)
      have "signal_of (def A) \<tau> A i = the (\<tau> ta A)"
        using infA unfolding to_signal_def comp_def to_trans_raw_sig_def by auto
      have "next_time 0 \<tau> = ta \<or> next_time 0 \<tau> < ta"
        using `next_time 0 \<tau> \<le> ta` by auto
      moreover
      { assume "next_time 0 \<tau> = ta"
        hence "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) A i = None"
          using infA
          by (metis inf_time_rem_curr_trans_at_t next_time_at_least2 rem_curr_trans_to_trans_raw_sig
          to_trans_raw_sig_def zero_fun_def zero_option_def)
        hence "signal_of (next_state 0 \<tau> def A) (\<tau>(next_time 0 \<tau> := 0)) A i = next_state 0 \<tau> def A"
          unfolding to_signal_def comp_def by auto
        also have "... = the (\<tau> ta A)"
          unfolding next_state_def Let_def comp_def `next_time 0 \<tau> = ta`
          by (simp add: \<open>\<tau> ta A \<noteq> None\<close> domIff)
        also have "... = signal_of (def A) \<tau> A i"
          using \<open>signal_of (def A) \<tau> A i = the (\<tau> ta A)\<close> by auto
        finally have ?thesis
          by auto }
      moreover
      { assume "next_time 0 \<tau> < ta"
        hence "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) A i = Some ta"
          using infA
          by (metis inf_time_rem_curr_trans nat_less_le option.inject rem_curr_trans_to_trans_raw_sig)
        hence ?thesis
          by (metis \<open>signal_of (def A) \<tau> A i = the (\<tau> ta A)\<close> calculation(2) fun_upd_apply o_def
          option.case(2) to_signal_def to_trans_raw_sig_def) }
      ultimately show ?thesis
        by auto
    qed
    moreover have "next_time 0 \<tau> \<le> i \<Longrightarrow> signal_of (next_state 0 \<tau> def B) (\<tau>(next_time 0 \<tau> := 0)) B i = signal_of (def B) \<tau> B i"
    proof (cases "inf_time (to_trans_raw_sig \<tau>) B i = None")
      assume "next_time 0 \<tau> \<le> i"
      case True
      hence "signal_of (def B) \<tau> B i = def B"
        by (metis inf_time_noneE2 signal_of_def to_trans_raw_sig_def)
      have "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) B i= None"
        using True  by (metis inf_time_rem_curr_trans option.simps(3) rem_curr_trans_to_trans_raw_sig)
      hence "signal_of (next_state 0 \<tau> def B) (\<tau>(next_time 0 \<tau>:= 0)) B i = next_state 0 \<tau> def B"
        by (metis inf_time_noneE2 signal_of_def to_trans_raw_sig_def)
      have "\<tau> (next_time 0 \<tau>) B = None"
        using True `next_time 0 \<tau> \<le> i`
        by (metis inf_time_noneE2 to_trans_raw_sig_def zero_option_def)
      hence "next_state 0 \<tau> def B = def B"
        unfolding next_state_def Let_def
        by (simp add: domIff)
      thus ?thesis
        using \<open>signal_of (def B) \<tau> B i = def B\<close> \<open>signal_of (next_state 0 \<tau> def B) (\<tau>(next_time 0 \<tau>
        := 0)) B i = next_state 0 \<tau> def B\<close> by auto
    next
      assume "next_time 0 \<tau> \<le> i"
      case False
      then obtain ta where infB: "inf_time (to_trans_raw_sig \<tau>) B i = Some ta"
        by auto
      hence "\<tau> ta B \<noteq> None"
        by (metis Femto_VHDL_raw.keys_def domIff dom_def inf_time_some_exists to_trans_raw_sig_def
        zero_option_def)
      hence "next_time 0 \<tau> \<le> ta"
        by (metis next_time_at_least2 not_le zero_map)
      have "signal_of (def B) \<tau> B i = the (\<tau> ta B)"
        using infB unfolding to_signal_def comp_def to_trans_raw_sig_def by auto
      have "next_time 0 \<tau> = ta \<or> next_time 0 \<tau> < ta"
        using `next_time 0 \<tau> \<le> ta` by auto
      moreover
      { assume "next_time 0 \<tau> = ta"
        hence "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) B i = None"
          using infB
          by (metis inf_time_rem_curr_trans_at_t next_time_at_least2 rem_curr_trans_to_trans_raw_sig
          to_trans_raw_sig_def zero_fun_def zero_option_def)
        hence "signal_of (next_state 0 \<tau> def B) (\<tau>(next_time 0 \<tau> := 0)) B i = next_state 0 \<tau> def B"
          unfolding to_signal_def comp_def by auto
        also have "... = the (\<tau> ta B)"
          unfolding next_state_def Let_def comp_def `next_time 0 \<tau> = ta`
          by (simp add: \<open>\<tau> ta B \<noteq> None\<close> domIff)
        also have "... = signal_of (def B) \<tau> B i"
          using \<open>signal_of (def B) \<tau> B i = the (\<tau> ta B)\<close> by auto
        finally have ?thesis
          by auto }
      moreover
      { assume "next_time 0 \<tau> < ta"
        hence "inf_time (to_trans_raw_sig (\<tau>(next_time 0 \<tau> := 0))) B i = Some ta"
          using infB
          by (metis inf_time_rem_curr_trans nat_less_le option.inject rem_curr_trans_to_trans_raw_sig)
        hence ?thesis
          by (metis \<open>signal_of (def B) \<tau> B i = the (\<tau> ta B)\<close> calculation(2) fun_upd_apply o_def
          option.case(2) to_signal_def to_trans_raw_sig_def) }
      ultimately show ?thesis
        by auto
    qed
    ultimately have IR: "next_time 0 \<tau> \<le> i \<Longrightarrow> bval_of (get_state res C) =
           (\<not> (bval_of (signal_of (def A) \<tau> A i) \<and>  bval_of (signal_of (def B) \<tau> B i)))"
      by auto
    hence ?thesis
      using IR by (metis (no_types, hide_lams) False le0 neq0_conv next_time_at_least2) }
  ultimately show ?thesis
    by auto 
qed

end