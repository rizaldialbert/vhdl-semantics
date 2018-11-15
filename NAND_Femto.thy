(*
 * Copyright 2018, NTU
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
  "trans_post sig v empty_trans t = Poly_Mapping.update t [sig \<mapsto> v] empty_trans"
proof transfer'
  fix sig v t
  show "trans_post_raw sig v (\<lambda>k. 0) t = (\<lambda>k. 0)(t := [sig \<mapsto> v]) "
    unfolding trans_post_raw_def zero_upd zero_map fun_upd_def
    by (auto)
qed

lemma get_trans_trans_upd_cancel:
  "get_trans (Poly_Mapping.update n [sig \<mapsto> v] \<tau>) n = [sig \<mapsto> v]"
  by (transfer) (auto)

lemma is_stable_empty_trans:
  "is_stable n empty_trans now sig v"
  unfolding is_stable_correct
  by (auto simp add:zero_map)

definition nand :: "sig conc_stmt" where
  "nand = process {A, B} : Bassign_inert C (Bnand (Bsig A) (Bsig B)) 1"

theorem
  assumes "10, 0, def_state, {A}, 0 \<turnstile> <nand, empty_trans> \<leadsto> beh"
  shows "get_trans beh 1 C = Some True"
  using assms
proof (cases)
  case (1 \<tau>')
  have base: "0 , def_state , {A} , 0 \<turnstile> <nand , rem_curr_trans 0 empty_trans> \<longrightarrow>\<^sub>c
                                                                         (Poly_Mapping.update 1 [C \<mapsto> True] 0)"
    unfolding nand_def by (auto simp add: is_stable_empty_trans inr_post_def  trans_post_empty_trans_upd)
  hence \<tau>'_def: "\<tau>' = (Poly_Mapping.update 1 [C \<mapsto> True] 0)"
    using 1 by auto
  have nt: "next_time 0 \<tau>' = 1"
  proof -
    have "(Poly_Mapping.update 1 [C \<mapsto> True] 0) \<noteq> empty_trans"
      by (transfer, metis fun_upd_same option.simps(3) zero_map)
    moreover have "(LEAST n. dom (get_trans \<tau>' n) \<noteq> {}) = 1"
      unfolding \<tau>'_def
    proof (transfer, rule Least_equality)
      show "dom (((\<lambda>_. 0)(1 := [C \<mapsto> True])) 1) \<noteq> {}"
        by auto
    next
      { fix y :: nat
        assume "\<not> 1 \<le> y"
        hence "y = 0"
          by auto
        hence "dom (((\<lambda>_. 0)(1 := [C \<mapsto> True])) y) = {}"
          by (auto simp add: zero_map)
        hence "\<not> dom (((\<lambda>_. 0)(1 := [C \<mapsto> True])) y) \<noteq> {}"
          by auto }
      thus "\<And>y::nat. dom (((\<lambda>_. 0)(1 := [C \<mapsto> True])) y) \<noteq> {} \<Longrightarrow> 1 \<le> y "
        by fastforce
    qed
    ultimately show ?thesis
      unfolding \<tau>'_def next_time_def by auto
  qed
  have ns: "next_state 0 \<tau>' def_state = def_state (C := True)" (is "?lhs = ?rhs")
    by (metis \<tau>'_def dom_eq_singleton_conv fun_upd_same get_trans_trans_upd_cancel next_state_def nt
              o_apply option.sel override_on_emptyset override_on_insert')
  have ne: "next_event 0 \<tau>' def_state = {C}"
    unfolding nt next_event_def
    by (smt "1"(3) Collect_cong base dom_empty dom_fun_upd fun_upd_comp fun_upd_idem fun_upd_same
            get_trans_trans_upd_cancel insert_absorb insert_iff insert_not_empty map_upd_nonempty
            option.sel singleton_conv)
  have nb: "add_to_beh def_state 0 0 1 =
       Poly_Mapping.update 0 (Some o def_state) 0" (is "_ = ?beh'")
    unfolding add_to_beh_def by auto
  define beh2 :: "(nat \<Rightarrow>\<^sub>0 sig \<Rightarrow> bool option)" where "beh2 = ?beh'"
  hence snd_cyc: "10, 1, def_state (C := True), {C} , beh2 \<turnstile> <nand , \<tau>'> \<leadsto> beh"
    using 1 nt ns ne nb by metis
  thus "get_trans beh 1 C = Some True"
  proof (cases)
    case (1 \<tau>'')
    have t''_def: "\<tau>'' = 0"
      unfolding nand_def
      using 1(3) unfolding nand_def  apply (auto simp add: \<tau>'_def rem_curr_trans_def)
      by (transfer', auto)
    have nt2: "next_time 1 0 = 1"
      by auto
    moreover have "next_state 1 \<tau>'' (def_state(C := True)) = def_state (C := True)"
      unfolding next_state_def Let_def t''_def nt2 by auto
    moreover have "next_event 1 \<tau>'' (def_state(C := True)) = {}"
      unfolding next_event_def Let_def t''_def nt2 by (auto simp add: zero_map)
    moreover have "add_to_beh (def_state(C := True)) beh2 1 (next_time 1 \<tau>'') = beh2"
      unfolding add_to_beh_def t''_def nt2 by (auto simp add: override_coeffs_open_right_same_idx)
    moreover have "rem_curr_trans 1 (Poly_Mapping.update 1 [C \<mapsto> True] empty_trans) = 0"
      unfolding rem_curr_trans_def by (transfer, auto)
    ultimately have "(10, 1, def_state (C := True), {}, beh2 \<turnstile> <nand, \<tau>''> \<leadsto> beh)"
      using 1(4) using t''_def by auto
    then show ?thesis
    proof (cases)
      case (1 \<tau>')
      then show ?thesis unfolding quiet_def t''_def by auto
    next
      case 2
      then show ?thesis unfolding quiet_def t''_def
        by (transfer, auto)
    next
      case 3
      then show ?thesis by auto
    qed
  next
    case 2
    then show ?thesis by (auto simp add:quiet_def)
  next
    case 3
    then show ?thesis by auto
  qed
next
  case 2
  then show ?thesis unfolding quiet_def by auto
next
  case 3
  then show ?thesis by auto
qed

values  "{lookup beh 1 C | beh. b_simulate_fin 10 0 def_state {A} 0 nand empty_trans beh}"

value "get_trans (functional_simulate_fin 10 0 def_state {A} 0 nand empty_trans) 1 C"

theorem
  "get_trans (functional_simulate_fin 10 0 def_state {A} 0 nand empty_trans) 1 C = Some True"
  by eval

value "get_trans (functional_simulate 10 nand) 1 C"

value "signal_of (functional_simulate 10 nand) C 100"

end