(*
 * Copyright 2018-2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Femto_VHDL
  imports Main
          "HOL-Library.Poly_Mapping"
          "HOL-Library.Finite_Map"
          "Polynomials.Poly_Mapping_Finite_Map"
          "Femto_VHDL_raw"
begin

section "Syntax and Semantics"

lemma zero_map:
  "(0 :: 'a \<rightharpoonup> 'b) x = None"
  by (auto simp add:zero_option_def zero_fun_def)

subsection "Operational Semantics"

(* ADD an introduction text *)
type_synonym 'signal transaction = "(nat, 'signal valuation) poly_mapping"

abbreviation empty_trans :: "'signal transaction" where
  "empty_trans \<equiv> 0"

type_synonym 'signal transaction_sig = "'signal \<Rightarrow> nat \<Rightarrow>\<^sub>0 val option"

lift_definition to_transaction_sig :: "'signal transaction \<Rightarrow> 'signal transaction_sig"
  is to_trans_raw_sig
  by (metis (mono_tags, lifting) finite_subset mem_Collect_eq subsetI to_trans_raw_sig_def
  zero_fun_def)

lift_definition to_transaction_sig_bit :: "val \<Rightarrow> 'signal transaction \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> 'signal transaction"
  is to_trans_raw_bit
  unfolding to_trans_raw_bit_def sym[OF eventually_cofinite] zero_fun_def zero_option_def 
  using zero_map
proof -
  fix val
  fix "fun" :: "nat \<Rightarrow> 'signal \<Rightarrow> val option" and nat :: nat and signal :: 'signal
  assume a1: "\<forall>\<^sub>\<infinity>x. fun x = Map.empty"
  obtain nn :: "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat" where
    f2: "\<And>p f pa fa. (\<not> eventually p f \<or> eventually pa f \<or> p (nn p pa)) \<and> (\<not> eventually p fa \<or> \<not> pa (nn p pa) \<or> eventually pa fa)"
    by (metis (no_types) eventually_mono)
  then have f3: "\<And>p. Alm_all p \<or> (\<forall>s. fun (nn (\<lambda>n. \<forall>s. fun n s = None) p) s = None)"
    using a1  by (metis (mono_tags, lifting))
  have f4: "\<And>n. (\<exists>s. fun n s \<noteq> None) \<or> (\<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some (Bv xa) \<Rightarrow> Map.empty xa | Some (Lv s bs) \<Rightarrow> (Some \<circ> Bv) (bs ! nat)) = None))"
    by force
  { assume "(\<forall>\<^sub>\<infinity>n. \<forall>s. fun n s = None) \<and> \<not> (\<forall>\<^sub>\<infinity>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some (Bv xa) \<Rightarrow> Map.empty xa | Some (Lv s bs) \<Rightarrow> (Some \<circ> Bv) (bs ! nat)) = None))"
    then have "\<exists>p. (\<forall>s. (s = signal \<or> fun (nn p (\<lambda>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some (Bv xa) \<Rightarrow> Map.empty xa | Some (Lv s bs) \<Rightarrow> (Some \<circ> Bv) (bs ! nat)) = None))) s = None) \<and> (s \<noteq> signal \<or> (case fun (nn p (\<lambda>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some (Bv xa) \<Rightarrow> Map.empty xa | Some (Lv s bs) \<Rightarrow> (Some \<circ> Bv) (bs ! nat)) = None))) s of None \<Rightarrow> None | Some (Bv xa) \<Rightarrow> Map.empty xa | Some (Lv s bs) \<Rightarrow> (Some \<circ> Bv) (bs ! nat)) = None)) \<and> Alm_all p"
      using f4 f3 by meson
    then have "\<forall>\<^sub>\<infinity>n. (\<lambda>s. if s \<noteq> signal then fun n s else case fun n s of None \<Rightarrow> None | Some (Bv xa) \<Rightarrow> Map.empty xa | Some (Lv s bs) \<Rightarrow> (Some \<circ> Bv) (bs ! nat)) = Map.empty"
      using f2
      by (smt \<open>(\<forall>\<^sub>\<infinity>n. \<forall>s. fun n s = None) \<and> \<not> (\<forall>\<^sub>\<infinity>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some (Bv x) \<Rightarrow> Map.empty x | Some (Lv s bs) \<Rightarrow> (Some \<circ> Bv) (bs ! nat)) = None))\<close>) }
  then show "\<forall>\<^sub>\<infinity>x. (\<lambda>sig. if sig \<noteq> signal then fun x sig
                     else case fun x sig of None \<Rightarrow> None
                          | Some v \<Rightarrow>
                              if 0 < x \<and> to_bit nat (signal_of val fun sig (x - 1)) = to_bit nat v then None
                              else if x = 0 \<and> to_bit nat val = to_bit nat v then None else Some (to_bit nat v)) =
              Map.empty"
  proof -
    have f1: "\<And>p. Alm_all p \<or> (\<forall>s. fun (nn (\<lambda>n. \<forall>s. fun n s = None) p) s = None)"
      by (simp add: f3)
    { assume "\<not> (\<forall>\<^sub>\<infinity>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit nat (signal_of val fun s (n - 1)) = to_bit nat v then None else if n = 0 \<and> to_bit nat val = to_bit nat v then None else Some (to_bit nat v)) = None))"
      then have "(\<forall>\<^sub>\<infinity>n. \<forall>s. fun n s = None) \<and> \<not> (\<forall>\<^sub>\<infinity>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit nat (signal_of val fun s (n - 1)) = to_bit nat v then None else if n = 0 \<and> to_bit nat val = to_bit nat v then None else Some (to_bit nat v)) = None))"
        by (metis a1)
      then have "\<exists>p. Alm_all p \<and> (\<forall>s. (s = signal \<or> fun (nn p (\<lambda>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit nat (signal_of val fun s (n - 1)) = to_bit nat v then None else if n = 0 \<and> to_bit nat val = to_bit nat v then None else Some (to_bit nat v)) = None))) s = None) \<and> (s \<noteq> signal \<or> (case fun (nn p (\<lambda>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit nat (signal_of val fun s (n - 1)) = to_bit nat v then None else if n = 0 \<and> to_bit nat val = to_bit nat v then None else Some (to_bit nat v)) = None))) s of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < nn p (\<lambda>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit nat (signal_of val fun s (n - 1)) = to_bit nat v then None else if n = 0 \<and> to_bit nat val = to_bit nat v then None else Some (to_bit nat v)) = None)) \<and> to_bit nat (signal_of val fun s (nn p (\<lambda>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit nat (signal_of val fun s (n - 1)) = to_bit nat v then None else if n = 0 \<and> to_bit nat val = to_bit nat v then None else Some (to_bit nat v)) = None)) - 1)) = to_bit nat v then None else if nn p (\<lambda>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit nat (signal_of val fun s (n - 1)) = to_bit nat v then None else if n = 0 \<and> to_bit nat val = to_bit nat v then None else Some (to_bit nat v)) = None)) = 0 \<and> to_bit nat val = to_bit nat v then None else Some (to_bit nat v)) = None))"
        using f1 by fastforce
      then have ?thesis
        by (smt MOST_mono \<open>(\<forall>\<^sub>\<infinity>n. \<forall>s. fun n s = None) \<and> \<not> (\<forall>\<^sub>\<infinity>n. \<forall>s. (s \<noteq> signal \<longrightarrow> fun n s = None) \<and> (s = signal \<longrightarrow> (case fun n s of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit nat (signal_of val fun s (n - 1)) = to_bit nat v then None else if n = 0 \<and> to_bit nat val = to_bit nat v then None else Some (to_bit nat v)) = None))\<close> option.simps(4)) }
    then show ?thesis
      by meson
  qed
qed

lemma finite_keys_to_transaction_sig:
  "finite (Poly_Mapping.keys (to_transaction_sig \<tau> s))"
  by auto

subsection \<open>From transaction to function of time (signal)\<close>

lemma list_split3:
  assumes "sorted xs" and "distinct xs" and "xs \<noteq> []"
  assumes "hd xs \<le> x" and "x < last xs"
  shows "\<exists>ys y zs. xs = ys @ y # zs \<and> (\<forall>k \<in> set ys. k \<le> x) \<and> x < y"
proof -
  obtain ys where "takeWhile (\<lambda>n. n \<le> x) xs = ys"
    by auto
  moreover obtain y zs where "dropWhile (\<lambda>n. n \<le> x) xs = y # zs"
    by (metis append_Nil2 assms(3) assms(5) last_in_set le_less not_less_iff_gr_or_eq set_takeWhileD
        sorted.cases takeWhile_dropWhile_id)
  ultimately have "xs = ys @ y # zs \<and> x < y"
    using dropWhile_eq_Cons_conv by fastforce
  moreover have "(\<forall>k\<in>set ys. k \<le> x)"
    using `takeWhile (\<lambda>n. n \<le> x) xs = ys`  by (meson set_takeWhileD)
  ultimately show ?thesis
    by auto
qed

lemma takeWhile_last:
  fixes maxtime :: nat
  assumes "sorted ys" and "ys \<noteq> []" and "last ys \<le> maxtime"
  shows "takeWhile (\<lambda>k. k \<le> maxtime) ys = ys"
  unfolding takeWhile_eq_all_conv
proof
  fix k
  assume "k \<in> set ys"
  hence "k \<le> last ys"
    using `sorted ys` `ys \<noteq> []`
    by (metis insertE last_appendR last_in_set less_or_eq_imp_le list.distinct(1) list.set(2)
        sorted.simps(2) sorted_append split_list)
  thus "k \<le> maxtime"
    using assms by auto
qed

lemma takeWhile_last_strict:
  fixes maxtime :: nat
  assumes "sorted ys" and "ys \<noteq> []" and "last ys < maxtime"
  shows "takeWhile (\<lambda>k. k < maxtime) ys = ys"
  using assms
  by (metis nat_less_le not_less takeWhile_eq_all_conv takeWhile_last)

fun inf_key :: "nat list \<Rightarrow> nat \<Rightarrow> nat option" where
  "inf_key ks n = (case takeWhile (\<lambda>k. k \<le> n) ks of [] \<Rightarrow> None | ks' \<Rightarrow> Some (last ks'))"

lemma inf_key_alt_def:
  assumes "sorted (a # ks)"
  shows "inf_key (a # ks) n = (if a \<le> n \<and> inf_key ks n = None then Some a else inf_key ks n)"
proof -
  have "a \<le> n \<or> n < a" by auto
  moreover
  { assume "a \<le> n"
    hence "takeWhile (\<lambda>k. k \<le> n) (a # ks) = a # takeWhile (\<lambda>k. k \<le> n) ks"
      by auto
    hence "inf_key (a # ks) n =
                         (case a # takeWhile (\<lambda>k. k \<le> n) ks of [] \<Rightarrow> None | ks' \<Rightarrow> Some (last ks'))"
      by auto
    also have "... =
        (if takeWhile (\<lambda>k. k \<le> n) ks = [] then Some a else Some (last (takeWhile (\<lambda>k. k \<le> n) ks)))"
      by auto
    also have "... = (if inf_key ks n = None then Some a else inf_key ks n)"
      by (auto split:list.splits)
    finally have "inf_key (a # ks) n = (if inf_key ks n = None then Some a else inf_key ks n)"
      by auto
    hence ?thesis using `a \<le> n` by auto }
  moreover
  { assume "n < a"
    hence "takeWhile (\<lambda>k. k \<le> n) (a # ks) = []"
      by auto
    hence "inf_key (a # ks) n = None"
      by auto
    moreover have "inf_key ks n = None"
      using `sorted (a # ks)`
      by (metis \<open>n < a\<close> inf_key.simps list.simps(4) neq_Nil_conv not_le order.strict_trans2 sorted2
          takeWhile.simps(1) takeWhile.simps(2))
    ultimately have ?thesis using `n < a` by auto }
  ultimately show ?thesis by auto
qed

lift_definition inf_time :: "'a transaction_sig \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat option" is
  Femto_VHDL_raw.inf_time .

lemma dropWhileD2:
  assumes "sorted xs" and "distinct xs"
  shows "x \<in> set (dropWhile (\<lambda>k. k \<le> n) xs) \<Longrightarrow> n < x"
  using assms
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have "a \<le> n \<or> n < a"
    by auto
  moreover
  { assume "a \<le> n"
    hence "dropWhile (\<lambda>k. k \<le> n) (a # xs) = dropWhile (\<lambda>k. k \<le> n) xs"
      by auto
    with Cons have ?case
      by auto }
  moreover
  { assume "n < a"
    hence "dropWhile (\<lambda>k. k \<le> n) (a # xs) = a # xs"
      by auto
    hence "x \<in> set (a # xs)"
      using Cons by auto
    with Cons have ?case
      using \<open>n < a\<close> order.strict_trans2 by auto }
  ultimately show ?case by auto
qed

lemma inf_time_inf_key [code]:
  "inf_time \<tau> sig n = inf_key (sorted_list_of_set (Poly_Mapping.keys (\<tau> sig))) n"
proof transfer
  fix \<tau> :: "'a \<Rightarrow> nat \<Rightarrow> val option"
  fix sig
  fix n
  assume "pred_fun top (\<lambda>f. finite {x. f x \<noteq> 0}) \<tau>"
  hence "finite {k. \<tau> sig k \<noteq> 0}"
    unfolding pred_fun_def by auto
  define ks where "ks = sorted_list_of_set {k. \<tau> sig k \<noteq> 0}"
  have "(\<exists>k\<in> keys(\<tau> sig). k \<le> n) \<or> \<not> (\<exists>k\<in> keys(\<tau> sig). k \<le> n)"
    by auto
  moreover
  { assume not: "\<not> (\<exists>k\<in> keys(\<tau> sig). k \<le> n)"
    have "takeWhile (\<lambda>k. k \<le> n) ks = []"
      using ks_def unfolding keys_def
      by (induction ks, simp)
         (metis Femto_VHDL_raw.keys_def \<open>finite {k. \<tau> sig k \<noteq> 0}\<close> insertI1 list.simps(15) not
         set_sorted_list_of_set takeWhile.simps(2))
    hence "inf_key ks n = None"
      by (simp add: ks_def)
    also have "... = Femto_VHDL_raw.inf_time \<tau> sig n"
      by (auto simp add: not Femto_VHDL_raw.inf_time_def)
    finally have "Femto_VHDL_raw.inf_time \<tau> sig n = inf_key ks n"
      by auto }
  moreover
  { assume exi: "\<exists>k\<in> keys(\<tau> sig). k \<le> n"
    hence *: "Femto_VHDL_raw.inf_time \<tau> sig n = Some (GREATEST k. k \<in> keys (\<tau> sig) \<and> k \<le> n)"
      by (auto simp add: Femto_VHDL_raw.inf_time_def)
    have "ks \<noteq> []"
      using exi by (auto simp add: \<open>finite {k. \<tau> sig k \<noteq> 0}\<close> ks_def keys_def)
    hence "takeWhile (\<lambda>k. k \<le> n) ks \<noteq> []"
      using ks_def exi unfolding keys_def
    proof (induction ks)
      case (Cons a ks)
      have "a \<le> n \<or> n < a"
        by auto
      moreover
      { assume "a \<le> n"
        hence "takeWhile (\<lambda>k. k \<le> n) (a # ks) = a # takeWhile (\<lambda>k. k \<le> n) ks"
          by auto
        hence ?case
          by auto }
      moreover
      { assume "n < a"
        with Cons.prems have "\<tau> sig a \<noteq> 0"
          by (metis \<open>finite {k. \<tau> sig k \<noteq> 0}\<close> domIff dom_def insertI1 list.simps(15)
          set_sorted_list_of_set zero_option_def)
        have "sorted (a # ks)" and "distinct (a # ks)"
          using Cons.prems(2) by auto
        hence "\<forall>k' \<in> set ks. a < k'"
          using nat_less_le by auto
        with `n < a` have "\<forall>k' \<in> set (a # ks). n < k'"
          by auto
        with Cons have "False"
          using \<open>finite {k. \<tau> sig k \<noteq> 0}\<close> by auto
        hence ?case by auto }
      ultimately show ?case by auto
    qed (auto)
    define ks' where "ks' = takeWhile (\<lambda>k. k \<le> n) ks"
    hence "ks' \<noteq> []"
      using `takeWhile (\<lambda>k. k \<le> n) ks \<noteq> []` by auto
    have "(GREATEST k. k \<in> keys (\<tau> sig) \<and> k \<le> n) = last ks'"
    proof (rule Greatest_equality)
      have "last ks' \<in> Femto_VHDL_raw.keys (\<tau> sig)"
        using `ks' \<noteq> []` unfolding keys_def ks'_def ks_def
        by (metis \<open>finite {k. \<tau> sig k \<noteq> 0}\<close> last_in_set set_sorted_list_of_set set_takeWhileD)
      moreover have "last ks' \<le> n"
        using `ks' \<noteq> []` unfolding ks'_def  by (meson last_in_set set_takeWhileD)
      ultimately show "last ks' \<in> Femto_VHDL_raw.keys (\<tau> sig) \<and> last ks' \<le> n"
        by auto
    next
      { fix y
        assume "\<not> y \<le> last ks'" hence "last ks' < y" by auto
        have "y \<in> set ks \<or> y \<notin> set ks"
          by auto
        moreover
        { assume "y \<notin> set ks"
          hence "y \<notin> Femto_VHDL_raw.keys (\<tau> sig)"
            unfolding keys_def ks_def by (simp add: \<open>finite {k. \<tau> sig k \<noteq> 0}\<close>)
          hence "\<not> (y \<in> Femto_VHDL_raw.keys (\<tau> sig) \<and> y \<le> n)"
            by auto }
        moreover
        { assume "y \<in> set ks"
          hence "y \<in> set (takeWhile (\<lambda>k. k \<le> n) ks) \<or> y \<in> set (dropWhile (\<lambda>k. k \<le> n) ks)"
            by (metis Un_iff set_append takeWhile_dropWhile_id)
          moreover
          { assume "y \<in> set (dropWhile (\<lambda>k. k \<le> n) ks)"
            hence "n < y"
              using dropWhileD2 distinct_sorted_list_of_set ks_def sorted_sorted_list_of_set
              by blast
            hence "\<not> (y \<in> Femto_VHDL_raw.keys (\<tau> sig) \<and> y \<le> n)"
              by auto }
          moreover
          { assume "y \<in> set (takeWhile (\<lambda>k. k \<le> n) ks)"
            hence "y \<le> last ks'"
              using `ks' \<noteq> []`
              by (metis ks'_def ks_def linorder_not_le order_refl sorted_list_of_set(2)
              sorted_takeWhile takeWhile_eq_all_conv takeWhile_last_strict)
            with `last ks' < y` have False by auto
            hence "\<not> (y \<in> Femto_VHDL_raw.keys (\<tau> sig) \<and> y \<le> n)"
              by auto }
          ultimately have "\<not> (y \<in> Femto_VHDL_raw.keys (\<tau> sig) \<and> y \<le> n)"
            by auto }
        ultimately have "\<not> (y \<in> Femto_VHDL_raw.keys (\<tau> sig) \<and> y \<le> n)"
          by auto }
      thus "\<And>y. y \<in> Femto_VHDL_raw.keys (\<tau> sig) \<and> y \<le> n \<Longrightarrow> y \<le> last ks'"
        by auto
    qed
    moreover have "inf_key ks n = Some (last ks')"
    proof -
      obtain x xs where "ks' = x # xs"
        using `ks' \<noteq> []`  by (meson neq_Nil_conv)
      hence "inf_key ks n = Some (last (x # xs))"
        using `ks' \<noteq>[]` unfolding ks'_def by auto
      thus ?thesis
        using `ks' = x # xs` by auto
    qed
    ultimately have "Femto_VHDL_raw.inf_time \<tau> sig n = inf_key ks n"
      using * by auto }
  ultimately show "Femto_VHDL_raw.inf_time \<tau> sig n = inf_key ks n"
    by auto
qed

lift_definition to_signal :: "val \<Rightarrow> 'signal transaction_sig \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val" is
  Femto_VHDL_raw.to_signal .

lemma [code]:
  "to_signal def \<tau> sig t = (case inf_time \<tau> sig t of
                              None    \<Rightarrow> def
                            | Some t' \<Rightarrow> the (lookup (\<tau> sig) t'))"
  by (transfer', auto simp add: Femto_VHDL_raw.to_signal_def)

abbreviation "signal_of2 def \<equiv> to_signal def o to_transaction_sig"

lift_definition beval ::
  "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow> 'signal bexp \<Rightarrow> val \<Rightarrow> bool"
  is beval_raw .

inductive beval_ind :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow> 'signal bexp \<Rightarrow> val \<Rightarrow> bool"
  where
  "beval_ind now \<sigma> \<gamma> \<theta> def (Bsig sig) (\<sigma> sig)"
| "beval_ind now \<sigma> \<gamma> \<theta> def (Btrue) (Bv True)"
| "beval_ind now \<sigma> \<gamma> \<theta> def (Bfalse) (Bv False)"
| "beval_ind now \<sigma> \<gamma> \<theta> def (Bsig_delayed sig t) (signal_of2 (def sig) \<theta> sig (now - t))"
| "beval_ind now \<sigma> \<gamma> \<theta> def (Bsig_event sig) (Bv (sig \<in> \<gamma>))"
| "beval_ind now \<sigma> \<gamma> \<theta> def e (Bv bool) \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def (Bnot e) (Bv (\<not> bool))"
| "beval_ind now \<sigma> \<gamma> \<theta> def e (Lv ki bs) \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def (Bnot e) (Lv ki (map Not bs))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1 (Bv val1); beval_ind now \<sigma> \<gamma> \<theta> def e2 (Bv val2)\<rbrakk> \<Longrightarrow>
                                           beval_ind now \<sigma> \<gamma> \<theta> def (Band e1 e2) (Bv ( val1 \<and> val2))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1 (Lv ki bs1); beval_ind now \<sigma> \<gamma> \<theta> def e2 (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                                  \<Longrightarrow>  beval_ind now \<sigma> \<gamma> \<theta> def (Band e1 e2) (Lv ki (map2 (\<and>) bs1 bs2))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1 (Bv val1); beval_ind now \<sigma> \<gamma> \<theta> def e2 (Bv val2)\<rbrakk> \<Longrightarrow>
                                            beval_ind now \<sigma> \<gamma> \<theta> def (Bor e1 e2) (Bv ( val1 \<or> val2))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1 (Lv ki bs1); beval_ind now \<sigma> \<gamma> \<theta> def e2 (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                                   \<Longrightarrow>  beval_ind now \<sigma> \<gamma> \<theta> def (Bor e1 e2) (Lv ki (map2 (\<or>) bs1 bs2))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1 (Bv val1); beval_ind now \<sigma> \<gamma> \<theta> def e2 (Bv val2)\<rbrakk> \<Longrightarrow>
                                        beval_ind now \<sigma> \<gamma> \<theta> def (Bnand e1 e2) (Bv (\<not>(val1 \<and> val2)))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1  (Lv ki bs1); beval_ind now \<sigma> \<gamma> \<theta> def e2  (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                    \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def (Bnand e1 e2)  (Lv ki (map2 (\<lambda>x y. \<not> (x \<and> y)) bs1 bs2))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1  (Bv val1); beval_ind now \<sigma> \<gamma> \<theta> def e2  (Bv val2)\<rbrakk> \<Longrightarrow>
                                         beval_ind now \<sigma> \<gamma> \<theta> def (Bnor e1 e2)  (Bv (\<not>(val1 \<or> val2)))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1  (Lv ki bs1); beval_ind now \<sigma> \<gamma> \<theta> def  e2  (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                     \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def (Bnor e1 e2)  (Lv ki (map2 (\<lambda>x y. \<not> (x \<or> y)) bs1 bs2))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1  (Bv val1); beval_ind now \<sigma> \<gamma> \<theta> def e2  (Bv val2)\<rbrakk> \<Longrightarrow>
                                          beval_ind now \<sigma> \<gamma> \<theta> def (Bxor e1 e2)  (Bv (xor val1 val2))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1  (Lv ki bs1); beval_ind now \<sigma> \<gamma> \<theta> def e2  (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                                   \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def (Bxor e1 e2)  (Lv ki (map2 xor bs1 bs2))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1  (Bv val1); beval_ind now \<sigma> \<gamma> \<theta> def e2  (Bv val2)\<rbrakk> \<Longrightarrow>
                                       beval_ind now \<sigma> \<gamma> \<theta> def (Bxnor e1 e2)  (Bv (\<not> xor val1 val2))"
| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e1  (Lv ki bs1); beval_ind now \<sigma> \<gamma> \<theta> def e2  (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                    \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def (Bxnor e1 e2)  (Lv ki (map2 (\<lambda>x y. \<not> xor x y) bs1 bs2))"
| "beval_ind now \<sigma> \<gamma> \<theta> def (Bsig sig) (Lv ki bs) \<Longrightarrow>  length bs = len \<Longrightarrow>
                                    beval_ind now \<sigma> \<gamma> \<theta> def (Bslice sig l r) (Lv ki (nths bs {len - l - 1 .. len - r - 1}))"
| "beval_ind now \<sigma> \<gamma> \<theta> def (Bsig sig) (Lv ki bs) \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def (Bindex sig idx) (Bv (bs ! idx))"

| "beval_ind now \<sigma> \<gamma> \<theta> def e1 (Lv Uns bs1) \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def e2 (Lv Uns bs2) \<Longrightarrow>
   len = max (length bs1) (length bs2) \<Longrightarrow> bs = bin_to_bl len (bl_to_bin bs1 + bl_to_bin bs2) \<Longrightarrow>
   beval_ind now \<sigma> \<gamma> \<theta> def (Badd e1 e2) (Lv Uns bs)"

| "beval_ind now \<sigma> \<gamma> \<theta> def e1 (Lv Sig bs1) \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def e2 (Lv Sig bs2) \<Longrightarrow>
   len = max (length bs1) (length bs2) \<Longrightarrow> bs = bin_to_bl len (sbl_to_bin bs1 + sbl_to_bin bs2) \<Longrightarrow>
   beval_ind now \<sigma> \<gamma> \<theta> def (Badd e1 e2) (Lv Sig bs)"

| "beval_ind now \<sigma> \<gamma> \<theta> def e1 (Lv Uns bs1) \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def e2 (Lv Uns bs2) \<Longrightarrow>
   len = (length bs1) + (length bs2) \<Longrightarrow> bs = bin_to_bl len (bl_to_bin bs1 * bl_to_bin bs2) \<Longrightarrow>
   beval_ind now \<sigma> \<gamma> \<theta> def (Bmult e1 e2) (Lv Uns bs)"

| "beval_ind now \<sigma> \<gamma> \<theta> def e1 (Lv Sig bs1) \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def e2 (Lv Sig bs2) \<Longrightarrow>
   len = (length bs1) + (length bs2) \<Longrightarrow> bs = bin_to_bl len (sbl_to_bin bs1 * sbl_to_bin bs2) \<Longrightarrow>
   beval_ind now \<sigma> \<gamma> \<theta> def (Bmult e1 e2) (Lv Sig bs)"

| "beval_ind now \<sigma> \<gamma> \<theta> def e1 (Lv Uns bs1) \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def e2 (Lv Uns bs2) \<Longrightarrow>
   len = max (length bs1) (length bs2) \<Longrightarrow> bs = bin_to_bl len (bl_to_bin bs1 - bl_to_bin bs2) \<Longrightarrow>
   beval_ind now \<sigma> \<gamma> \<theta> def (Bsub e1 e2) (Lv Uns bs)"

| "beval_ind now \<sigma> \<gamma> \<theta> def e1 (Lv Sig bs1) \<Longrightarrow> beval_ind now \<sigma> \<gamma> \<theta> def e2 (Lv Sig bs2) \<Longrightarrow>
   len = max (length bs1) (length bs2) \<Longrightarrow> bs = bin_to_bl len (sbl_to_bin bs1 - sbl_to_bin bs2) \<Longrightarrow>
   beval_ind now \<sigma> \<gamma> \<theta> def (Bsub e1 e2) (Lv Sig bs)"

| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e (Lv Uns bs);  bs' = drop n (bs @ replicate n False)\<rbrakk>
                                              \<Longrightarrow>  beval_ind now \<sigma> \<gamma> \<theta> def (Bshiftl e n) (Lv Uns bs')"

| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e (Lv Sig bs);  bs' = drop n (bs @ replicate n False)\<rbrakk>
                                              \<Longrightarrow>  beval_ind now \<sigma> \<gamma> \<theta> def (Bshiftl e n) (Lv Sig bs')"

| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e (Lv Uns bs);  bs' = take (length bs) (replicate n False @ bs)\<rbrakk>
                                              \<Longrightarrow>  beval_ind now \<sigma> \<gamma> \<theta> def (Bshiftr e n) (Lv Uns bs')"

| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def e (Lv Sig bs);  bs' = take (length bs) (replicate n (hd bs) @ bs)\<rbrakk>
                                              \<Longrightarrow>  beval_ind now \<sigma> \<gamma> \<theta> def (Bshiftr e n) (Lv Sig bs')"

| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def g (Bv True);  beval_ind now \<sigma> \<gamma> \<theta> def th res\<rbrakk>
                                              \<Longrightarrow>  beval_ind now \<sigma> \<gamma> \<theta> def (Bwhen th g el) res"

| "\<lbrakk>beval_ind now \<sigma> \<gamma> \<theta> def g (Bv False);  beval_ind now \<sigma> \<gamma> \<theta> def el res\<rbrakk>
                                              \<Longrightarrow>  beval_ind now \<sigma> \<gamma> \<theta> def (Bwhen th g el) res"

| "beval_ind now \<sigma> \<gamma> \<theta> def (Bliteral sign val) (Lv sign val)"

lemma beval_eq_beval_ind:
  "beval t \<sigma> \<gamma> \<theta> def exp res = beval_ind t \<sigma> \<gamma> \<theta> def exp res"
proof
  assume "beval t \<sigma> \<gamma> \<theta> def exp res"
  hence "beval_ind t \<sigma> \<gamma> (Abs_poly_mapping (lookup \<theta>)) def exp res"
  proof transfer
    fix t \<sigma> \<gamma>
    fix \<theta> :: "nat \<Rightarrow> 'a \<Rightarrow> val option"
    fix def exp res
    assume "finite {x. \<theta> x \<noteq> 0}"
    assume "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b res"
    thus "beval_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def exp res"
      using `finite {x. \<theta> x \<noteq> 0}`
    proof (induction rule: beval_raw.induct)
      case (4 now \<sigma> \<gamma> \<theta> def sig t)
      have "signal_of2 (def sig) (Abs_poly_mapping \<theta>) sig (now - t) = signal_of (def sig) \<theta> sig (now - t)"
        unfolding Femto_VHDL.to_signal.rep_eq comp_def to_transaction_sig.rep_eq
        lookup_Abs_poly_mapping[OF 4] by auto
      then show ?case by (metis beval_ind.intros(4))
    qed (metis beval_ind.intros)+
  qed
  thus "beval_ind t \<sigma> \<gamma> \<theta> def exp res"
    unfolding lookup_inverse by auto
next
  assume "beval_ind t \<sigma> \<gamma> \<theta> def exp res"
  thus "beval t \<sigma> \<gamma> \<theta> def exp res"
    unfolding beval.rep_eq
  proof (induction rule: beval_ind.inducts)
    case (4 now \<sigma> \<gamma> \<theta> def sig t)
    have "signal_of2 (def sig) \<theta> sig (now - t) = signal_of (def sig) (lookup \<theta>) sig (now - t)"
      by transfer' auto
    then show ?case
      using beval_raw.intros(4) by force
  qed (metis beval_raw.intros)+
qed

lemma beval_ind_deterministic:
  assumes "beval_ind t \<sigma> \<gamma> \<theta> def exp res1"
  assumes "beval_ind t \<sigma> \<gamma> \<theta> def exp res2"
  shows "res2 = res1"
  using assms unfolding sym[OF beval_eq_beval_ind]
  by transfer' (simp add: beval_raw_deterministic)

lift_definition transtyping :: "'s tyenv \<Rightarrow> 's transaction \<Rightarrow> bool" is ttyping .

lemma beval_ind_progress_unique:
  assumes "bexp_wt \<Gamma> exp type" and "styping \<Gamma> \<sigma>" and "transtyping \<Gamma> \<theta>" and "styping \<Gamma> def"
  shows "\<exists>!v. beval_ind t \<sigma> \<gamma> \<theta> def exp v"
  unfolding sym[OF beval_eq_beval_ind] using assms
  by transfer' (auto simp add: beval_raw_progress beval_raw_deterministic)

lift_definition post :: "'signal \<Rightarrow> val \<Rightarrow> 'signal transaction \<Rightarrow> nat \<Rightarrow> 'signal transaction" is
  post_raw unfolding post_raw_def sym[OF eventually_cofinite]
  by (smt MOST_mono MOST_neq(2) MOST_rev_mp fun_upd_idem_iff zero_fun_def zero_option_def)

lift_definition preempt :: "'signal \<Rightarrow> 'signal transaction \<Rightarrow> nat \<Rightarrow> 'signal transaction" is
  preempt_raw unfolding preempt_raw_def sym[OF eventually_cofinite]
  by (smt MOST_mono fun_upd_idem_iff zero_map)

lift_definition post_necessary:: "nat \<Rightarrow> 'signal transaction \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool"
  is post_necessary_raw .

lift_definition trans_post ::
  "'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal transaction \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal transaction"
  is trans_post_raw
  unfolding  sym[OF eventually_cofinite] using trans_post_raw_almost_all_zero
  by metis

lemma [code]:
  "trans_post s val def \<tau> t dly =
  (if post_necessary dly \<tau> t s val def then post s val \<tau> (t + dly) else preempt s \<tau> (t + dly))"
  by (transfer', auto simp add: trans_post_raw_def)

lift_definition purge :: "'signal transaction \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal transaction" is
  purge_raw unfolding purge_raw_def sym[OF eventually_cofinite]
  by (metis purge_raw_almost_all_zero purge_raw_def)

lift_definition purge' :: "'signal transaction \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal transaction" is
  purge_raw' unfolding purge_raw'_def sym[OF eventually_cofinite]
  by (metis (no_types) purge_raw'_def purge_raw_almost_all_zero')

(* TODO: remove the following proof since it  is duplicated from Femto_VHDL_raw.thy *)

lift_definition combine_trans_bit_lifted :: "'signal transaction \<Rightarrow> (val \<times> 'signal transaction) list \<Rightarrow> signedness \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal transaction" is
  combine_trans_bit unfolding combine_trans_bit_def Let_def 
proof -
  fix f :: "nat \<Rightarrow> 'signal \<Rightarrow> val option"
  fix list :: "(val \<times> (nat \<Rightarrow> 'signal \<Rightarrow> val option)) list" 
  fix signedness signal now dly
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) list"
  assume "finite {x. f x \<noteq> 0}"
  hence "\<forall>\<^sub>\<infinity>x. f x = 0"
    unfolding sym[OF eventually_cofinite] by auto
  assume "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) list"  
  have "(\<lambda>x sig. if x \<le> now \<or> now + dly < x \<or> sig \<noteq> signal then f x sig
                 else if x \<in> fold (\<union>) (map (Femto_VHDL_raw.keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> signal) \<circ> snd) list) {}
                 then Some (Lv signedness (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig x)) list)) else None) = 
        (override_on (\<lambda>x. if x \<le> now \<or> now + dly < x then f x else (f x)(signal := None)) 
                     (\<lambda>x. \<lambda>sig. if x \<le> now \<or> now + dly < x \<or> sig \<noteq> signal then f x sig else 
                               Some (Lv signedness (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig x)) list))) 
                     (fold (\<union>) (map (Femto_VHDL_raw.keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> signal) \<circ> snd) list) {}))"
      (is "?fun = ?fun'") by (auto intro!: ext)
  have "finite {x. ?fun' x \<noteq> 0}"
    unfolding sym[OF eventually_cofinite] 
  proof (intro upd_eventually_cofinite_override_on_finite)
    have "\<And>init. finite init \<Longrightarrow> finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) signal k \<noteq> 0}) list) init)"
      using *
    proof (induction list)
      case Nil
      then show ?case by auto
    next
      case (Cons a ps)
      have "pred_prod (\<lambda>a. True) (\<lambda>f. finite {x. f x \<noteq> 0}) a"
        using Cons(3) by auto
      hence "finite {x. snd a x \<noteq> 0}"
        using pred_prod_inject surjective_pairing[of "a"] by metis
      have **: " (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) signal k \<noteq> 0}) (a # ps)) init) = 
             fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) signal k \<noteq> 0}) ps) ({k. to_trans_raw_sig (snd a) signal k \<noteq> 0} \<union> init)"
        unfolding list.map(2) fold_Cons comp_def Un_empty_right by auto
      have "finite  ({k. to_trans_raw_sig (snd a) signal k \<noteq> 0} \<union> init)"
        using `finite init` `finite {x. snd a x \<noteq> 0}` unfolding finite_Un 
        to_trans_raw_sig_def
        by (metis (mono_tags, lifting) finite_nat_iff_bounded mem_Collect_eq subset_eq zero_map zero_option_def)
      thus ?case
        using Cons by auto
    qed
    hence fin: "finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) signal k \<noteq> 0}) list) {})"
      by auto
    thus " finite (fold (\<union>) (map (Femto_VHDL_raw.keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> signal) \<circ> snd) list) {})"
      unfolding keys_def comp_def by auto
  next
    show " \<forall>\<^sub>\<infinity>x. (if x \<le> now \<or> now + dly < x then f x else (f x)(signal := None)) = 0"
      using `\<forall>\<^sub>\<infinity>x. f x = 0` by (smt MOST_mono fun_upd_idem zero_map)
  qed
  thus "finite                                                                
        {x. (\<lambda>sig. if x \<le> now \<or> now + dly < x \<or> sig \<noteq> signal then f x sig
                   else if x \<in> fold (\<union>) (map (Femto_VHDL_raw.keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> signal) \<circ> snd) list) {}
                        then Some (Lv signedness (map (\<lambda>p. bval_of (signal_of (get_time p) (snd p) sig x)) list)) else None) \<noteq>
            0}"
    using `?fun = ?fun'` by metis
qed

lift_definition inr_post ::
  "'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal transaction \<Rightarrow> nat \<Rightarrow> delay \<Rightarrow> 'signal transaction"
  is inr_post_raw'
  unfolding sym[OF eventually_cofinite] using inr_post_raw_almost_all_zero'
  by metis

lemma [code]:
  "inr_post sig val def \<tau> now dly =
      trans_post sig val def (purge' \<tau> now dly sig def val) now dly"
  by (transfer', auto simp add: Femto_VHDL_raw.inr_post_raw'_def)

lift_definition seq_exec :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow>
                                    'signal seq_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> bool" is
  b_seq_exec .

declare seq_exec.rep_eq[code_abbrev]

inductive seq_exec_ind :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow>
                                    'signal seq_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> bool" where
  "seq_exec_ind t \<sigma> \<gamma> \<theta> def Bnull \<tau> \<tau>"

| "seq_exec_ind t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>'' \<Longrightarrow> seq_exec_ind t \<sigma> \<gamma> \<theta> def ss2 \<tau>'' \<tau>' \<Longrightarrow>
                                                        seq_exec_ind t \<sigma> \<gamma> \<theta> def (Bcomp ss1 ss2) \<tau> \<tau>'"

| "beval_ind t \<sigma> \<gamma> \<theta> def guard (Bv True)  \<Longrightarrow> seq_exec_ind t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>' \<Longrightarrow>
                                               seq_exec_ind t \<sigma> \<gamma> \<theta> def (Bguarded guard ss1 ss2) \<tau> \<tau>'"


| "beval_ind t \<sigma> \<gamma> \<theta> def guard (Bv False) \<Longrightarrow> seq_exec_ind t \<sigma> \<gamma> \<theta> def ss2 \<tau> \<tau>' \<Longrightarrow>
                                               seq_exec_ind t \<sigma> \<gamma> \<theta> def (Bguarded guard ss1 ss2) \<tau> \<tau>'"

| "beval_ind t \<sigma> \<gamma> \<theta> def e x \<Longrightarrow> trans_post sig x (\<sigma> sig) \<tau> t dly = \<tau>' \<Longrightarrow>
                                              seq_exec_ind t \<sigma> \<gamma> \<theta> def (Bassign_trans sig e dly) \<tau> \<tau>'"

| "beval_ind t \<sigma> \<gamma> \<theta> def e x \<Longrightarrow> inr_post sig x (\<sigma> sig) \<tau> t dly = \<tau>' \<Longrightarrow>
                                              seq_exec_ind t \<sigma> \<gamma> \<theta> def (Bassign_inert sig e dly) \<tau> \<tau>'"

| "beval_ind t \<sigma> \<gamma> \<theta> def exp x \<Longrightarrow> beval_ind t \<sigma> \<gamma> \<theta> def exp' x \<Longrightarrow> seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'
   \<Longrightarrow> seq_exec_ind t \<sigma> \<gamma> \<theta> def (Bcase exp ((Explicit exp', ss) # choices)) \<tau> \<tau>'"

| "beval_ind t \<sigma> \<gamma> \<theta> def exp x \<Longrightarrow> beval_ind t \<sigma> \<gamma> \<theta> def exp' x' \<Longrightarrow> x \<noteq> x' \<Longrightarrow>
   seq_exec_ind t \<sigma> \<gamma> \<theta> def (Bcase exp choices) \<tau> \<tau>'  \<Longrightarrow>
   seq_exec_ind t \<sigma> \<gamma> \<theta> def (Bcase exp ((Explicit exp', ss) # choices)) \<tau> \<tau>'"

| "seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' \<Longrightarrow>
   seq_exec_ind t \<sigma> \<gamma> \<theta> def (Bcase exp ((Others, ss) # choices)) \<tau> \<tau>'"

| "seq_exec_ind t \<sigma> \<gamma> \<theta> def (Bcase exp []) \<tau> \<tau>"

lemma seq_exec_eq_seq_exec_ind:
  "seq_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>' = seq_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
proof
  assume "seq_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  hence "seq_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping (lookup \<theta>)) def cs (Abs_poly_mapping (lookup \<tau>)) (Abs_poly_mapping (lookup \<tau>'))"
  proof transfer
    fix t \<sigma> \<gamma>
    fix \<theta> :: "nat \<Rightarrow> 'a \<Rightarrow> val option"
    fix def cs
    fix \<tau> \<tau>' :: "nat \<Rightarrow> 'a \<Rightarrow> val option"
    assume "finite {x. \<theta> x \<noteq> 0}"
    assume "finite {x. \<tau> x \<noteq> 0}"
    assume "finite {x. \<tau>' x \<noteq> 0}"
    assume "t , \<sigma> , \<gamma> , \<theta> , def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    thus "seq_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>')"
      using `finite {x. \<theta> x \<noteq> 0}` `finite {x. \<tau> x \<noteq> 0}` `finite {x. \<tau>' x \<noteq> 0}`
    proof (induction rule:b_seq_exec.induct)
      case (1 t \<sigma> \<gamma> \<theta> def \<tau>)
      then show ?case by (auto intro!: seq_exec_ind.intros)
    next
      case (2 t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>'' ss2 \<tau>')
      hence "finite {x. \<tau>'' x \<noteq> 0}"
        using b_seq_exec_almost_all_zero[OF 2(1)]  by (simp add: eventually_cofinite)
      hence "seq_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def ss1 (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>'')"
        using 2(3)[OF 2(5-6)] by auto
      moreover have " seq_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def ss2 (Abs_poly_mapping \<tau>'') (Abs_poly_mapping \<tau>')"
        using 2(4)[OF 2(5) `finite {x. \<tau>'' x \<noteq> 0}` 2(7)] by auto
      ultimately show ?case
        by (auto intro!: seq_exec_ind.intros)
    next
      case (3 t \<sigma> \<gamma> \<theta> def guard ss1 \<tau> \<tau>' ss2)
      hence "finite {x. \<tau>' x \<noteq> 0}"
        using b_seq_exec_almost_all_zero  by blast
      moreover have "beval t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def guard (Bv True)"
        using 3(1) unfolding beval.rep_eq lookup_Abs_poly_mapping[OF `finite {x. \<theta> x \<noteq> 0}`]
        by auto
      ultimately show ?case
        by (simp add: beval_eq_beval_ind "3.IH" "3.prems"(1) "3.prems"(2) seq_exec_ind.intros(3))
    next
      case (4 t \<sigma> \<gamma> \<theta> def guard ss2 \<tau> \<tau>' ss1)
      hence "finite {x. \<tau>' x \<noteq> 0}"
        using b_seq_exec_almost_all_zero  by blast
      moreover have "beval t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def guard (Bv False)"
        using 4(1) unfolding beval.rep_eq lookup_Abs_poly_mapping[OF `finite {x. \<theta> x \<noteq> 0}`]
        by auto
      ultimately show ?case
        by (simp add: beval_eq_beval_ind "4.IH" "4.prems"(1) "4.prems"(2) seq_exec_ind.intros(4))
    next
      case (5 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
      have "beval t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def e x"
        using 5(1) unfolding beval.rep_eq lookup_Abs_poly_mapping[OF `finite {x. \<theta> x \<noteq> 0}`]
        by auto
      have "lookup (trans_post sig x (\<sigma> sig) (Abs_poly_mapping \<tau>) t dly) = lookup (Abs_poly_mapping \<tau>')"
        using 5(2) unfolding trans_post.rep_eq lookup_Abs_poly_mapping[OF `finite {x. \<tau> x \<noteq> 0}`]
        lookup_Abs_poly_mapping[OF `finite {x. \<tau>' x \<noteq> 0}`] by auto
      hence "trans_post sig x (\<sigma> sig) (Abs_poly_mapping \<tau>) t dly = Abs_poly_mapping \<tau>'"
        unfolding lookup_inject by auto
      then show ?case
        using `beval t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def e x`
        by (simp add: beval_eq_beval_ind seq_exec_ind.intros(5))
    next
      case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
      have "beval t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def e x"
        using 6(1) unfolding beval.rep_eq lookup_Abs_poly_mapping[OF `finite {x. \<theta> x \<noteq> 0}`]
        by auto
      have "lookup (inr_post sig x (\<sigma> sig) (Abs_poly_mapping \<tau>) t dly) = lookup (Abs_poly_mapping \<tau>')"
        using 6(2) unfolding inr_post.rep_eq  lookup_Abs_poly_mapping[OF `finite {x. \<tau> x \<noteq> 0}`]
        lookup_Abs_poly_mapping[OF `finite {x. \<tau>' x \<noteq> 0}`] by auto
      hence "inr_post sig x (\<sigma> sig) (Abs_poly_mapping \<tau>) t dly = Abs_poly_mapping \<tau>'"
        unfolding lookup_inject by auto
      then show ?case
        using `beval t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def e x`
        by (auto simp add: seq_exec_ind.intros(6) beval_eq_beval_ind)
    next
      case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau> \<tau>' choices)
      have "beval_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def exp x"
        by (metis (mono_tags, lifting) "7.hyps"(1) "7.prems"(1) beval.abs_eq beval_eq_beval_ind
        eq_onp_same_args)
      moreover have "beval_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def exp' x"
        by (metis "7.hyps"(2) "7.prems"(1) beval.rep_eq beval_eq_beval_ind lookup_Abs_poly_mapping)
      moreover have " seq_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def ss (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>')"
        using 7 by auto
      ultimately show ?case
        by (intro seq_exec_ind.intros) auto
    next
      case (8 t \<sigma> \<gamma> \<theta> def exp x exp' x' choices \<tau> \<tau>' ss)
      have "beval_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def exp x"
        by (metis (mono_tags, lifting) "8.hyps"(1) "8.prems"(1) beval.abs_eq beval_eq_beval_ind
        eq_onp_same_args)
      moreover have "beval_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def exp' x'"
        by (metis (mono_tags) "8.hyps"(2) "8.prems"(1) beval.rep_eq beval_eq_beval_ind
        lookup_Abs_poly_mapping)
      moreover have "seq_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def (Bcase exp choices) (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>')"
        using 8 by auto
      ultimately show ?case
        using 8(3) by (intro seq_exec_ind.intros(8)) auto
    qed (auto simp add: seq_exec_ind.intros)
  qed
  thus "seq_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
    unfolding lookup_inverse by auto
next
  assume "seq_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  thus "seq_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
    unfolding seq_exec.rep_eq
  proof (induction rule:seq_exec_ind.inducts)
    case (3 t \<sigma> \<gamma> \<theta> def guard ss1 \<tau> \<tau>' ss2)
    have "beval_raw t \<sigma> \<gamma> (lookup \<theta>) def guard (Bv True)"
      using 3(1) unfolding sym[OF beval_eq_beval_ind]
      by transfer' auto
    then show ?case
      using 3(3)  by (simp add: b_seq_exec.intros(3))
  next
    case (4 t \<sigma> \<gamma> \<theta> def guard ss2 \<tau> \<tau>' ss1)
    have "beval_raw t \<sigma> \<gamma> (lookup \<theta>) def guard (Bv False)"
      using 4(1) unfolding sym[OF beval_eq_beval_ind] by transfer' auto
    then show ?case
      using 4(3)  by (simp add: b_seq_exec.intros(4))
  next
    case (5 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
    have "beval_raw t \<sigma> \<gamma> (lookup \<theta>) def e x"
      using 5(1) unfolding sym[OF beval_eq_beval_ind] by transfer' auto
    have "trans_post_raw sig x (\<sigma> sig) (lookup \<tau>) t dly = lookup \<tau>'"
      using 5(2) by transfer' auto
    then show ?case
      by (metis \<open>t , \<sigma> , \<gamma> , lookup \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b x\<close> b_seq_exec.intros(5))
  next
    case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
    have "beval_raw t \<sigma> \<gamma> (lookup \<theta>) def e x"
      using 6(1) unfolding sym[OF beval_eq_beval_ind] by transfer' auto
    have "inr_post_raw' sig x (\<sigma> sig) (lookup \<tau>) t dly = lookup \<tau>'"
      using 6(2) by transfer' auto
    then show ?case
      by (metis \<open>t , \<sigma> , \<gamma> , lookup \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b x\<close> b_seq_exec.intros(6))
  next
    case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau> \<tau>' choices)
    have "t, \<sigma> , \<gamma> , lookup \<theta> , def \<turnstile> exp \<longrightarrow>\<^sub>b x"
      by (metis "7.hyps"(1) beval.rep_eq beval_eq_beval_ind)
    moreover have "t, \<sigma> , \<gamma> , lookup \<theta> , def \<turnstile> exp' \<longrightarrow>\<^sub>b x"
      by (metis "7.hyps"(2) beval.rep_eq beval_eq_beval_ind)
    moreover have "b_seq_exec t \<sigma> \<gamma> (lookup \<theta>) def ss (lookup \<tau>) (lookup \<tau>')"
      using 7(3)  by (simp add: "7.IH")
    ultimately show ?case
      by (intro b_seq_exec.intros) auto
  next
    case (8 t \<sigma> \<gamma> \<theta> def exp x exp' x' choices \<tau> \<tau>' ss)
    have "t, \<sigma> , \<gamma> , lookup \<theta> , def \<turnstile> exp \<longrightarrow>\<^sub>b x"
      by (metis "8.hyps"(1) beval.rep_eq beval_eq_beval_ind)
    moreover have "t, \<sigma> , \<gamma> , lookup \<theta> , def \<turnstile> exp' \<longrightarrow>\<^sub>b x'"
      by (metis "8.hyps"(2) beval.rep_eq beval_eq_beval_ind)
    moreover have "b_seq_exec t \<sigma> \<gamma> (lookup \<theta>) def (Bcase exp choices) (lookup \<tau>) (lookup \<tau>')"
      using 8 by auto
    ultimately show ?case
      using 8(3) by (intro b_seq_exec.intros(8)) auto
  qed (auto intro!: b_seq_exec.intros)
qed

lemma seq_exec_ind_deterministic:
  assumes "seq_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>1"
  assumes "seq_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>2"
  shows "\<tau>2 = \<tau>1"
  using assms unfolding sym[OF seq_exec_eq_seq_exec_ind]
  by transfer' (auto simp add: b_seq_exec_deterministic)

lemma seq_exec_ind_progress:
  assumes "seq_wt \<Gamma> ss" and "styping \<Gamma> \<sigma>" and "transtyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "transtyping \<Gamma> \<tau>"
  shows "\<exists>\<tau>'. seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
  unfolding sym[OF seq_exec_eq_seq_exec_ind] using assms
proof transfer
  fix \<Gamma> :: "'a tyenv"
  fix ss \<sigma>
  fix \<theta> \<tau> :: "nat \<Rightarrow> 'a \<rightharpoonup> val"
  fix def t \<gamma>
  assume "seq_wt \<Gamma> ss"
  assume "styping \<Gamma> \<sigma>"
  assume "finite {x. \<theta> x \<noteq> 0}"
  assume "ttyping \<Gamma> \<theta>"
  assume "styping \<Gamma> def"
  assume "finite {x. \<tau> x \<noteq> 0}"
  assume "ttyping \<Gamma> \<tau>"
  hence "\<exists>\<tau>'. t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    using seq_stmts_progress[OF `seq_wt \<Gamma> ss` `styping \<Gamma> \<sigma>` `ttyping \<Gamma> \<theta>` `styping \<Gamma> def` `ttyping \<Gamma> \<tau>`]
    by auto
  then obtain \<tau>' where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by auto
  hence "finite {x. \<tau>' x \<noteq> 0}"
    using b_seq_exec_almost_all_zero
    by (metis (mono_tags) \<open>finite {x. \<tau> x \<noteq> 0}\<close> \<open>finite {x. \<theta> x \<noteq> 0}\<close> eventually_cofinite map_diff_fin_variability)
  thus "Bex {f. finite {x. f x \<noteq> 0}} (b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau>)"
    using \<open>t , \<sigma> , \<gamma> , \<theta> , def \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close> by blast
qed

lemma seq_exec_ind_unique_progress:
  assumes "seq_wt \<Gamma> ss" and "styping \<Gamma> \<sigma>" and "transtyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "transtyping \<Gamma> \<tau>"
  shows "\<exists>!\<tau>'. seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
  using assms
  by (auto simp add: seq_exec_ind_progress  seq_exec_ind_deterministic)

lift_definition map_diff_trans :: "'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction"
  is map_diff_trans_raw unfolding sym[OF eventually_cofinite]
  by (simp add: map_diff_fin_variability)

lift_definition map_add_trans :: "'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction"
  is "\<lambda>\<tau>1 \<tau>2 n. map_add (\<tau>1 n) (\<tau>2 n)" unfolding sym[OF eventually_cofinite]
  by (simp add: map_add_fin_variability)

lemma dom_map_diff_trans_post:
  "dom (lookup (map_diff_trans (trans_post sig x def \<tau> t dly) \<tau>) n)  \<subseteq> {sig}"
  by (transfer', simp add: dom_map_diff_trans_post)

lemma dom_map_diff_purge:
  "\<And>n. dom (lookup (map_diff_trans (purge \<tau> t dly sig def val) \<tau>) n) \<subseteq> {sig}"
  by (transfer', simp add: dom_map_diff_purge)

lift_definition clean_zip ::
  "'signal transaction \<Rightarrow> 'signal transaction \<times> 'signal set \<Rightarrow>  'signal transaction \<times> 'signal set \<Rightarrow>
                                                                                'signal transaction"
  is clean_zip_raw unfolding sym[OF eventually_cofinite]
proof (auto split:prod.splits)
  fix f x1 x1a:: "nat \<Rightarrow> 'signal \<Rightarrow> val option"
  fix x2 x2a
  assume assm1: "\<forall>\<^sub>\<infinity>x. f x = 0"
  assume assm2: "\<forall>\<^sub>\<infinity>x. x1 x = 0"
  assume assm3: "\<forall>\<^sub>\<infinity>x. x1a x = 0"
  thus "\<forall>\<^sub>\<infinity>x. clean_zip_raw f (x1, x2) (x1a, x2a) x = 0"
    using clean_zip_raw_almost_all_zero[OF assm1 assm2 assm3] by auto
qed

lift_definition conc_exec :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow>
                             'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> bool" is
  b_conc_exec .

declare conc_exec.rep_eq[code_abbrev]

inductive conc_exec_ind :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow>
                             'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> bool"
  where
  "disjnt sl \<gamma> \<Longrightarrow> conc_exec_ind t \<sigma> \<gamma> \<theta> def (process sl : ss) \<tau> \<tau>"

| "seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' \<Longrightarrow> \<not> disjnt sl \<gamma> \<Longrightarrow>
                                                     conc_exec_ind t \<sigma> \<gamma> \<theta> def (process sl : ss) \<tau> \<tau>'"

| "conc_exec_ind t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 \<Longrightarrow> conc_exec_ind t \<sigma> \<gamma> \<theta> def cs2 \<tau> \<tau>2 \<Longrightarrow>
    clean_zip \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>'
                                                      \<Longrightarrow> conc_exec_ind t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"

lemma conc_exec_eq_conc_exec_ind:
  "conc_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>' = conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
proof
  assume "conc_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  hence "conc_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping (lookup \<theta>)) def cs (Abs_poly_mapping (lookup \<tau>)) (Abs_poly_mapping (lookup \<tau>'))"
  proof transfer
    fix t \<sigma> \<gamma>
    fix \<theta> \<tau> \<tau>':: "nat \<Rightarrow> 'a \<Rightarrow> val option"
    fix def cs
    assume 1: "finite {x. \<theta> x \<noteq> 0}"
    assume 2: "finite {x. \<tau> x \<noteq> 0}"
    assume 3: "finite {x. \<tau>' x \<noteq> 0}"
    assume "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    thus "conc_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>')"
      using 1 2 3
    proof (induction rule: b_conc_exec.inducts)
      case (1 sl \<gamma> t \<sigma> \<theta> def ss \<tau>)
      then show ?case by (auto intro!: conc_exec_ind.intros)
    next
      case (2 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
      have "seq_exec t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def ss (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>')"
        using 2(1) unfolding seq_exec.rep_eq lookup_Abs_poly_mapping[OF `finite {x. \<theta> x \<noteq> 0}`]
        lookup_Abs_poly_mapping[OF `finite {x. \<tau> x \<noteq> 0}`] lookup_Abs_poly_mapping[OF `finite {x. \<tau>' x \<noteq> 0}`]
        by auto
      then show ?case
        using 2(2) unfolding seq_exec_eq_seq_exec_ind
        by (auto intro!: conc_exec_ind.intros)
    next
      case (3 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
      hence "finite {x. \<tau>1 x \<noteq> 0}" and "finite {x. \<tau>2 x \<noteq> 0}"
        using b_conc_exec_almost_all_zero by blast+
      hence " conc_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs1 (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>1)"
        and " conc_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs2 (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>2)"
        using 3 by blast+
      have "lookup (clean_zip (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>1, set (signals_from cs1)) (Abs_poly_mapping \<tau>2, set (signals_from cs2))) =
            lookup (Abs_poly_mapping \<tau>')"
        using 3(3) unfolding clean_zip.rep_eq lookup_Abs_poly_mapping[OF `finite {x. \<tau> x \<noteq> 0}`]
        lookup_Abs_poly_mapping[OF `finite {x. \<tau>' x \<noteq> 0}`]
        by (simp add: \<open>finite {x. \<tau>1 x \<noteq> 0}\<close> \<open>finite {x. \<tau>2 x \<noteq> 0}\<close>)
      hence "clean_zip (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>1, set (signals_from cs1)) (Abs_poly_mapping \<tau>2, set (signals_from cs2)) =
             Abs_poly_mapping \<tau>'"
        unfolding lookup_inject by auto
      then show ?case
        using \<open>conc_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs1 (Abs_poly_mapping \<tau>)
        (Abs_poly_mapping \<tau>1)\<close> \<open>conc_exec_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs2 (Abs_poly_mapping
        \<tau>) (Abs_poly_mapping \<tau>2)\<close> conc_exec_ind.intros(3) by blast
    qed
  qed
  thus "conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
    unfolding lookup_inverse by auto
next
  assume "conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  thus "conc_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
    unfolding conc_exec.rep_eq
  proof (induction rule: conc_exec_ind.inducts)
    case (1 sl \<gamma> t \<sigma> \<theta> def ss \<tau>)
    then show ?case by transfer' (auto intro!: b_conc_exec.intros)
  next
    case (2 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
    then show ?case
      unfolding sym[OF seq_exec_eq_seq_exec_ind] by transfer' (auto intro!: b_conc_exec.intros)
  next
    case (3 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
    hence "b_conc_exec t \<sigma> \<gamma> (lookup \<theta>) def cs1 (lookup \<tau>) (lookup \<tau>1)" and
          "b_conc_exec t \<sigma> \<gamma> (lookup \<theta>) def cs2 (lookup \<tau>) (lookup \<tau>2)"
      using 3(1-2) by (transfer', auto)+
    then show ?case
      by (metis "3.hyps"(3) b_conc_exec.intros(3) clean_zip.rep_eq id_apply map_prod_simp)
  qed
qed

lemma conc_exec_ind_deterministic:
  assumes "conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>1"
  assumes "conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>2"
  shows "\<tau>2 = \<tau>1"
  using assms unfolding sym[OF conc_exec_eq_conc_exec_ind]
  by transfer' (simp add: b_conc_exec_deterministic)

lemma conc_exec_ind_progress:
  assumes "conc_wt \<Gamma> cs" and "styping \<Gamma> \<sigma>" and "transtyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "transtyping \<Gamma> \<tau>"
  shows "\<exists>\<tau>'. conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  unfolding sym[OF conc_exec_eq_conc_exec_ind] using assms
proof transfer
  fix \<Gamma> :: "'a tyenv"
  fix cs \<sigma>
  fix \<theta> \<tau> :: "nat \<Rightarrow> 'a \<rightharpoonup> val"
  fix def t \<gamma>
  assume 1: "conc_wt \<Gamma> cs"
  assume 2: "styping \<Gamma> \<sigma>"
  assume 3: "finite {x. \<theta> x \<noteq> 0}"
  assume 4: "ttyping \<Gamma> \<theta>"
  assume 5: "styping \<Gamma> def"
  assume 6: "finite {x. \<tau> x \<noteq> 0}"
  assume 7: "ttyping \<Gamma> \<tau>"
  then obtain \<tau>' where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using conc_stmts_progress[OF 1 2 4 5 7] by blast
  moreover hence "finite {x. \<tau>' x \<noteq> 0}"
    using b_conc_exec_almost_all_zero 3 6 by blast
  ultimately show " Bex {f. finite {x. f x \<noteq> 0}} (b_conc_exec t \<sigma> \<gamma> \<theta> def cs \<tau>)"
    by auto
qed

lemma conc_exec_ind_unique_progress:
  assumes "conc_wt \<Gamma> cs" and "styping \<Gamma> \<sigma>" and "transtyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "transtyping \<Gamma> \<tau>"
  shows "\<exists>!\<tau>'. conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  using assms conc_exec_ind_deterministic conc_exec_ind_progress
  by auto

lift_definition init' :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow>
                                 'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> bool"
  is Femto_VHDL_raw.init' .

inductive init'_ind :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow>
                                 'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> bool" where
  "seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' \<Longrightarrow> init'_ind t \<sigma> \<gamma> \<theta> def (process sl : ss) \<tau> \<tau>'"
| "init'_ind t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 \<Longrightarrow> init'_ind t \<sigma> \<gamma> \<theta> def cs2 \<tau> \<tau>2 \<Longrightarrow>
    clean_zip \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>'
                                                      \<Longrightarrow> init'_ind t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"

lemma init'_eq_init'_ind:
  "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>' = init'_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
proof
  assume "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  hence "init'_ind t \<sigma> \<gamma> (Abs_poly_mapping (lookup \<theta>)) def cs (Abs_poly_mapping (lookup \<tau>)) (Abs_poly_mapping (lookup \<tau>'))"
  proof transfer
    fix t \<sigma> \<gamma>
    fix \<theta> \<tau> \<tau>' :: "nat \<Rightarrow> 'a \<rightharpoonup> val"
    fix def cs
    assume 1: "finite {x. \<theta> x \<noteq> 0}"
    assume 2: "finite {x. \<tau> x \<noteq> 0}"
    assume 3: "finite {x. \<tau>' x \<noteq> 0}"
    assume "Femto_VHDL_raw.init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>' "
    thus "init'_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>')"
      using 1 2 3
    proof (induction rule:Femto_VHDL_raw.init'.inducts)
      case (1 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
      have " seq_exec t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def ss (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>')"
        using 1  by (simp add: seq_exec.rep_eq)
      then show ?case
        unfolding seq_exec_eq_seq_exec_ind
        by (simp add: init'_ind.intros(1))
    next
      case (2 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
      hence "finite {x. \<tau>1 x \<noteq> 0}" and "finite {x. \<tau>2 x \<noteq> 0}"
        using init'_raw_almost_all_zero by blast+
      hence "init'_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs1 (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>1)"
        and "init'_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs2 (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>2)"
        using 2 by auto
      have "lookup (clean_zip (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>1, set (signals_from cs1)) (Abs_poly_mapping \<tau>2, set (signals_from cs2))) =
             lookup (Abs_poly_mapping \<tau>')"
        using 2(3) unfolding clean_zip.rep_eq lookup_Abs_poly_mapping[OF `finite {x. \<tau> x \<noteq> 0}`]
        lookup_Abs_poly_mapping[OF `finite {x. \<tau>' x \<noteq> 0}`]
        by (simp add: \<open>finite {x. \<tau>1 x \<noteq> 0}\<close> \<open>finite {x. \<tau>2 x \<noteq> 0}\<close>)
      hence "clean_zip (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>1, set (signals_from cs1)) (Abs_poly_mapping \<tau>2, set (signals_from cs2)) = Abs_poly_mapping \<tau>'"
        unfolding lookup_inject by auto
      then show ?case
        using \<open>init'_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs1 (Abs_poly_mapping \<tau>) (Abs_poly_mapping
        \<tau>1)\<close> \<open>init'_ind t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs2 (Abs_poly_mapping \<tau>) (Abs_poly_mapping
        \<tau>2)\<close> init'_ind.intros(2) by blast
    qed
  qed
  thus "init'_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
    unfolding lookup_inverse by auto
next
  assume "init'_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  thus "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
    unfolding init'.rep_eq
  proof (induction rule: init'_ind.inducts)
    case (1 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
    then show ?case
      unfolding sym[OF seq_exec_eq_seq_exec_ind]
      by (transfer', auto intro!: Femto_VHDL_raw.init'.intros)
  next
    case (2 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
    have "clean_zip_raw (lookup \<tau>) (lookup \<tau>1, set (signals_from cs1)) (lookup \<tau>2, set (signals_from cs2)) = lookup \<tau>'"
      using 2(3) by transfer' auto
    then show ?case
      using "2.IH"(1) "2.IH"(2) init'.intros(2) by blast
  qed
qed

definition rem_curr_trans :: "nat \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction" where
  "rem_curr_trans t \<tau> = Poly_Mapping.update t 0 \<tau>"

subsection \<open>Semantics of simulation\<close>

lift_definition next_time :: "nat \<Rightarrow> 'signal transaction \<Rightarrow> nat"
  is Femto_VHDL_raw.next_time .

declare next_time.rep_eq[code_abbrev]

lift_definition quiet :: "'signal transaction \<Rightarrow> 'signal event \<Rightarrow> bool"
  is Femto_VHDL_raw.quiet .

declare quiet.rep_eq[code_abbrev]

lemma [code]:
  "quiet \<tau> \<gamma> = (if \<tau> = 0 \<and> \<gamma> = {} then True else False)"
  by (transfer', auto simp add: Femto_VHDL_raw.quiet_def zero_fun_def zero_option_def)

lift_definition next_state :: "nat \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow> 'signal state"
  is Femto_VHDL_raw.next_state .

declare next_state.rep_eq[code_abbrev]

lemma [code]:
  "next_state t \<tau>' \<sigma> = (let m = lookup \<tau>' (next_time t \<tau>') in override_on \<sigma> (the o m) (dom m))"
  by (transfer', auto simp add: Femto_VHDL_raw.next_state_def)

lift_definition next_event :: "nat \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow> 'signal event"
  is Femto_VHDL_raw.next_event .

declare next_event.rep_eq[code_abbrev]

lemma [code]:
  "next_event t \<tau>' \<sigma> = (let m = lookup \<tau>' (next_time t \<tau>') in
                                       {sig. if sig \<in> dom m then (the o m) sig \<noteq> \<sigma> sig else False})"
  by (transfer', auto simp add: Femto_VHDL_raw.next_event_def Let_def)

lift_definition add_to_beh ::
  "'signal state \<Rightarrow> 'signal transaction \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal transaction"
  is Femto_VHDL_raw.add_to_beh unfolding add_to_beh_def sym[OF eventually_cofinite]
  by (metis (mono_tags) upd_eventually_cofinite)

lemma [code]:
  "add_to_beh \<sigma> \<theta> st fi = (if st < fi then Poly_Mapping.update st (Some o \<sigma>) \<theta> else \<theta>)"
  by (transfer', auto simp add: Femto_VHDL_raw.add_to_beh_def)

lift_definition add_to_beh2 ::
  "'signal state \<Rightarrow> 'signal transaction \<Rightarrow> nat \<Rightarrow> 'signal state \<Rightarrow> 'signal transaction"
  is Femto_VHDL_raw.add_to_beh2 unfolding add_to_beh2_def Let_def sym[OF eventually_cofinite]
  using upd_eventually_cofinite by fastforce

lemma [code]:
  "add_to_beh2 \<sigma> \<theta> t def = (let m = (\<lambda>s. if signal_of2 (def s) \<theta> s t = \<sigma> s then lookup \<theta> t s else Some (\<sigma> s)) in Poly_Mapping.update t m \<theta>)"
  apply transfer' unfolding Femto_VHDL_raw.add_to_beh2_def by auto

lift_definition simulate_fin ::  "nat \<Rightarrow> nat \<Rightarrow> 'a  state \<Rightarrow> 'a event \<Rightarrow> 'a transaction \<Rightarrow> 'a state \<Rightarrow>
                                            'a conc_stmt \<Rightarrow> 'a transaction \<Rightarrow> nat \<times> 'a state \<times> 'a event \<times>'a transaction \<times> 'a transaction \<Rightarrow> bool"
  is b_simulate_fin .

inductive simulate_fin_ind :: "nat \<Rightarrow> nat \<Rightarrow> 'signal  state \<Rightarrow> 'signal event \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow>
                            'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> nat \<times> 'signal state \<times> 'signal event \<times> 'signal transaction \<times> 'signal transaction \<Rightarrow> bool"
  where

  \<comment> \<open>Business as usual: not quiesced yet and there is still time\<close>
  "    (t < maxtime)
   \<Longrightarrow> (\<not> quiet \<tau> \<gamma>)
   \<Longrightarrow> (conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>')
   \<Longrightarrow> next_time t \<tau>' \<le> maxtime
   \<Longrightarrow> simulate_fin_ind
          maxtime
             (next_time t \<tau>')
                (next_state t \<tau>' \<sigma>)
                    (next_event t \<tau>' \<sigma>)
                        (add_to_beh2 \<sigma> \<theta> t def) def cs (rem_curr_trans (next_time t \<tau>') \<tau>') res
   \<Longrightarrow> simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res"

  \<comment> \<open>Business as usual: not quiesced yet and there is still time --- case 2\<close>
| "    (t < maxtime)
   \<Longrightarrow> (\<not> quiet \<tau> \<gamma>)
   \<Longrightarrow> (conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>')
   \<Longrightarrow> (maxtime < next_time t \<tau>')
   \<Longrightarrow> simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> (maxtime, \<sigma>, {}, add_to_beh2 \<sigma> \<theta> t def, \<tau>')"

  \<comment> \<open>The simulation has quiesced and there is still time\<close>
| "    (t < maxtime)
   \<Longrightarrow> (quiet \<tau> \<gamma>)
   \<Longrightarrow> simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> (maxtime, \<sigma>, \<gamma>, \<theta>, 0)"

  \<comment> \<open>Time is up\<close>
| "  t = maxtime
   \<Longrightarrow> simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> (maxtime, \<sigma>, \<gamma>, \<theta>, \<tau>)"

thm b_simulate_fin_deterministic

lemma simulate_fin_deterministic:
  assumes "simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res1"
  assumes "simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res2"
  shows "res2 = res1"
  using assms
  by (transfer', auto simp add: b_simulate_fin_deterministic)

inductive_cases bau2: "simulate_fin_ind maxtime t \<sigma> \<gamma> def \<theta> cs \<tau> res"

lemma simulate_fin_eq_simulate_fin_ind:
  "simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res = simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res"
proof
  assume "simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res"
  hence "simulate_fin_ind maxtime t \<sigma> \<gamma> (Abs_poly_mapping (lookup \<theta>)) def cs (Abs_poly_mapping (lookup \<tau>))
         (get_time res, get_state res, get_event res, (Abs_poly_mapping (lookup (get_beh res))), (Abs_poly_mapping (lookup (get_trans res))))"
  proof  transfer
    fix maxtime t :: nat
    fix \<sigma> :: "'a state "
    fix \<gamma> def cs
    fix \<tau> \<theta> :: "'a trans_raw"
    fix res :: "nat \<times> 'a state \<times> 'a event \<times>'a trans_raw \<times> 'a trans_raw"
    assume fin_trans: "finite {x. \<tau> x \<noteq> 0}"
    assume fin_hist:  "finite {x. \<theta> x \<noteq> 0}"
    assume fin_res: "pred_prod top
        (pred_prod (pred_fun top top) (pred_prod (\<lambda>A. Ball A top) (pred_prod (\<lambda>f. finite {x. f x \<noteq> 0}) (\<lambda>f. finite {x. f x \<noteq> 0}))))
        res"
    hence fin_res1: "finite {x. get_beh res x \<noteq> 0}" and fin_res2: "finite {x. get_trans res x \<noteq> 0}"
      by (simp add: pred_prod_beta)+
    assume "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
    thus "simulate_fin_ind maxtime t \<sigma> \<gamma> (Abs_poly_mapping \<theta>) def cs (Abs_poly_mapping \<tau>) (get_time res, get_state res, get_event res, Abs_poly_mapping (get_beh res), Abs_poly_mapping (get_trans res))"
      using fin_res1 fin_res2 fin_hist fin_trans
    proof (induction rule:b_simulate_fin.induct)
      case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
      have "\<not> quiet (Abs_poly_mapping \<tau>) \<gamma>"
        using 1(2) unfolding quiet.rep_eq lookup_Abs_poly_mapping[OF `finite {x. \<tau> x \<noteq> 0}`] by auto

      \<comment> \<open>several abbreviations for simplifying the proof notation\<close>
      let ?\<theta> = "Abs_poly_mapping \<theta>"
      let ?\<tau> = "Abs_poly_mapping \<tau>"
      let ?res = "(t, \<sigma>, Abs_poly_mapping (get_beh res), Abs_poly_mapping (get_trans res))"
      obtain q\<tau>' where qt_def: "conc_exec t \<sigma> \<gamma> ?\<theta> def cs ?\<tau> q\<tau>'"
        by (metis (no_types, lifting) "1.hyps"(3) "1.prems"(3) "1.prems"(4) Collect_cong b_conc_exec_almost_all_zero conc_exec.abs_eq eq_onp_same_args)
      note fin_res1 = `finite {x. get_beh res x \<noteq> 0}`
      note fin_res2 = `finite {x. get_trans res x \<noteq> 0}`
      note fin_trans = `finite {x. \<tau> x \<noteq> 0}`
      note fin_hist = `finite {x. \<theta> x \<noteq> 0}`

      \<comment> \<open>obtaining inductive hypothesis\<close>
      have "finite {x. Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x \<noteq> 0}"
        using add_to_beh2_almost_all_zero[OF fin_hist] by auto
      moreover have "finite {x. \<tau>' x \<noteq> 0}"
        using b_conc_exec_almost_all_zero[OF `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` fin_trans fin_hist]
        by auto
      moreover hence "finite {x. (\<tau>'(Femto_VHDL_raw.next_time t \<tau>' := 0)) x \<noteq> 0}"
        using rem_next_time_almost_all_zero by metis
      ultimately have IH: " simulate_fin_ind maxtime (Femto_VHDL_raw.next_time t \<tau>') (Femto_VHDL_raw.next_state t \<tau>' \<sigma>) (Femto_VHDL_raw.next_event t \<tau>' \<sigma>)
     (Abs_poly_mapping (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def)) def cs (Abs_poly_mapping (\<tau>'(Femto_VHDL_raw.next_time t \<tau>' := 0)))
     (get_time res, get_state res, get_beh' res, Abs_poly_mapping (get_beh res), Abs_poly_mapping (get_trans res))"
        using 1(6)[OF fin_res1 fin_res2] by blast 

      \<comment> \<open>continuing the proof\<close>
      have nt: "Femto_VHDL_raw.next_time t \<tau>' = next_time t q\<tau>'" and
           ns: "Femto_VHDL_raw.next_state t \<tau>' \<sigma> = next_state t q\<tau>' \<sigma>" and
           ne: "Femto_VHDL_raw.next_event t \<tau>' \<sigma> = next_event t q\<tau>' \<sigma>" and
           nb: "Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def = lookup (add_to_beh2 \<sigma> ?\<theta> t def)"
        unfolding next_time.rep_eq next_state.rep_eq next_event.rep_eq  add_to_beh.rep_eq
          conc_exec.rep_eq  lookup_Abs_poly_mapping[OF fin_hist]  lookup_Abs_poly_mapping[OF fin_trans]
        using `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` qt_def
           apply (metis \<open>lookup (Abs_poly_mapping \<tau>) = \<tau>\<close> \<open>lookup (Abs_poly_mapping \<theta>) = \<theta>\<close> b_conc_exec_deterministic conc_exec.rep_eq)+
        by (simp add: \<open>lookup (Abs_poly_mapping \<theta>) = \<theta>\<close> add_to_beh2.rep_eq)
      have ntr: "\<tau>'(Femto_VHDL_raw.next_time t \<tau>' := 0) = lookup (rem_curr_trans (next_time t q\<tau>') q\<tau>')"
        unfolding rem_curr_trans_def Poly_Mapping.update.rep_eq conc_exec.rep_eq next_time.rep_eq
        lookup_Abs_poly_mapping[OF fin_hist]  lookup_Abs_poly_mapping[OF fin_trans]
        using `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` qt_def
        by (metis \<open>lookup (Abs_poly_mapping \<tau>) = \<tau>\<close> \<open>lookup (Abs_poly_mapping \<theta>) = \<theta>\<close> b_conc_exec_deterministic conc_exec.rep_eq)+
      have sim: "simulate_fin_ind maxtime (Femto_VHDL.next_time t q\<tau>') (Femto_VHDL.next_state t q\<tau>' \<sigma>) (Femto_VHDL.next_event t q\<tau>' \<sigma>)
     (Abs_poly_mapping (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def)) def cs (rem_curr_trans (next_time t q\<tau>') q\<tau>')
     (get_time res, get_state res, get_beh' res, Abs_poly_mapping (get_beh res), Abs_poly_mapping (get_trans res))"
        using IH ntr unfolding nt ns ne by simp
      show ?case
        using simulate_fin_ind.intros(1)[OF `t < maxtime` `\<not> quiet ?\<tau> \<gamma>` _ _] sim qt_def 
        \<open>Femto_VHDL_raw.next_time t \<tau>' \<le> maxtime\<close>
        unfolding conc_exec_eq_conc_exec_ind  using nt 
        by (smt Femto_VHDL_raw.add_to_beh_def add_to_beh.rep_eq lookup_inverse nb update.rep_eq)
    next
      case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
      hence "\<not> quiet (Abs_poly_mapping \<tau>) \<gamma>"
        using 2(2) unfolding quiet.rep_eq lookup_Abs_poly_mapping[OF `finite {x. \<tau> x \<noteq> 0}`] by auto

      \<comment> \<open>several abbreviations for simplifying the proof notation\<close>
      let ?\<theta> = "Abs_poly_mapping \<theta>"
      let ?\<tau> = "Abs_poly_mapping \<tau>"
      let ?res = "(t, \<sigma>, Abs_poly_mapping (get_beh res), Abs_poly_mapping (get_trans res))"
      obtain q\<tau>' where qt_def: "conc_exec t \<sigma> \<gamma> ?\<theta> def cs ?\<tau> q\<tau>'"
        by (metis (no_types, lifting) 2 Collect_cong b_conc_exec_almost_all_zero conc_exec.abs_eq eq_onp_same_args)
      note fin_res1 = `finite {x. get_beh res x \<noteq> 0}`
      note fin_res2 = `finite {x. get_trans res x \<noteq> 0}`
      note fin_trans = `finite {x. \<tau> x \<noteq> 0}`
      note fin_hist = `finite {x. \<theta> x \<noteq> 0}`
      have qt_def': "conc_exec_ind t \<sigma> \<gamma> ?\<theta> def cs ?\<tau> q\<tau>'"
        using qt_def unfolding conc_exec_eq_conc_exec_ind by auto
      have nt: "Femto_VHDL_raw.next_time t \<tau>' = next_time t q\<tau>'" and
           ns: "Femto_VHDL_raw.next_state t \<tau>' \<sigma> = next_state t q\<tau>' \<sigma>" and
           ne: "Femto_VHDL_raw.next_event t \<tau>' \<sigma> = next_event t q\<tau>' \<sigma>" and
           nb: "Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def =
                lookup (add_to_beh2 \<sigma> ?\<theta> t def)"
        unfolding next_time.rep_eq next_state.rep_eq next_event.rep_eq  add_to_beh.rep_eq
          conc_exec.rep_eq  lookup_Abs_poly_mapping[OF fin_hist]  lookup_Abs_poly_mapping[OF fin_trans]
        using `t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'` qt_def
           apply (metis \<open>lookup (Abs_poly_mapping \<tau>) = \<tau>\<close> \<open>lookup (Abs_poly_mapping \<theta>) = \<theta>\<close> b_conc_exec_deterministic conc_exec.rep_eq)+
        by (simp add: \<open>lookup (Abs_poly_mapping \<theta>) = \<theta>\<close> add_to_beh2.rep_eq)
      hence "maxtime < Femto_VHDL.next_time t q\<tau>'"
        using 2(4) by auto
      have "lookup (Poly_Mapping.update t (Some \<circ> \<sigma>) (Abs_poly_mapping \<theta>)) = (\<theta>(t := Some \<circ> \<sigma>))"
        unfolding Poly_Mapping.update.rep_eq lookup_Abs_poly_mapping[OF 2(5)]
        by (simp add: "2.prems"(3))
      hence " Abs_poly_mapping (Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def) = Femto_VHDL.add_to_beh2 \<sigma> (Abs_poly_mapping \<theta>) t def"
        by (simp add: nb)
      have "lookup (Abs_poly_mapping \<theta>) = \<theta>"
        using fin_hist by auto
      moreover have "lookup (Abs_poly_mapping \<tau>) = \<tau>" 
        by (simp add: "2.prems"(4))
      ultimately have "lookup q\<tau>' = \<tau>'"
        using qt_def \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'\<close> unfolding conc_exec.rep_eq
        using b_conc_exec_deterministic by fastforce
      hence "Abs_poly_mapping \<tau>' = q\<tau>'"
        using lookup_inverse by blast
      thus ?case 
        using simulate_fin_ind.intros(2)[OF `t < maxtime` \<open>\<not> quiet (Abs_poly_mapping \<tau>) \<gamma>\<close> qt_def' \<open>maxtime < Femto_VHDL.next_time t q\<tau>'\<close>]
        nb by auto
    next
      case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
      have *: "quiet (Abs_poly_mapping \<tau>) \<gamma>"
        using 3 unfolding quiet.rep_eq lookup_Abs_poly_mapping[OF `finite {x. \<tau> x \<noteq> 0}`] by auto
      have "lookup (Poly_Mapping.update t (Some \<circ> \<sigma>) (Abs_poly_mapping \<theta>)) = (\<theta>(t := Some \<circ> \<sigma>))"
        unfolding Poly_Mapping.update.rep_eq lookup_Abs_poly_mapping[OF 3(4)]
        by (simp add: "3.prems"(3))
      hence "Abs_poly_mapping (\<theta>(t := Some \<circ> \<sigma>)) = Poly_Mapping.update t (Some \<circ> \<sigma>) (Abs_poly_mapping \<theta>)"
        by (metis lookup_inverse)
      thus ?case
        using simulate_fin_ind.intros(3)[OF 3(1) *] 
      proof -
        have "Abs_poly_mapping (0::nat \<Rightarrow> 'a \<Rightarrow> val option) = empty_trans"
          by (simp add: poly_mapping_eqI zero_fun_def)
        then show ?thesis
          using \<open>\<And>def cs \<theta> \<sigma>. simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs (Abs_poly_mapping \<tau>) (maxtime, \<sigma>, \<gamma>, \<theta>, empty_trans)\<close> by auto
      qed
    next
      case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
      then show ?case
        using simulate_fin_ind.intros(4)[OF 4(1)] by auto
    qed
  qed
  thus "simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res"
    unfolding lookup_inverse by auto
next
  assume "simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res"
  thus "simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res"
    unfolding simulate_fin.rep_eq
  proof (induction rule: simulate_fin_ind.induct)
    case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
    then show ?case     
      unfolding sym[OF conc_exec_eq_conc_exec_ind]
      by (metis Femto_VHDL.rem_curr_trans_def add_to_beh2.rep_eq b_simulate_fin.intros(1)
      conc_exec.rep_eq next_event.rep_eq next_state.rep_eq next_time.rep_eq quiet.rep_eq
      update.rep_eq)
  next
    case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
    have *: " map_prod id (map_prod id (map_prod id (map_prod lookup lookup)))
                                                  (maxtime, \<sigma>, {}, Femto_VHDL.add_to_beh2 \<sigma> \<theta> t def, \<tau>') = 
            (maxtime, \<sigma>, {}, lookup (Femto_VHDL.add_to_beh2 \<sigma> \<theta> t def), lookup \<tau>')"
      by auto
    have **: "lookup (Femto_VHDL.add_to_beh2 \<sigma> \<theta> t def) = Femto_VHDL_raw.add_to_beh2 \<sigma> (lookup \<theta>) t def"
      by transfer' auto
    show ?case     
      unfolding sym[OF conc_exec_eq_conc_exec_ind] * **
    proof (rule b_simulate_fin.intros(2))
      show "t < maxtime"
        by (simp add: "2.hyps"(1))
    next
      show "\<not> Femto_VHDL_raw.quiet (lookup \<tau>) \<gamma>"
        using 2(2) by transfer' auto
    next
      show "t , \<sigma> , \<gamma> , lookup \<theta>, def  \<turnstile> <cs , lookup \<tau>> \<longrightarrow>\<^sub>c lookup \<tau>'"
        using 2(3) unfolding sym[OF conc_exec_eq_conc_exec_ind] 
        by transfer' auto
    next
      show "maxtime < Femto_VHDL_raw.next_time t (lookup \<tau>')"
        using 2(4) by transfer' auto
    qed
  next
    case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
    then show ?case 
      unfolding sym[OF conc_exec_eq_conc_exec_ind]
      by (smt Femto_VHDL_raw.quiet_def apsnd_conv apsnd_def b_simulate_fin.intros(3) lookup_zero
      map_prod_def old.prod.case poly_mapping_eqI quiet.rep_eq update.rep_eq zero_fun_def)
  qed (simp add: b_simulate_fin.intros(4))
qed

lemma simulate_fin_ind_deterministic:
  assumes "simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res1"
  assumes "simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res2"
  shows "res2 = res1"
  using assms unfolding sym[OF simulate_fin_eq_simulate_fin_ind]
  by (auto simp add: simulate_fin_deterministic)

lift_definition simulate :: "nat \<Rightarrow> 'a state \<Rightarrow> 'a conc_stmt \<Rightarrow> 'a transaction \<Rightarrow> nat \<times> 'a state \<times> 'a event \<times> 'a transaction \<times> 'a transaction \<Rightarrow> bool"
  is b_simulate .

inductive simulate_ind :: "nat \<Rightarrow> 'a state \<Rightarrow> 'a conc_stmt \<Rightarrow> 'a transaction \<Rightarrow>  nat \<times> 'a state \<times> 'a event \<times> 'a transaction \<times> 'a transaction \<Rightarrow> bool" where
  "     init'_ind 0 def {} 0 def cs \<tau> \<tau>'
   \<Longrightarrow>  next_time  0 \<tau>' = t'
   \<Longrightarrow>  next_state 0 \<tau>' def = \<sigma>'
   \<Longrightarrow>  next_event 0 \<tau>' def = \<gamma>'
   \<Longrightarrow>  simulate_fin_ind maxtime t' \<sigma>' \<gamma>' 0 def cs (rem_curr_trans t' \<tau>') res
   \<Longrightarrow>  simulate_ind  maxtime def cs \<tau> res"

lemma simulate_eq_simulate_ind:
  "simulate maxtime def cs \<tau> res = simulate_ind maxtime def cs \<tau> res"
proof
  assume "simulate maxtime def cs \<tau> res"
  hence "simulate_ind maxtime def cs (Abs_poly_mapping (lookup \<tau>))
         (get_time res, get_state res, get_event res, (Abs_poly_mapping (lookup (get_beh res))), (Abs_poly_mapping (lookup (get_trans res))))"
  proof transfer
    fix maxtime :: nat
    fix def
    fix \<tau> :: "'a trans_raw"
    fix res :: "nat \<times> 'a state \<times> 'a event \<times>'a trans_raw \<times> 'a trans_raw"
    fix cs :: "'a conc_stmt"
    assume fin_trans: "finite {x. \<tau> x \<noteq> 0}"
    assume fin_hist: "pred_prod top
        (pred_prod (pred_fun top top) (pred_prod (\<lambda>A. Ball A top) (pred_prod (\<lambda>f. finite {x. f x \<noteq> 0}) (\<lambda>f. finite {x. f x \<noteq> 0}))))
        res "
    hence fin_hist1: "finite {x. get_beh res x \<noteq> 0}" and fin_hist2: "finite {x. get_trans res x \<noteq> 0}"
      by (simp add: pred_prod_beta)+
    assume "b_simulate maxtime def cs \<tau> res"
    thus "simulate_ind maxtime def cs (Abs_poly_mapping \<tau>)
          (get_time res, get_state res, get_event res, (Abs_poly_mapping (get_beh res)), Abs_poly_mapping (get_trans res))"
      using fin_trans fin_hist1 fin_hist2
    proof (induction rule: b_simulate.induct)
      case (1 def cs \<tau> \<tau>' t' \<sigma>' \<gamma>'  maxtime res)
      note fin_trans = `finite {x. \<tau> x \<noteq> 0}`
      note fin_hist1 = `finite {x. get_beh res x \<noteq> 0}`
      note fin_hist2 = `finite {x. get_trans res x \<noteq> 0}`
      have fin_next_trans: "finite {x. \<tau>' x \<noteq> 0}"
        using init'_raw_almost_all_zero[OF 1(1) _ fin_trans]
        by (simp add: zero_fun_def)
      \<comment> \<open>obtaining the first premise in the proof rule of @{term "simulate_ind"}\<close>
      have look_abs_trans: "lookup (Abs_poly_mapping \<tau>) = \<tau>"
        using lookup_Abs_poly_mapping[OF fin_trans] by auto
      have "lookup (Abs_poly_mapping \<tau>') = \<tau>'"
        using lookup_Abs_poly_mapping[OF `finite {x. \<tau>' x \<noteq> 0}`] by auto
      have "lookup empty_trans = 0"
        by (transfer', auto simp add: zero_fun_def)
      have prem1: "init' 0 def {} 0 def cs  (Abs_poly_mapping \<tau>) (Abs_poly_mapping \<tau>')"
        unfolding init'.rep_eq `lookup empty_trans = 0` using 1(1)
        by (simp add: \<open>lookup (Abs_poly_mapping \<tau>') = \<tau>'\<close> look_abs_trans)

      \<comment> \<open>obtaining the 2nd and 3rd premise in the proof rule of @{term "simulate_ind"}\<close>
      have prem2: "next_time 0 (Abs_poly_mapping \<tau>') = t'" and
           prem3: "next_state 0 (Abs_poly_mapping \<tau>') def = \<sigma>'"
        using 1(2) 1(3) unfolding next_time.rep_eq next_state.rep_eq
        lookup_Abs_poly_mapping[OF fin_next_trans] by auto

      \<comment> \<open>obtaining the 4th premise in the proof rule of @{term "simulate_ind"}\<close>
      have prem4: "next_event 0 (Abs_poly_mapping \<tau>') def = \<gamma>'"
        using 1(4) unfolding next_event.rep_eq
        lookup_Abs_poly_mapping[OF fin_next_trans] by auto

      \<comment> \<open>obtaining the 6th premise in the proof rule of @{term "simulate_ind"}\<close>
      let ?res  = "(get_time res, get_state res, get_event res, (Abs_poly_mapping (get_beh res)), Abs_poly_mapping (get_trans res))"
      let ?\<tau>'   = "Abs_poly_mapping \<tau>'"
      have lookup_res: "(get_time res, get_state res, get_event res, lookup (Abs_poly_mapping (get_beh res)), lookup (Abs_poly_mapping (get_trans res))) = res"
        using lookup_Abs_poly_mapping[OF fin_hist1] lookup_Abs_poly_mapping[OF fin_hist2]
        by auto
      have lookup_rem: "lookup (rem_curr_trans t' ?\<tau>') = \<tau>'(t':=0)"
        unfolding rem_curr_trans_def update.rep_eq lookup_Abs_poly_mapping[OF fin_next_trans]
        by auto
      have map_comp: "map_prod id (map_prod id (map_prod id (map_prod lookup lookup))) (get_time res, get_state res, get_beh' res, Abs_poly_mapping (get_beh res), Abs_poly_mapping (get_trans res)) = 
            (get_time res, get_state res, get_event res, lookup (Abs_poly_mapping (get_beh res)), lookup (Abs_poly_mapping (get_trans res)))"
        by auto
      have "simulate_fin maxtime t' \<sigma>' \<gamma>' 0 def cs (rem_curr_trans t' ?\<tau>') ?res"
        using 1(5) unfolding simulate_fin.rep_eq  lookup_rem \<open>lookup empty_trans = 0\<close> map_comp lookup_res
        by auto
      hence prem6: "simulate_fin_ind maxtime t' \<sigma>' \<gamma>' 0 def cs (rem_curr_trans t' ?\<tau>') ?res"
        using simulate_fin_eq_simulate_fin_ind by metis
      show "simulate_ind maxtime def cs (Abs_poly_mapping \<tau>)
        (get_time res, get_state res, get_event res, Abs_poly_mapping (get_beh res), Abs_poly_mapping (get_trans res))"
        using prem1 prem2 prem3 prem4  prem6
        unfolding init'_eq_init'_ind by (auto intro!:simulate_ind.intros)
    qed
  qed
  thus "simulate_ind maxtime def cs \<tau> res"
    unfolding lookup_inverse by auto
next
  assume "simulate_ind maxtime def cs \<tau> res"
  thus "simulate maxtime def cs \<tau> res"
    unfolding simulate.rep_eq
  proof (induction rule:simulate_ind.induct)
    case (1 def cs \<tau> \<tau>' t' \<sigma>' \<gamma>' maxtime res)
    have prem1: "Femto_VHDL_raw.init' 0 def {} 0 def cs (lookup \<tau>) (lookup \<tau>')"
      using 1(1) unfolding sym[OF init'_eq_init'_ind] by (transfer', auto simp add: zero_fun_def)
    have prem2: "Femto_VHDL_raw.next_time  0 (lookup \<tau>') = t'"
      using 1(2) by transfer'
    have prem3: "Femto_VHDL_raw.next_state 0 (lookup \<tau>') def = \<sigma>'"
      using 1(3) by transfer'
    have prem4: "Femto_VHDL_raw.next_event 0 (lookup \<tau>') def = \<gamma>'"
      using 1(4) by transfer'
    have prem6: "maxtime, t', \<sigma>', \<gamma>', (lookup empty_trans), def \<turnstile> <cs, (lookup \<tau>')(t' := 0)> \<leadsto> (get_time res, get_state res, get_event res, lookup (get_beh res), lookup (get_trans res))"
      using 1(5) unfolding sym[OF simulate_fin_eq_simulate_fin_ind] rem_curr_trans_def
      by (transfer', auto)
    have "lookup empty_trans = 0"
      by (transfer', auto simp add: zero_fun_def)
    have res_def: "res = (get_time res, get_state res, get_event res, get_beh res, get_trans res)"
      by auto
    hence helper: "(map_prod id (map_prod id (map_prod id (map_prod lookup lookup)))) (get_time res, get_state res, get_event res, get_beh res, get_trans res) = (get_time res, get_state res, get_event res, lookup (get_beh res), lookup (get_trans res))"
      unfolding  Product_Type.map_prod_simp by auto
    show ?case
      apply (rule b_simulate.intros)
      using prem1 apply simp
      using prem2 apply simp
      using prem3 apply simp
      using prem4 apply simp
      using prem6 unfolding \<open>lookup empty_trans = 0\<close> using res_def helper by presburger
  qed
qed

type_synonym 'signal configuration = "nat \<times> 'signal  state \<times> 'signal event \<times> 'signal transaction \<times> 'signal state"

lift_definition update_config :: "'signal configuration \<Rightarrow> 'signal transaction \<Rightarrow> 'signal configuration"
  is update_config_raw unfolding sym[OF eventually_cofinite]
proof -
  fix config :: "nat \<times> 'signal  state \<times> 'signal event \<times> 'signal trans_raw \<times> 'signal state"
  fix \<tau>' :: "'signal trans_raw"
  assume *: " pred_prod top (pred_prod top (pred_prod top (pred_prod (\<lambda>f. \<forall>\<^sub>\<infinity>x. f x = 0) top))) config "
  obtain t \<sigma> \<gamma> \<theta> def where "config = (t, \<sigma>, \<gamma>, \<theta>, def)"
    using prod_cases5 by blast
  hence "\<forall>\<^sub>\<infinity>x. \<theta> x = 0"
    using * by auto
  assume "\<forall>\<^sub>\<infinity>x. \<tau>' x = 0"
  obtain t' \<sigma>' \<gamma>' \<theta>' def' where "update_config_raw config \<tau>' = (t', \<sigma>', \<gamma>', \<theta>', def')" and
    "t' = Femto_VHDL_raw.next_time t \<tau>'" and "\<sigma>' = Femto_VHDL_raw.next_state t \<tau>' \<sigma>" and
    "\<gamma>' = Femto_VHDL_raw.next_event t \<tau>' \<sigma>" and "\<theta>' = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def"
    using `config = (t, \<sigma>, \<gamma>, \<theta>, def)`  by (metis update_config_raw.simps)
  have "\<forall>\<^sub>\<infinity>x. Femto_VHDL_raw.add_to_beh \<sigma> \<theta> t t' x = 0"
    unfolding Femto_VHDL_raw.add_to_beh_def  using `\<forall>\<^sub>\<infinity>x. \<theta> x = 0`
    by (metis (mono_tags) upd_eventually_cofinite)
  thus "pred_prod top (pred_prod top (pred_prod top (pred_prod (\<lambda>f. \<forall>\<^sub>\<infinity>x. f x = 0) top))) (update_config_raw config \<tau>')"
    by (simp add: \<open>\<forall>\<^sub>\<infinity>x. \<theta> x = 0\<close> \<open>\<theta>' = Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def\<close> \<open>update_config_raw config \<tau>' = (t', \<sigma>', \<gamma>', \<theta>', def')\<close> add_to_beh2_eventually_cofinite)
qed

lift_definition simulate_fin_ss :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal conc_stmt \<Rightarrow>
  'signal transaction \<times> 'signal configuration  \<Rightarrow>  'signal transaction \<times> 'signal configuration \<Rightarrow> bool"
  is b_simulate_fin_ss .

end