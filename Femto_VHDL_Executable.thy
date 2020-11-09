(*
 * Copyright 2018-2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Femto_VHDL_Executable
  imports Femto_VHDL
begin

datatype sig = A | B | C

notation (output) A  ("A")
notation (output) B  ("B")
notation (output) C  ("C")

lemma UNIV_sig:
  "UNIV = {A, B, C}"
  by (auto intro: sig.exhaust)

instantiation sig :: enum
begin

definition enum_sig where
  "enum_sig = [A, B, C]"

definition enum_all_sig where
  "enum_all_sig P \<longleftrightarrow> P A \<and> P B \<and> P C"

definition enum_ex_sig where
  "enum_ex_sig P \<longleftrightarrow> P A \<or> P B \<or> P C"

instance proof
qed (simp_all only: enum_sig_def enum_all_sig_def enum_ex_sig_def UNIV_sig, simp_all)
end

lemma zero_upd:
  "0 (sig := None) = 0"
  by (auto simp add:zero_map zero_option_def)

definition to_transaction2' :: "'signal transaction \<Rightarrow> 'signal transaction_sig" where
  "to_transaction2' \<tau> = (\<lambda>s. Poly_Mapping.map (\<lambda>m. m s) \<tau>)"

lemma [code]:
  "to_transaction_sig \<tau> = to_transaction2' \<tau>"
  unfolding to_transaction2'_def
  by (transfer', unfold to_trans_raw_sig_def)
     (metis (mono_tags, hide_lams) "when"(1) when_def zero_fun_def)


lemma [code]:
  "to_transaction_sig_bit def \<tau> idx sig' = Poly_Mapping.mapp (\<lambda>n m s. if s \<noteq> sig' then m s else case m s of None \<Rightarrow> None 
                                                                                                       | Some v \<Rightarrow> if 0 < n \<and> to_bit idx (signal_of2 def \<tau> sig' (n - 1)) = to_bit idx v then None 
                                                                                                                   else if n = 0 \<and> to_bit idx def = to_bit idx v then None 
                                                                                                                   else Some (to_bit idx v)) \<tau>"
  unfolding poly_mapping_eq_iff lookup_mapp
  apply transfer'
  unfolding to_trans_raw_bit_def when_def zero_fun_def zero_option_def
  apply (rule ext)+
  by (auto split: val.splits)

code_pred (modes : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) beval_ind .

definition "functional_beval_ind t \<sigma> \<gamma> \<theta> def exp =
  Predicate.the (beval_ind_i_i_i_i_i_i_o t \<sigma> \<gamma> \<theta> def exp)"

value [code] "signals_in (Bassign_trans C Btrue 0)"

values "{x. beval_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) (Bsig A) x}"
value [code] "functional_beval_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) (Bsig A)"

values "{x. beval_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) (Band (Bsig A) (Bsig B)) x}"
value [code] "functional_beval_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) (Band (Bsig A) (Bsig B))"

values "{x. beval_ind 0 (\<lambda>x. Lv Neu (replicate 4 False)) {} 0 (\<lambda>x. Lv Neu (replicate 4 False)) (Bslice C 3 2) x}"
value [code] "functional_beval_ind 0 (\<lambda>x. Lv Neu (replicate 4 False)) {} 0 (\<lambda>x. Lv Neu (replicate 4 False)) (Bslice C 3 2)"

lemma [code]:
  "Poly_Mapping.mapp f (Pm_fmap xs) = Pm_fmap (fmmap_keys f (clearjunk0 xs))"
  apply (intro poly_mapping_eqI)
  apply transfer'
  unfolding fmlookup_default_def Pm_fmap.rep_eq fmmap_keys.rep_eq
  apply (auto split:option.splits)
  unfolding compute_keys_pp
   apply (simp add: clearjunk0_def fmdom'_notI)+
  by auto

theorem functional_beval_ind_completeness:
  assumes "beval_ind t \<sigma> \<gamma> \<theta> def exp v"
  shows "functional_beval_ind t \<sigma> \<gamma> \<theta> def exp = v"
  using assms unfolding functional_beval_ind_def beval_ind_i_i_i_i_i_i_o_def
  Predicate.the_def pred.sel
  by (auto intro!: simp add: beval_ind_deterministic)

theorem functional_beval_ind_soundness:
  assumes "bexp_wt \<Gamma> exp type" and "styping \<Gamma> \<sigma>" and "transtyping \<Gamma> \<theta>" and "styping \<Gamma> def"
  assumes "functional_beval_ind t \<sigma> \<gamma> \<theta> def exp = v"
  shows "beval_ind t \<sigma> \<gamma> \<theta> def exp v"
  using assms(5) theI'[OF beval_ind_progress_unique[OF assms(1-4)]]
  unfolding functional_beval_ind_def beval_ind_i_i_i_i_i_i_o_def Predicate.the_def pred.sel
  by blast

theorem functional_beval_ind_correctness:
  assumes "bexp_wt \<Gamma> exp type" and "styping \<Gamma> \<sigma>" and "transtyping \<Gamma> \<theta>" and "styping \<Gamma> def"
  shows "functional_beval_ind t \<sigma> \<gamma> \<theta> def exp = v \<longleftrightarrow> beval_ind t \<sigma> \<gamma> \<theta> def exp v"
  using functional_beval_ind_completeness functional_beval_ind_soundness
  using assms by blast

definition
  "test_beh = Pm_fmap (fmap_of_list [(1 :: nat, [A \<mapsto> Bv True, B \<mapsto> Bv False, C \<mapsto> Bv True])])"

lemma lookup0_fmdrop:
  "lookup0 (fmdrop x xa) = map_drop x (lookup0 xa)"
  by (auto simp add: fmlookup_default_def Finite_Map.map_filter_def map_drop_def zero_option_def
              split: option.splits)

lemma lookup0_fmupd:
  "lookup0 (fmupd a b m) a' = (if a = a' then b else lookup0 m a')"
  by (simp add: fmlookup_default_def)

(* TODO : streamline this proof; applying auto in the middle is ugly *)
lemma lookup0_update_with_none:
  "(lookup0 xs)(time := (lookup0 xs time)(sig := None)) =
    lookup0 (fmupd time (map_drop sig (lookup0 xs time)) xs)"
  apply (auto simp add: fmlookup_default_def Finite_Map.map_filter_def map_drop_def zero_option_def
              split: option.splits)
  unfolding lookup0_fmupd
proof (rule_tac[!] ext)
  fix a'
  assume "fmlookup xs time = None"
  thus "((lookup0 xs)(time := 0(sig := None))) a' =
            (if time = a' then \<lambda>x. if x \<noteq> sig then 0 x else None else lookup0 xs a')"
    by auto
next
  fix x2 a'
  assume "fmlookup xs time = Some x2"
  thus "((lookup0 xs)(time := x2(sig := None))) a' =
            (if time = a' then \<lambda>x. if x \<noteq> sig then x2 x else None else lookup0 xs a')"
    by auto
qed

lemma
  "override_on (lookup0 xs) (\<lambda>n. (lookup0 xs n)(sig := None)) {t<..t + dly} = lookup0 (fmmap_keys (\<lambda>t'. if t < t' \<and> t' \<le> t + dly then map_drop sig else id) xs)"
  by (rule ext) (auto simp add: override_on_def fmlookup_default_def zero_map map_drop_def map_filter_def split:option.splits)

lemma[code]:
  "purge (Pm_fmap xs) t dly sig def val = (let
                                              chopped = fmmap_keys (\<lambda>t'. if t < t' \<and> t' \<le> t + dly then map_drop sig else id);
                                              s1 = signal_of2 def (Pm_fmap xs) sig t;
                                              s2 = signal_of2 def (Pm_fmap xs) sig (t + dly);
                                              k2 = inf_time (to_transaction_sig (Pm_fmap xs)) sig (t + dly);
                                              chopped2 = fmmap_keys (\<lambda>t'. if t < t' \<and> t' < the k2 \<or> the k2 < t' \<and> t' \<le> t + dly then map_drop sig else id)
                                           in
                                              if s1 = val \<or> s2 \<noteq> val then
                                                  Pm_fmap (chopped xs)
                                              else
                                                  Pm_fmap (chopped2 xs))"
  by (transfer', rule ext)(auto simp add: Let_def override_on_def purge_raw_def fmlookup_default_def zero_map
                                         map_drop_def map_filter_def
                                        split:option.splits)

(*TODO : factoring this proof *)
lemma [code]:
  "combine_trans_bit_lifted (Pm_fmap xs) ps sign sig' now dly = (
      let                                           
        kset = fold (\<union>) (map (Poly_Mapping.keys o (\<lambda>\<tau>. to_transaction_sig \<tau> sig') o snd) ps) {}
      in 
        Pm_fmap (
                     fmmap_keys (\<lambda>t'. if t' \<le> now \<or> now + dly < t' then id else map_drop sig') xs
                        ++\<^sub>f
                    (fmap_of_list (map (\<lambda>t. (t, 
                      \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then (case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s) 
                          else  Some (Lv sign (map (\<lambda>p. bval_of (signal_of2 (fst p) (snd p) sig' t)) ps)))) (sorted_list_of_set kset)))
                )
  )"
  apply transfer
  unfolding combine_trans_bit_def Let_def comp_def  fmlookup_default_add
  apply (rule ext)+
  apply ( auto simp add: fmlookup_default_def zero_map map_drop_def map_filter_def 
                        split: option.splits)
proof -
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x now dly
  assume "sig \<noteq> sig'"
  assume "fmlookup xs x = None"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume " x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)
  hence "(fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x) = Some (\<lambda>s. if x \<le> now \<or> now + dly < x \<or> s \<noteq> sig' then case fmlookup xs x of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' x)) ps)))"
    unfolding fmlookup_of_list map_of_map_restrict restrict_in[OF **]
    by (auto)
  thus "None =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    using `sig \<noteq> sig'` `fmlookup xs x = None`
    by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig' :: "'a"
  fix sign x now dly
  assume "fmlookup xs x = None"
  assume "\<not> x \<le> now" and "\<not> now + dly < x"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume " x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"  
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)
  hence "(fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x) = Some (\<lambda>s. if x \<le> now \<or> now + dly < x \<or> s \<noteq> sig' then case fmlookup xs x of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' x)) ps)))"
    unfolding fmlookup_of_list map_of_map_restrict restrict_in[OF **]
    by (auto)
  thus "Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' x)) ps)) =       
        the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig'"
    using `\<not> x \<le> now` `\<not> now + dly < x` by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig' :: "'a"
  fix sign n  now dly
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume "n \<in> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}"
  have "\<And>init. finite init \<Longrightarrow> finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) init)"
    using *
  proof (induction ps)
    case Nil
    then show ?case by auto
  next
    case (Cons a ps)
    have "pred_prod (\<lambda>a. True) (\<lambda>f. finite {x. f x \<noteq> 0}) a"
      using Cons(3) by auto
    hence "finite {x. snd a x \<noteq> 0}"
      using pred_prod_inject surjective_pairing[of "a"] by metis
    have **: " (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) (a # ps)) init) = 
           fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      unfolding list.map(2) fold_Cons comp_def Un_empty_right by auto
    have "finite  ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      using `finite init` `finite {x. snd a x \<noteq> 0}` unfolding finite_Un 
      to_trans_raw_sig_def
      by (metis (mono_tags, lifting) finite_nat_iff_bounded mem_Collect_eq subset_eq zero_map zero_option_def)
    thus ?case
      using Cons by auto
  qed
  hence fin: "finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {})"
    by auto
  show " n |\<in>|
       (get_time \<circ>
        (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                     else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))) |`|
       fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    unfolding comp_def
    apply (intro fimage_eqI)
    using `n \<in> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}`
    unfolding keys_def fset_of_list_elem set_sorted_list_of_set[OF fin]
    by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x now dly
  assume "sig \<noteq> sig'"
  assume "fmlookup xs x = None"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume "x \<notin> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}"
  assume "sig \<noteq> sig'"
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)
  have "\<And>init. finite init \<Longrightarrow> finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) init)"
    using *
  proof (induction ps)
    case Nil
    then show ?case by auto
  next
    case (Cons a ps)
    have "pred_prod (\<lambda>a. True) (\<lambda>f. finite {x. f x \<noteq> 0}) a"
      using Cons(3) by auto
    hence "finite {x. snd a x \<noteq> 0}"
      using pred_prod_inject surjective_pairing[of "a"] by metis
    have **: " (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) (a # ps)) init) = 
           fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      unfolding list.map(2) fold_Cons comp_def Un_empty_right by auto
    have "finite  ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      using `finite init` `finite {x. snd a x \<noteq> 0}` unfolding finite_Un 
      to_trans_raw_sig_def
      by (metis (mono_tags, lifting) finite_nat_iff_bounded mem_Collect_eq subset_eq zero_map zero_option_def)
    thus ?case
      using Cons by auto
  qed
  hence fin: "finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {})"
    by auto
  have "False"
    using ** `x \<notin> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}` 
    unfolding set_sorted_list_of_set[OF fin] keys_def by auto
  thus "None =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig' :: "'a"
  fix sign x now dly
  assume "fmlookup xs x = None"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume "x \<notin> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}"
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)
  have "\<And>init. finite init \<Longrightarrow> finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) init)"
    using *
  proof (induction ps)
    case Nil
    then show ?case by auto
  next
    case (Cons a ps)
    have "pred_prod (\<lambda>a. True) (\<lambda>f. finite {x. f x \<noteq> 0}) a"
      using Cons(3) by auto
    hence "finite {x. snd a x \<noteq> 0}"
      using pred_prod_inject surjective_pairing[of "a"] by metis
    have **: " (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) (a # ps)) init) = 
           fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      unfolding list.map(2) fold_Cons comp_def Un_empty_right by auto
    have "finite  ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      using `finite init` `finite {x. snd a x \<noteq> 0}` unfolding finite_Un 
      to_trans_raw_sig_def
      by (metis (mono_tags, lifting) finite_nat_iff_bounded mem_Collect_eq subset_eq zero_map zero_option_def)
    thus ?case
      using Cons by auto
  qed
  hence fin: "finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {})"
    by auto
  have "False"
    using ** `x \<notin> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}` 
    unfolding set_sorted_list_of_set[OF fin] keys_def by auto
  thus "None =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig'"
    by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x2 x now dly
  assume "fmlookup xs x = Some x2"
  assume "sig \<noteq> sig'"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume "x \<in> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}"
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)
  hence "(fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x) = Some (\<lambda>s. if x \<le> now \<or> now + dly < x \<or> s \<noteq> sig' then case fmlookup xs x of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' x)) ps)))"
    unfolding fmlookup_of_list map_of_map_restrict restrict_in[OF **]
    by (auto)
  thus "x2 sig =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    using `sig \<noteq> sig'` `fmlookup xs x = Some x2` by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig' :: "'a"
  fix sign x2 x now dly
  assume "fmlookup xs x = Some x2"
  assume "\<not> x \<le> now " and " \<not> now + dly < x "
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume "x \<in> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}"
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"  
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)
  hence "(fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x) = Some (\<lambda>s. if x \<le> now \<or> now + dly < x \<or> s \<noteq> sig' then case fmlookup xs x of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' x)) ps)))"
    unfolding fmlookup_of_list map_of_map_restrict restrict_in[OF **]
    by (auto)
  thus " Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' x)) ps)) =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig'"
    using `\<not> x \<le> now` `\<not> now + dly < x` by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig' :: "'a"
  fix sign x2 n now dly
  assume "fmlookup xs n = Some x2"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume "n \<in> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}"
  have "\<And>init. finite init \<Longrightarrow> finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) init)"
    using *
  proof (induction ps)
    case Nil
    then show ?case by auto
  next
    case (Cons a ps)
    have "pred_prod (\<lambda>a. True) (\<lambda>f. finite {x. f x \<noteq> 0}) a"
      using Cons(3) by auto
    hence "finite {x. snd a x \<noteq> 0}"
      using pred_prod_inject surjective_pairing[of "a"] by metis
    have **: " (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) (a # ps)) init) = 
           fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      unfolding list.map(2) fold_Cons comp_def Un_empty_right by auto
    have "finite  ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      using `finite init` `finite {x. snd a x \<noteq> 0}` unfolding finite_Un 
      to_trans_raw_sig_def
      by (metis (mono_tags, lifting) finite_nat_iff_bounded mem_Collect_eq subset_eq zero_map zero_option_def)
    thus ?case
      using Cons by auto
  qed
  hence fin: "finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {})"
    by auto
  show " n |\<in>|
       (get_time \<circ>
        (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                     else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))) |`|
       fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    unfolding comp_def
    apply (intro fimage_eqI)
    using `n \<in> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}`
    unfolding keys_def fset_of_list_elem set_sorted_list_of_set[OF fin]
    by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x2 x now dly
  assume "fmlookup xs x = Some x2"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"  
  assume "x \<notin> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}"
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)  
  have "\<And>init. finite init \<Longrightarrow> finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) init)"
    using *
  proof (induction ps)
    case Nil
    then show ?case by auto
  next
    case (Cons a ps)
    have "pred_prod (\<lambda>a. True) (\<lambda>f. finite {x. f x \<noteq> 0}) a"
      using Cons(3) by auto
    hence "finite {x. snd a x \<noteq> 0}"
      using pred_prod_inject surjective_pairing[of "a"] by metis
    have **: " (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) (a # ps)) init) = 
           fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      unfolding list.map(2) fold_Cons comp_def Un_empty_right by auto
    have "finite  ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      using `finite init` `finite {x. snd a x \<noteq> 0}` unfolding finite_Un 
      to_trans_raw_sig_def
      by (metis (mono_tags, lifting) finite_nat_iff_bounded mem_Collect_eq subset_eq zero_map zero_option_def)
    thus ?case
      using Cons by auto
  qed
  hence fin: "finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {})"
    by auto
  hence False
    using ** `x \<notin> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}`
    unfolding set_sorted_list_of_set[OF fin] keys_def by auto
  thus " x2 sig =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig' :: "'a"
  fix sign x2 x now dly
  assume "fmlookup xs x = Some x2"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"  
  assume "x \<notin> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}"
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)  
  have "\<And>init. finite init \<Longrightarrow> finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) init)"
    using *
  proof (induction ps)
    case Nil
    then show ?case by auto
  next
    case (Cons a ps)
    have "pred_prod (\<lambda>a. True) (\<lambda>f. finite {x. f x \<noteq> 0}) a"
      using Cons(3) by auto
    hence "finite {x. snd a x \<noteq> 0}"
      using pred_prod_inject surjective_pairing[of "a"] by metis
    have **: " (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) (a # ps)) init) = 
           fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      unfolding list.map(2) fold_Cons comp_def Un_empty_right by auto
    have "finite  ({k. to_trans_raw_sig (snd a) sig' k \<noteq> 0} \<union> init)"
      using `finite init` `finite {x. snd a x \<noteq> 0}` unfolding finite_Un 
      to_trans_raw_sig_def
      by (metis (mono_tags, lifting) finite_nat_iff_bounded mem_Collect_eq subset_eq zero_map zero_option_def)
    thus ?case
      using Cons by auto
  qed
  hence fin: "finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {})"
    by auto
  hence False
    using ** `x \<notin> fold (\<union>) (map (\<lambda>x. Femto_VHDL_raw.keys (to_trans_raw_sig (snd x) sig')) ps) {}`
    unfolding set_sorted_list_of_set[OF fin] keys_def by auto
  thus "  None =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig'"
    by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x now dly
  assume "fmlookup xs x = None"
  assume "x \<le> now"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)
  thus "None =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    using `x \<le> now` `fmlookup xs x = None` unfolding fmlookup_of_list map_of_map_restrict 
    restrict_map_def by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x now dly
  assume "fmlookup xs x = None"
  assume "now + dly < x"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)
  thus "None =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    using `now + dly < x` `fmlookup xs x = None` unfolding fmlookup_of_list map_of_map_restrict 
    restrict_map_def by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x now dly
  assume "fmlookup xs x = None"
  assume "now + dly < x"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)
  thus "None =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    using `now + dly < x` `fmlookup xs x = None` unfolding fmlookup_of_list map_of_map_restrict 
    restrict_map_def by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x now dly
  assume "fmlookup xs x = None"
  assume "\<not> now + dly < x"
  assume "sig \<noteq> sig'"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)
  thus "None =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    using `sig \<noteq> sig'` `fmlookup xs x = None` unfolding fmlookup_of_list map_of_map_restrict 
    restrict_map_def by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x2 x now dly
  assume "fmlookup xs x = Some x2"
  assume "x \<le> now"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"  
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)  
  thus " x2 sig =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    using `x \<le> now` `fmlookup xs x = Some x2`
    unfolding fmlookup_of_list map_of_map_restrict restrict_map_def by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x2 x now dly
  assume "fmlookup xs x = Some x2"
  assume "x \<le> now"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"  
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)  
  thus " x2 sig =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    using `x \<le> now` `fmlookup xs x = Some x2`
    unfolding fmlookup_of_list map_of_map_restrict restrict_map_def by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x2 x now dly
  assume "fmlookup xs x = Some x2"
  assume "now + dly < x"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"  
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)  
  thus " x2 sig =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    using `now + dly < x` `fmlookup xs x = Some x2`
    unfolding fmlookup_of_list map_of_map_restrict restrict_map_def by auto
next
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  fix ps :: "(val \<times> (nat \<Rightarrow> 'a \<Rightarrow> val option)) list"
  fix sig sig' :: "'a"
  fix sign x2 x now dly
  assume "fmlookup xs x = Some x2"
  assume "now + dly < x"
  assume *: "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) ps"  
  assume "x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
  hence "x |\<in>| fmdom (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))"
    by auto
  have **: "x \<in> set (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))"
    using `x |\<in>| fset_of_list (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))`
    by (simp add: fset_of_list_elem)  
  thus " x2 sig =
       the (fmlookup
             (fmap_of_list
               (map (\<lambda>t. (t, \<lambda>s. if t \<le> now \<or> now + dly < t \<or> s \<noteq> sig' then case fmlookup xs t of None \<Rightarrow> None | Some m \<Rightarrow> m s
                                 else Some (Lv sign (map (\<lambda>p. bval_of (Femto_VHDL_raw.to_signal (get_time p) (to_trans_raw_sig (snd p)) sig' t)) ps))))
                 (sorted_list_of_set (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) sig' k \<noteq> 0}) ps) {}))))
             x)
        sig"
    using `now + dly < x` `fmlookup xs x = Some x2`
    unfolding fmlookup_of_list map_of_map_restrict restrict_map_def by auto  
qed

lemma [code]: 
  "purge' \<tau> t dly sig def (Bv b) = purge \<tau> t dly sig def (Bv b)"
  apply transfer'
  unfolding purge_raw'_def by auto

lemma purge'_code[code]: 
  "purge' \<tau> t dly sig def (Lv sign bs) = combine_trans_bit_lifted \<tau> (zip (map (\<lambda>n. Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..< length bs]) 
                                                                                   (map (\<lambda>n. purge (to_transaction_sig_bit def \<tau> n sig) t dly sig (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..< length bs])) sign sig t dly"
  apply transfer'
  unfolding purge_raw'_def by auto


value [code] "lookup (purge' (0 :: sig transaction) 1 1 C (Bv False) (Bv True)) 1 C"

lemma [code]:
  "post_necessary dly (Pm_fmap xs) t sig v def = (signal_of2 def (Pm_fmap xs) sig (t + dly) \<noteq> v)"
  by transfer' auto


lemma [code]:
  "post sig v (Pm_fmap xs) t =
                          (let
                             current  = lookup0 xs t;
                             chopped = fmmap_keys (\<lambda>t'. if t < t' then map_drop sig else id);
                             updated  = fmupd t (current(sig \<mapsto> v)) xs
                           in
                             Pm_fmap (chopped updated))"
  by (transfer', unfold Let_def post_raw_def)
     (rule ext, auto simp add: fmlookup_default_def zero_map map_drop_def map_filter_def
                        split: option.splits)

lemma [code]:
  "preempt sig (Pm_fmap xs) t =
                          (let
                             chopped = fmmap_keys (\<lambda>t'. if t \<le> t' then map_drop sig else id)
                           in
                             Pm_fmap (chopped xs))"
  by (transfer', unfold Let_def preempt_raw_def)
     (rule ext, auto simp add: fmlookup_default_def zero_map map_drop_def map_filter_def
                        split: option.splits)


lemma [code]:
  "trans_post sig v def (Pm_fmap xs) t dly = (let
                                                current  = lookup0 xs (t + dly);
                                                chopped1 = fmmap_keys (\<lambda>t'. if t + dly < t' then map_drop sig else id);
                                                chopped2 = fmmap_keys (\<lambda>t'. if t + dly \<le> t' then map_drop sig else id);
                                                updated  = fmupd (t + dly) (current(sig \<mapsto> v)) xs
                                              in
                                                if signal_of2 def (Pm_fmap xs) sig (t + (dly - 1)) \<noteq> v then Pm_fmap (chopped1 updated) else Pm_fmap (chopped2 xs))"
  by (transfer', unfold Let_def  trans_post_raw_def preempt_raw_def
                        post_raw_def)
     (rule ext, auto simp add: fmlookup_default_def zero_map map_drop_def map_filter_def
                        split: option.splits)

values "{x. beval_ind 2 (\<lambda>x. Bv False) {} test_beh (\<lambda>x. Bv False) (Bsig_delayed A 1) x}"
values "{x. beval_ind 2 (\<lambda>x. Bv False) {} test_beh (\<lambda>x. Bv False) (Bsig_delayed B 1) x}"
values "{x. beval_ind 2 (\<lambda>x. Bv False) {} test_beh (\<lambda>x. Bv False) (Bsig_delayed C 1) x}"

term "seq_exec_ind"

code_pred (modes : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) seq_exec_ind .

definition "functional_seq_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> =
  Predicate.the (seq_exec_ind_i_i_i_i_i_i_i_o t \<sigma> \<gamma> \<theta> def cs \<tau>)"

values "{x. seq_exec_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) (Bnull :: sig seq_stmt) empty_trans x}"
value [code] "functional_seq_exec_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) (Bnull :: sig seq_stmt) empty_trans"

lemma functional_seq_exec_ind_completeness:
  assumes "seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
  shows "functional_seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> = \<tau>'"
  using assms unfolding functional_seq_exec_ind_def seq_exec_ind_i_i_i_i_i_i_i_o_def
  Predicate.the_def pred.sel
  by (auto intro!: simp add: seq_exec_ind_deterministic)

lemma functional_seq_exec_ind_soundness:
  assumes "seq_wt \<Gamma> ss" and "styping \<Gamma> \<sigma>" and "transtyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "transtyping \<Gamma> \<tau>"
  assumes "functional_seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> = \<tau>'"
  shows   "seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
  using assms(6) theI'[OF seq_exec_ind_unique_progress[OF assms(1-5)], of "t" "\<gamma>"]
  unfolding functional_seq_exec_ind_def seq_exec_ind_i_i_i_i_i_i_i_o_def Predicate.the_def pred.sel
  by blast

theorem functional_seq_exec_correctness:
  assumes "seq_wt \<Gamma> ss" and "styping \<Gamma> \<sigma>" and "transtyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "transtyping \<Gamma> \<tau>"
  shows "functional_seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> = \<tau>' \<longleftrightarrow> seq_exec_ind t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
  using assms functional_seq_exec_ind_completeness functional_seq_exec_ind_soundness by blast

definition
  "exp1 = Bsig C"

definition
  "exp2 = Bnand (Bsig A) (Bsig B)"

definition
  "exp3 = Bnot (Bor (Bsig C) (Bsig B))"

definition
  "seq1 = Bassign_trans C exp2 1"

definition
  "seq2 = Bassign_inert B exp3 2"

definition
  "seq3 = Bguarded exp1 seq1 seq2"

values "{lookup x 1 C | x. seq_exec_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) (Bcomp seq1 seq2) empty_trans x}"
value [code] "lookup (functional_seq_exec_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) (Bcomp seq1 seq2) empty_trans) 1 C"

values "{lookup x 2 C | x. seq_exec_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) (Bguarded exp1 seq1 seq2) empty_trans x}"
value [code] "lookup (functional_seq_exec_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) (Bguarded exp1 seq1 seq2) empty_trans) 2 C"

values "{lookup x 1 C | x. seq_exec_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) seq1 empty_trans x}"
value [code] "lookup (functional_seq_exec_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) seq1 empty_trans) 1 C"

values "{lookup x 2 C | x. seq_exec_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) seq2 empty_trans x}"
value [code] "lookup (functional_seq_exec_ind 0 (\<lambda>x. Bv False) {} 0 (\<lambda>x. Bv False) seq2 empty_trans) 2 C"

term "fmmap_keys (\<lambda>x. fmadd)"

lemma [code]:
  "map_add_trans (Pm_fmap xs) (Pm_fmap ys) =
                               Pm_fmap (fmmap_keys (\<lambda>k v. lookup0 xs k ++ lookup0 ys k) (xs ++\<^sub>f ys))"
  by (transfer') (rule ext, auto simp add:fmlookup_default_def map_add_subsumed1 split:option.splits)

lemma [code]:
  "map_diff_trans (Pm_fmap xs) (Pm_fmap ys) =
                     Pm_fmap (fmmap_keys (\<lambda>k v. map_diff (lookup0 xs k) (lookup0 ys k)) (xs ++\<^sub>f ys))"
  by (transfer') (rule ext, auto simp add: fmlookup_default_def zero_map split:option.splits)

lemma [code]:
  "clean_zip (Pm_fmap ts) (Pm_fmap ts1, s1) (Pm_fmap ts2, s2) =
      Pm_fmap (fmmap_keys
              (\<lambda>k v s. if s \<in> s1 then lookup0 ts1 k s else if s \<in> s2 then lookup0 ts2 k s else lookup0 ts k s)
              (ts ++\<^sub>f ts1 ++\<^sub>f ts2))"
  apply transfer'
  apply (rule ext)
  unfolding clean_zip_raw_def Let_def
  by (auto split:prod.splits option.splits simp add: fmlookup_default_def zero_map)

code_pred (modes : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) conc_exec_ind .

definition "functional_conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> =
                                     Predicate.the (conc_exec_ind_i_i_i_i_i_i_i_o t \<sigma> \<gamma> \<theta> def cs \<tau>)"

values "{lookup x 2 C | x. conc_exec_ind 1 (\<lambda>x. Bv False) {A, B} test_beh (\<lambda>x. Bv False) (process {A} : seq1) empty_trans x}"
value [code] "lookup (functional_conc_exec_ind 1 (\<lambda>x. Bv False) {A, B} test_beh (\<lambda>x. Bv False) (process {A} : seq1) empty_trans) 2 C"

values "{lookup x 3 B | x. conc_exec_ind 1 (\<lambda>x. Bv False) {A, C} test_beh (\<lambda>x. Bv False) ((process {A} : seq1) || (process {C} : seq2)) empty_trans x}"
value [code] "lookup (functional_conc_exec_ind 1 (\<lambda>x. Bv False) {A, C} test_beh (\<lambda>x. Bv False) ((process {A} : seq1) || (process {C} : seq2)) empty_trans) 3 B"

lemma functional_conc_exec_ind_completeness:
  assumes "conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  shows "functional_conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> = \<tau>'"
  using assms unfolding functional_conc_exec_ind_def conc_exec_ind_i_i_i_i_i_i_i_o_def
  Predicate.the_def pred.sel
  by (auto intro!: simp add: conc_exec_ind_deterministic)

lemma functional_conc_exec_ind_soundness:
  assumes "conc_wt \<Gamma> cs" and "styping \<Gamma> \<sigma>" and "transtyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "transtyping \<Gamma> \<tau>"
  assumes "functional_conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> = \<tau>'"
  shows "conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  using assms(6) theI'[OF conc_exec_ind_unique_progress[OF assms(1-5)], of "t" "\<gamma>"]
  unfolding functional_conc_exec_ind_def conc_exec_ind_i_i_i_i_i_i_i_o_def Predicate.the_def pred.sel
  by blast

theorem functional_conc_exec_ind_correctness:
  assumes "conc_wt \<Gamma> cs" and "styping \<Gamma> \<sigma>" and "transtyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "transtyping \<Gamma> \<tau>"
  shows "functional_conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> = \<tau>' \<longleftrightarrow> conc_exec_ind t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  using assms functional_conc_exec_ind_completeness functional_conc_exec_ind_soundness
  by blast

value [code] "quiet (empty_trans :: sig transaction) {}"

lemma [code]:
  "Poly_Mapping.update k v (Pm_fmap xs) = Pm_fmap (fmupd k v xs)"
  by (transfer, auto simp add:fmlookup_default_def)

value [code] "rem_curr_trans 0 (empty_trans :: sig transaction)"

lemma lookup0_zero_fun:
  "lookup0 xs = (\<lambda>k. 0) \<longleftrightarrow> clearjunk0 xs = fmempty"
  by (metis PM_clearjunk0_cong Pm_fmap.rep_eq aux compute_keys_pp compute_zero_pp
            fmap_exhaust fmdom'_fmupd insert_iff lookup_not_eq_zero_eq_in_keys)

lemma LEAST_ext:
  assumes "\<And>n. P n = Q n"
  shows "(LEAST n. P n) = (LEAST n. Q n)"
  using assms by auto

lemma clearjunk0_fmupd_with_0:
  "clearjunk0 (fmupd x 0 m) = fmdrop x (clearjunk0 m)"
proof -
  have "clearjunk0 (fmupd x 0 m) = fmfilter (\<lambda>k. fmlookup (fmupd x 0 m) k \<noteq> Some 0) (fmupd x 0 m)"
    unfolding clearjunk0_def by auto
  also have "... = fmfilter (\<lambda>k. fmlookup (fmupd x 0 m) k \<noteq> Some 0) m"
    by auto
  also have "... = fmfilter (\<lambda>k. k \<noteq> x \<and> fmlookup m k \<noteq> Some 0) m"
    by (metis fmupd_lookup)
  also have "... = fmfilter (\<lambda>k. k \<noteq> x) (fmfilter (\<lambda>k. fmlookup m k \<noteq> Some 0) m)"
    unfolding fmfilter_comp by auto
  also have "... = fmfilter (\<lambda>k. k \<noteq> x) (clearjunk0 m)"
    unfolding clearjunk0_def by auto
  also have "... = fmdrop x (clearjunk0 m)"
    by (simp add: fmfilter_alt_defs(1))
  finally show ?thesis by auto
qed

lemma sorted_list_fmdom_fmupd:
  "sorted_list_of_fset (fmdom (fmupd x y m)) = insort x (sorted_list_of_fset (fmdom (fmdrop x m)))"
proof -
  have "fmdom (fmupd x y m) = finsert x (fmdom m)"
    by auto
  hence "sorted_list_of_fset (fmdom (fmupd x y m)) = sorted_list_of_fset (finsert x (fmdom m))"
    by auto
  also have "... = insort x (sorted_list_of_fset (fmdom m - {|x|}))"
    by (auto simp add: sorted_list_of_fset.rep_eq)
  also have "... = insort x (sorted_list_of_fset (fmdom (fmdrop x m)))"
    by auto
  finally show "sorted_list_of_fset (fmdom (fmupd x y m)) =
                   insort x (sorted_list_of_fset (fmdom (fmdrop x m)))"
    by auto
qed

lemma sorted_list_of_fmap_fmupd:
  "sorted_list_of_fmap (fmupd x y m) =
   map (\<lambda>k. (k, the (fmlookup (fmupd x y m) k))) (insort x (sorted_list_of_fset (fmdom (fmdrop x m))))"
proof -
  have "sorted_list_of_fset (fmdom (fmupd x y m)) =
                   insort x (sorted_list_of_fset (fmdom (fmdrop x m)))"
    using sorted_list_fmdom_fmupd by auto
  thus "sorted_list_of_fmap (fmupd x y m) =
    map (\<lambda>k. (k, the (fmlookup (fmupd x y m) k))) (insort x (sorted_list_of_fset (fmdom (fmdrop x m))))"
    unfolding sorted_list_of_fmap_def by auto
qed

lemma clearjunk0_fmupd_neq_0:
  "y \<noteq> 0 \<Longrightarrow> clearjunk0 (fmupd x y m) = fmupd x y (clearjunk0 m)"
  by (rule fmap_ext) (auto simp add: clearjunk0_def)

lemma fst_hd_list_is_hd_map:
  "xs \<noteq> [] \<Longrightarrow> fst (hd xs) = hd (map fst xs)"
  by (induction xs) auto

lemma dom_only:
  "m \<noteq> fmempty \<Longrightarrow> fst (hd (sorted_list_of_fmap m)) = hd (sorted_list_of_fset (fmdom m))"
proof -
  assume a1: "m \<noteq> fmempty"
  obtain aa :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> 'a" where
    "\<forall>f fa. fa = f \<or> map_of (sorted_list_of_fmap fa) (aa fa f) \<noteq> map_of (sorted_list_of_fmap f) (aa fa f)"
    by (metis fmap_ext map_of_sorted_list)
  then have " fst (hd (sorted_list_of_fmap m)) = hd (map fst (sorted_list_of_fmap m))"
    using a1 by (metis (no_types) bot_fset.rep_eq fmdom_empty list.map_sel(1) list.simps(8)
                 map_of_sorted_list sorted_list_of_fmap_def sorted_list_of_fset.rep_eq
                 sorted_list_of_set_empty)
  also have "... = hd (sorted_list_of_fset (fmdom m))"
    unfolding sorted_list_of_fmap_def by (simp add: o_def)
  finally show ?thesis by auto
qed

lemma obtain_neq_empty':
  fixes m :: "('a, 'b \<rightharpoonup> 'c) fmap"
  assumes "clearjunk0 m \<noteq> fmempty"
  shows  "\<exists>k. lookup0 m k \<noteq> Map.empty"
proof -
  have *: "\<And>k. fmlookup (clearjunk0 m) k \<noteq> Some (0 :: 'b \<rightharpoonup> 'c)"
    unfolding clearjunk0_def by auto
  obtain k where k_prop: "fmlookup (clearjunk0 m) k \<noteq> None"
    using assms by (metis fmap_ext fmempty_lookup)
  with * have "fmlookup (clearjunk0 m) k \<noteq> Some 0"
    by auto
  then obtain val where "fmlookup (clearjunk0 m) k = Some val" and "val \<noteq> 0"
    using k_prop by auto
  hence "val \<noteq> Map.empty"
    by (auto simp add:zero_map)
  hence "lookup0 (clearjunk0 m) k \<noteq> Map.empty"
    using `fmlookup (clearjunk0 m) k = Some val` unfolding fmlookup_default_def
    by auto
  hence "lookup0 m k \<noteq> Map.empty"
    unfolding clearjunk0_def
    by (metis \<open>lookup0 (clearjunk0 m) k \<noteq> Map.empty\<close> lookup0_clearjunk0)
  thus ?thesis
    by (intro exI[where x="k"])
qed

lemma obtain_neq_empty:
  fixes m :: "('a, 'b \<rightharpoonup> 'c) fmap"
  assumes "clearjunk0 m \<noteq> fmempty"
  obtains k where "lookup0 m k \<noteq> Map.empty"
  using obtain_neq_empty'[OF assms] by blast

lemma hd_after_insert_larger_key:
  assumes "xs \<noteq> []"
  assumes "hd xs < x"
  shows "hd (insort x xs) = hd xs"
  by (metis assms insort_key.simps(2) leD list.collapse list.sel(1))

(* TODO : streamline this ugly proof! *)
lemma least_fst_hd_sorted:
  fixes xs :: "('a::wellorder, 'b \<Rightarrow> 'c option) fmap"
  assumes "clearjunk0 xs \<noteq> fmempty"
  shows "(LEAST n. lookup0 xs n \<noteq> Map.empty) = fst (hd (sorted_list_of_fmap (clearjunk0 xs)))"
  using assms
proof (induction xs rule: fmap_induct)
  case fmempty
  then show ?case by (auto simp add: clearjunk0_def)
next
  case (fmupd x y m)
  have "clearjunk0 m = fmempty \<or> clearjunk0 m \<noteq> fmempty"
    by auto
  moreover
  { assume *: "clearjunk0 m = fmempty"
    have "(LEAST n. lookup0 (fmupd x y m) n \<noteq> Map.empty) = x"
    proof (rule Least_equality)
      have **: "x \<in> fmdom' (clearjunk0 (fmupd x y m))"
        using fmupd(3) *  by (metis (mono_tags, hide_lams) compute_keys_pp compute_lookup_pp
                                    in_keys_iff  lookup0_fmupd lookup0_zero_fun)
      have " lookup0 (fmupd x y m) x = lookup0 (clearjunk0 (fmupd x y m)) x"
        using lookup0_clearjunk0 by metis
      moreover have "... \<noteq> Map.empty"
        using fmupd(3)
        apply (auto simp add:fmlookup_default_def split:option.splits)
        apply (metis "*"calculation fmlookup_default_if(2) lookup0_fmupd lookup0_zero_fun)
        using clearjunk0_nonzero[OF **] zero_fun_def zero_option_def
        by (metis "**" PM_clearjunk0_cong calculation clearjunk0_map_of_SomeD clearjunk0_nonzero
                       compute_keys_pp ext fmlookup_default_def fmupd_lookup option.simps(5))
      ultimately show "lookup0 (fmupd x y m) x \<noteq> Map.empty"
        by auto
    next
      { fix ya
        assume "\<not> x \<le> ya" hence "ya <  x" by auto
        hence "lookup0 (fmupd x y m) ya = lookup0 m ya"
          unfolding lookup0_fmupd by auto
        moreover have "lookup0 m ya = Map.empty"
          using * lookup0_zero_fun zero_map by force
        ultimately have "lookup0 (fmupd x y m) ya =  Map.empty"
          by auto
      }
      thus "\<And>ya. lookup0 (fmupd x y m) ya \<noteq> Map.empty \<Longrightarrow> x \<le> ya "
        by blast
    qed
    moreover have " fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) = x"
    proof -
      have "fmlookup (fmupd x y m) x \<noteq> Some 0"
        using fmupd(3) by (metis "*" fmupd_lookup lookup0_fmupd lookup0_zero_fun option.sel)
      hence "fmdom (clearjunk0 (fmupd x y m)) =  finsert x (fmdom (clearjunk0 m))"
        by (auto simp add:clearjunk0_def)
      also have "... = {|x|}"
        using * by auto
      finally have "fmdom (clearjunk0 (fmupd x y m)) =  {|x|}"
        by auto
      moreover have "the (fmlookup (clearjunk0 (fmupd x y m)) x) = y"
      proof -
        have "fmlookup (fmupd x y m) x \<noteq> Some 0"
          using \<open>fmlookup (fmupd x y m) x \<noteq> Some 0\<close> by blast
        then show ?thesis
          by (simp add: clearjunk0_def)
      qed
      ultimately have "sorted_list_of_fmap (clearjunk0 (fmupd x y m)) = [(x, y)]"
        unfolding sorted_list_of_fmap_def sorted_list_of_fset_def by auto
      thus ?thesis by auto
    qed
    ultimately have ?case by auto }

  moreover
  { assume "clearjunk0 m \<noteq> fmempty"
    with fmupd(1) have ind: "(LEAST n. lookup0 m n \<noteq> Map.empty) = fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
      by auto
    obtain cur_least where cur_least_def: "cur_least = (LEAST n. lookup0 m n \<noteq> Map.empty) "
      by auto
    consider (new) "x < cur_least" | (old) "cur_least \<le> x"
      using le_less_linear by blast
    hence ?case
    proof (cases)
      case new
      have "lookup0 (fmupd x y m) x = Map.empty \<or> lookup0 (fmupd x y m) x \<noteq> Map.empty"
        by auto
      moreover
      { assume "lookup0 (fmupd x y m) x = Map.empty"
        hence "(LEAST n. lookup0 (fmupd x y m) n \<noteq> Map.empty) =
               (LEAST n. n \<noteq> x \<and> lookup0 (fmupd x y m) n \<noteq> Map.empty)"
          by metis
        also have "... = (LEAST n. lookup0 m n \<noteq> Map.empty)"
          apply (rule LEAST_ext)
          unfolding lookup0_fmupd using fmupd.hyps zero_map by force
        also have "... = fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          using ind by auto
        finally have lexpand: "(LEAST n. lookup0 (fmupd x y m) n \<noteq> Map.empty) =
                                                      fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          by auto
        have "y = 0"
          using `lookup0 (fmupd x y m) x = Map.empty`
          by (auto simp add:zero_map)
        have "clearjunk0 (fmupd x y m) = fmdrop x (clearjunk0 m)"
          using clearjunk0_fmupd_with_0 unfolding `y = 0` by metis
        also have "... = clearjunk0 m"
          using fmupd(2)  by (simp add: clearjunk0_def fmap_ext)
        finally have "clearjunk0 (fmupd x y m) = clearjunk0 m"
          by auto
        hence "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) =
                                                      fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          by auto
        with lexpand have ?thesis by auto }
      moreover
      { assume "lookup0 (fmupd x y m) x \<noteq> Map.empty"
        hence "y \<noteq> Map.empty" by auto
        have lexpand2: "(LEAST n. lookup0 (fmupd x y m) n \<noteq> Map.empty) = x"
        proof (rule Least_equality)
          show "lookup0 (fmupd x y m) x \<noteq> Map.empty"
            using `lookup0 (fmupd x y m) x \<noteq> Map.empty` by auto
        next
          { fix ya
            assume "\<not> x \<le> ya" hence "ya < x" by auto
            hence "lookup0 (fmupd x y m) ya = lookup0 m ya"
              unfolding lookup0_fmupd by auto
            have "ya < cur_least"
              using `ya < x` and `x < cur_least` by auto
            hence "lookup0 m ya = Map.empty"
              unfolding cur_least_def using not_less_Least by auto
            hence "lookup0 (fmupd x y m) ya = Map.empty"
              using `lookup0 (fmupd x y m) ya = lookup0 m ya` by auto }
          thus "\<And>ya. lookup0 (fmupd x y m) ya \<noteq> Map.empty \<Longrightarrow> x \<le> ya "
            by auto
        qed
        have push_clearjunk0: "clearjunk0 (fmupd x y m) = fmupd x y (clearjunk0 m)"
          by (metis \<open>y \<noteq> Map.empty\<close> clearjunk0_fmupd_neq_0 zero_map)
        hence swap_cj_fmupd: "sorted_list_of_fmap (clearjunk0 (fmupd x y m)) =
               sorted_list_of_fmap (fmupd x y (clearjunk0 m))"
          by auto
        have "... =
            map (\<lambda>k. (k, the (fmlookup (fmupd x y (clearjunk0 m)) k)))
                                              (insort x (sorted_list_of_fset (fmdom (fmdrop x (clearjunk0 m)))))"
            (is "?simple = ?complex")
          using sorted_list_of_fmap_fmupd by auto
        have "fmdrop x (clearjunk0 m) = clearjunk0 m"
          by (simp add: fmupd clearjunk0_def fmap_ext)
        hence "sorted_list_of_fset (fmdom (fmdrop x (clearjunk0 m))) =
               sorted_list_of_fset (fmdom (clearjunk0 m))"
          by auto
        moreover have "insort x (sorted_list_of_fset (fmdom (clearjunk0 m))) =
            x # (sorted_list_of_fset (fmdom (clearjunk0 m)))"
          using new unfolding cur_least_def
          using ind  unfolding dom_only[OF `clearjunk0 m \<noteq> fmempty`]
          by (metis (no_types, lifting) insort_key.simps(1) insort_key.simps(2) less_imp_le list.collapse)
        ultimately have x_as_hd: "insort x (sorted_list_of_fset (fmdom (fmdrop x (clearjunk0 m)))) =
               x # sorted_list_of_fset (fmdom (clearjunk0 m))"
          by auto
        have "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) =  x"
          using swap_cj_fmupd `?simple = ?complex` x_as_hd by auto
        with lexpand2 have ?thesis by auto }
      ultimately show ?thesis by auto
    next
      case old
      have "x \<noteq> cur_least"
      proof (rule ccontr)
        assume "\<not> x \<noteq> cur_least"
        hence "x = cur_least" by auto
        obtain k where k_not_emp: "lookup0 m k \<noteq> Map.empty"
          using `clearjunk0 m \<noteq> fmempty`
          by (smt Pm_fmap.rep_eq clearjunk0_def compute_keys_pp fmdom'_filter fmdom'_notI
                  fmfilter_false fmlookup_default_if(1) fmupd(2) in_keys_iff member_filter)
        hence "lookup0 m x \<noteq> Map.empty"
          using LeastI[where P = "\<lambda>x. lookup0 m x \<noteq> Map.empty", OF k_not_emp] `x = cur_least`
          unfolding cur_least_def by auto
        thus "False"
          using fmupd(2) by (simp add: zero_fun_def zero_option_def)
      qed
      hence "cur_least < x" using old by auto
      have lexpand_old:"(LEAST n. lookup0 (fmupd x y m) n \<noteq> Map.empty) = cur_least"
      proof (rule Least_equality)
        have eqlookup0: "lookup0 (fmupd x y m) cur_least = lookup0 m cur_least"
          using `x \<noteq> cur_least` unfolding lookup0_fmupd by auto
        obtain k where wit: "lookup0 m k \<noteq> Map.empty"
          using obtain_neq_empty[OF `clearjunk0 m \<noteq> fmempty`] by auto
        hence "lookup0 m cur_least \<noteq> Map.empty"
          using LeastI[of "\<lambda>x. lookup0 m x \<noteq> Map.empty", OF wit] unfolding cur_least_def
          by auto
        thus "lookup0 (fmupd x y m) cur_least \<noteq> Map.empty"
          using eqlookup0 by auto
      next
        { fix ya
          assume "\<not> cur_least \<le> ya" hence "ya < cur_least" by auto
          hence "ya < x" using `cur_least < x` by auto
          hence "lookup0 (fmupd x y m) ya = lookup0 m ya"
            unfolding lookup0_fmupd by auto
          also have "...  = Map.empty"
            using `ya < cur_least` cur_least_def not_less_Least by auto
          finally have "lookup0 (fmupd x y m) ya = Map.empty"
            by auto }
        thus "\<And>ya. lookup0 (fmupd x y m) ya \<noteq> Map.empty \<Longrightarrow> cur_least \<le> ya "
          by blast
      qed
      have fi_rexpand: "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) =
            hd (sorted_list_of_fset (fmdom (clearjunk0 (fmupd x y m))))"
        using dom_only[OF `clearjunk0 (fmupd x y m) \<noteq> fmempty`] by auto

      have "y = Map.empty \<or> y \<noteq> Map.empty" by auto
      moreover
      { assume "y = Map.empty"
        hence "clearjunk0 (fmupd x y m) = fmdrop x (clearjunk0 m)"
          using clearjunk0_fmupd_with_0[of "x" "m"]  by (simp add: zero_fun_def zero_option_def)
        also have "... = clearjunk0 m"
          using fmupd(2)  by (simp add: clearjunk0_def fmap_ext)
        finally have "clearjunk0 (fmupd x y m) = clearjunk0 m"
          by auto
        hence " hd (sorted_list_of_fset (fmdom (clearjunk0 (fmupd x y m)))) =
                hd (sorted_list_of_fset (fmdom (clearjunk0 m)))"
          by auto
        also have "... = fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          using dom_only[OF `clearjunk0 m \<noteq> fmempty`] by auto
        finally have "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) =
                       fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          using fi_rexpand by auto
        also have "... = cur_least"
          using ind unfolding cur_least_def by auto
        finally have "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) =
                      cur_least" by auto
        with lexpand_old have ?thesis by auto }

      moreover
      { assume "y \<noteq> Map.empty"
        have push_clearjunk0_old: "clearjunk0 (fmupd x y m) = fmupd x y (clearjunk0 m)"
          by (metis \<open>y \<noteq> Map.empty\<close> clearjunk0_fmupd_neq_0 zero_map)
        hence fmdom_clearjunk: "fmdom (clearjunk0 (fmupd x y m)) = fmdom (fmupd x y (clearjunk0 m))"
          by auto
        have "sorted_list_of_fset (fmdom (fmupd x y (clearjunk0 m))) =
              insort x (sorted_list_of_fset (fmdom (fmdrop x (clearjunk0  m)))) "
          using sorted_list_fmdom_fmupd by auto
        moreover have "fmdrop x (clearjunk0 m) = clearjunk0 m"
          by (simp add: fmupd clearjunk0_def fmap_ext)
        ultimately have ****: "sorted_list_of_fset (fmdom (fmupd x y (clearjunk0 m))) =
                      insort x (sorted_list_of_fset (fmdom (clearjunk0  m)))"
          by auto
        hence "sorted_list_of_fset (fmdom (clearjunk0 (fmupd x y m))) =
               insort x (sorted_list_of_fset (fmdom (clearjunk0 m)))"
          using push_clearjunk0_old by auto
        have "hd (insort x (sorted_list_of_fset (fmdom (clearjunk0 m)))) =
                        hd (sorted_list_of_fset (fmdom (clearjunk0 m)))"
        proof (rule hd_after_insert_larger_key)
          show "sorted_list_of_fset (fmdom (clearjunk0 m)) \<noteq> []"
            by (metis \<open>clearjunk0 m \<noteq> fmempty\<close> fmrestrict_fset_dom fmrestrict_fset_null fset_of_list_simps(1)
                      sorted_list_of_fset_simps(2))
        next
          show " hd (sorted_list_of_fset (fmdom (clearjunk0 m))) < x "
            using \<open>clearjunk0 m \<noteq> fmempty\<close> \<open>cur_least < x\<close> cur_least_def dom_only ind by force
        qed
        also have "... = fst (hd (sorted_list_of_fmap (clearjunk0 m)))"
          using dom_only[OF `clearjunk0 m \<noteq> fmempty`] by auto
        also have "... = cur_least"
          using ind unfolding cur_least_def by auto
        finally have "hd (insort x (sorted_list_of_fset (fmdom (clearjunk0 m)))) =
                         cur_least" by auto
        hence "fst (hd (sorted_list_of_fmap (clearjunk0 (fmupd x y m)))) =
                cur_least"
          using  **** fi_rexpand push_clearjunk0_old by auto
        with lexpand_old have ?thesis by auto }
      ultimately show ?thesis by auto
    qed }
  ultimately show ?case by auto
qed

lemma [code]:
  "next_time t (Pm_fmap xs) =
      (if clearjunk0 xs = fmempty then t + 1 else (fst o hd) (sorted_list_of_fmap (clearjunk0 xs)))"
proof transfer'
  fix t :: nat
  fix xs :: "(nat, 'a \<Rightarrow> val option) fmap"
  have "Femto_VHDL_raw.next_time t (lookup0 xs) =
                                (if lookup0 xs = (\<lambda>k. 0) then t + 1 else LEAST n. dom (lookup0 xs n) \<noteq> {})"
    unfolding Femto_VHDL_raw.next_time_def zero_fun_def by auto
  also have "... = (if clearjunk0 xs = fmempty then t + 1 else (fst o hd) (sorted_list_of_fmap (clearjunk0 xs)))"
    unfolding lookup0_zero_fun by (auto simp add: least_fst_hd_sorted)
  finally show "Femto_VHDL_raw.next_time t (lookup0 xs) =
      (if clearjunk0 xs = fmempty then t + 1 else (fst \<circ> hd) (sorted_list_of_fmap (clearjunk0 xs)))"
    by auto
qed

value [code] "next_time 0 (empty_trans :: sig transaction)"
value [code] "next_state 0 (empty_trans :: sig transaction) (\<lambda>x. Bv False)  B"
value [code] "fmadd (fmap_of_list [(1::nat, True)]) (fmap_of_list [(1::nat, False)])"

definition fm_const_interval_open_right :: "'a :: zero \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, 'a) fmap" where
  "fm_const_interval_open_right v lo hi = fmap_of_list (zip [lo ..< hi] (replicate (hi - lo) v))"

lemma fmlookup_const_interval_if:
  "x \<in> {lo ..< hi} \<Longrightarrow> fmlookup (fm_const_interval_open_right v lo hi) x = Some v"
  "x \<notin> {lo ..< hi} \<Longrightarrow> fmlookup (fm_const_interval_open_right v lo hi) x = None"
  unfolding fm_const_interval_open_right_def fmlookup_of_list
  by (metis distinct_upt in_set_impl_in_set_zip1 in_set_replicate length_replicate length_upt
            map_fst_zip map_of_eq_Some_iff set_upt set_zip_rightD) (auto)

value [code] "add_to_beh ((\<lambda>x. Bv False)  :: sig state)"

code_thms add_to_beh

code_thms next_event

value [code] "next_event 0 (empty_trans :: sig transaction) (\<lambda>x. Bv False) "

code_pred (modes : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) simulate_fin_ind .

thm simulate_fin_ind.equation

definition "functional_simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> =
            Predicate.the (simulate_fin_ind_i_i_i_i_i_i_i_i_o maxtime t \<sigma> \<gamma> \<theta> def cs \<tau>)"

theorem functional_simulate_fin_complete:
  assumes "simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> beh"
  shows "functional_simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> = beh"
  using assms unfolding functional_simulate_fin_def simulate_fin_ind_i_i_i_i_i_i_i_i_o_def
  Predicate.the_def pred.sel
proof -
  have sim: "simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> beh"
    using simulate_fin_eq_simulate_fin_ind assms by metis
  hence "\<And>x. simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> x \<Longrightarrow> x = beh"
    unfolding sym[OF simulate_fin_eq_simulate_fin_ind]
    by (transfer', metis b_simulate_fin_deterministic)
  thus "The (simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau>) = beh"
    using assms by blast
qed

lemma functional_simulate_fin_sound:
  assumes "simulate_ss maxtime def cs (lookup \<tau>, t, \<sigma>, \<gamma>, lookup \<theta>, def) (lookup \<tau>', t', \<sigma>', \<gamma>', lookup \<theta>', def')"
  assumes "\<forall>n. (min maxtime t) < n \<longrightarrow> lookup \<theta> n = 0"
  assumes "\<forall>n. n < t \<longrightarrow> lookup \<tau> n = 0"
  assumes "functional_simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> = beh"
  assumes "maxtime = t'"
  shows "simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> beh"
proof -
  have *: "The (simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau>) = beh"
    using assms unfolding functional_simulate_fin_def simulate_fin_ind_i_i_i_i_i_i_i_i_o_def
    Predicate.the_def pred.sel  simulate_fin_eq_simulate_fin_ind
    by auto
  obtain \<tau>' \<sigma>' \<gamma>' \<theta>' def' where ss: "simulate_ss maxtime def cs (lookup \<tau>, t, \<sigma>, \<gamma>, lookup \<theta>, def) (\<tau>', t', \<sigma>', \<gamma>', \<theta>', def')"
    using assms(1) by auto
  have **: "b_simulate_fin maxtime t \<sigma> \<gamma> (lookup \<theta>) def cs (lookup \<tau>)  (t', \<sigma>', \<gamma>', \<theta>', \<tau>')"
    using small_step_implies_big_step[OF ss assms(2) assms(3)] \<open>maxtime = t'\<close> by auto 
  have fin: "finite {x. \<theta>' x \<noteq> 0}"
    using b_simulate_fin_almost_all_zero[OF **] by auto
  have fin2: "finite {x. \<tau>' x \<noteq> 0}"
    using b_simulate_fin_almost_all_zero2[OF **]  by simp
  have ***: "simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> (t', \<sigma>', \<gamma>', Abs_poly_mapping \<theta>', Abs_poly_mapping \<tau>')"
    using ** lookup_Abs_poly_mapping[OF fin] lookup_Abs_poly_mapping[OF fin2]
    unfolding simulate_fin.rep_eq  by simp
  hence "\<And>beh. simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> beh \<Longrightarrow> beh = (t', \<sigma>', \<gamma>', Abs_poly_mapping \<theta>', Abs_poly_mapping \<tau>')"
    using simulate_fin_deterministic by blast
  with * show "simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> beh"
    using theI[where P="simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau>"] ***
    unfolding sym[OF simulate_fin_eq_simulate_fin_ind] by metis
qed

lemma functional_simulate_eq_simulate_fin_ind:
  assumes "simulate_ss maxtime def cs (lookup \<tau>, t, \<sigma>, \<gamma>, lookup \<theta>, def) (lookup \<tau>', t', \<sigma>', \<gamma>', lookup \<theta>', def')"
  assumes "\<forall>n. (min maxtime t) < n \<longrightarrow> lookup \<theta> n = 0"
  assumes "\<forall>n. n < t \<longrightarrow> lookup \<tau> n = 0"
  assumes "maxtime = t'"
  shows "simulate_fin_ind maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> beh \<longleftrightarrow> (functional_simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> = beh)"
  by (metis assms(1) assms(2) assms(3) assms(4) functional_simulate_fin_complete functional_simulate_fin_sound)

lemma functional_simulate_eq_b_simulate_fin:
  assumes "simulate_ss maxtime def cs (lookup \<tau>, t, \<sigma>, \<gamma>, lookup \<theta>, def) (lookup \<tau>', t', \<sigma>', \<gamma>', lookup \<theta>', def')"
  assumes "\<forall>n. (min maxtime t) < n \<longrightarrow> lookup \<theta> n = 0"
  assumes "\<forall>n. n < t \<longrightarrow> lookup \<tau> n = 0"
  assumes "maxtime = t'"
  shows "simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> beh \<longleftrightarrow> (functional_simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> = beh)"
  using functional_simulate_eq_simulate_fin_ind[OF assms] simulate_fin_eq_simulate_fin_ind
  by metis

code_pred (modes : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) simulate_ind .

definition "functional_simulate maxtime def cs \<tau> =
            Predicate.the (simulate_ind_i_i_i_i_o maxtime def cs \<tau>)"

theorem functional_simulate_complete:
  assumes "simulate_ind maxtime def cs \<tau> beh"
  shows "functional_simulate maxtime def cs \<tau> = beh"
  using assms unfolding functional_simulate_def simulate_ind_i_i_i_i_o_def
  Predicate.the_def pred.sel
proof -
  have "simulate maxtime def cs \<tau> beh"
    using simulate_eq_simulate_ind assms by blast
  hence "(\<And>x. simulate_ind maxtime def cs \<tau> x \<Longrightarrow> x = beh)"
    unfolding sym[OF simulate_eq_simulate_ind]
    by (transfer')(metis b_sim_init_deterministic)
  thus  "(THE x. simulate_ind maxtime def cs \<tau> x) = beh"
    using assms by blast
qed

theorem functional_simulate_sound:
  assumes "Femto_VHDL_raw.init' 0 def {} 0 def cs (lookup ctrans) \<tau>"
  assumes "update_config_raw (0, def, {}, 0, def) \<tau> = (t, \<sigma>, \<gamma>, \<theta>, def)"
  assumes "simulate_ss maxtime def cs (\<tau>(t:=0), t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>', t', \<sigma>', \<gamma>', \<theta>', def')"
  assumes "functional_simulate maxtime def cs ctrans = beh"
  assumes "maxtime = t'"
  assumes "0 < maxtime"
  shows "simulate_ind maxtime def cs ctrans beh"
proof -
  have the_beh: "The (simulate_ind maxtime def cs ctrans) = beh"
    using assms unfolding functional_simulate_def simulate_ind_i_i_i_i_o_def Predicate.the_def pred.sel
    by auto
  have "t = Femto_VHDL_raw.next_time 0 \<tau>"
    using assms(2) by (auto simp add: Let_def)
  hence "\<forall>n. n < t \<longrightarrow>  \<tau> n = 0"
    using next_time_at_least2 by auto
  hence look: "\<forall>n<t. \<tau> n = 0 "
    by auto
  hence look': "\<forall>n<t. (\<tau>(t:=0)) n = 0"
    by (simp add: lookup_update)
  have empty: "\<And>s.  signal_of (def s) 0 s 0 = def s"
    by (meson signal_of_empty)
  have "\<theta> = Femto_VHDL_raw.add_to_beh2 def 0 0 def"
    using assms(2) unfolding update_config_raw.simps by auto
  also have "... = 0"
    using empty
    unfolding Femto_VHDL_raw.add_to_beh2_def Let_def comp_def fun_upd_def zero_fun_def zero_option_def
    by auto
  finally have *: "\<forall>n>(min maxtime t). 0 n = 0"
    using `0 < maxtime` 
    by (simp add: zero_fun_def) 
  hence bsf : "b_simulate_fin maxtime t \<sigma> \<gamma> 0 def cs (\<tau>(t:=0)) (t', \<sigma>', \<gamma>', \<theta>', \<tau>')"
    using small_step_implies_big_step[OF assms(3)] look' \<open>maxtime = t'\<close>
    by (simp add: "*" \<open>Femto_VHDL_raw.add_to_beh2 def 0 0 def = 0\<close> \<open>\<theta> = Femto_VHDL_raw.add_to_beh2 def 0 0 def\<close>)
  hence bs: "b_simulate maxtime def cs (lookup ctrans) (t', \<sigma>', \<gamma>', \<theta>', \<tau>')"
    using assms(1) assms(2) b_simulate.simps by force
  have "simulate maxtime def cs ctrans (t', \<sigma>', \<gamma>', Abs_poly_mapping \<theta>', Abs_poly_mapping \<tau>')"
  proof -
    have "\<theta> = 0"
      by (simp add: \<open>Femto_VHDL_raw.add_to_beh2 def 0 0 def = 0\<close> \<open>\<theta> = Femto_VHDL_raw.add_to_beh2 def 0 0 def\<close>)
    hence "finite {x. \<theta> x \<noteq> 0}"
      unfolding sym[OF eventually_cofinite] Femto_VHDL_raw.add_to_beh_def
      by (simp add: MOST_nat zero_fun_def)
    hence "finite {x. \<theta>' x \<noteq> 0}"
      using b_simulate_fin_almost_all_zero bsf  using \<open>\<theta> = 0\<close> by fastforce
    moreover have "finite {x. \<tau>' x \<noteq> 0}"
    proof -
      have "finite {x. lookup (ctrans) x \<noteq> 0}"
        by simp
      hence "finite {x. \<tau> x \<noteq> 0}"
        using init'_raw_almost_all_zero[OF _ \<open>finite {x. \<theta> x \<noteq> 0}\<close>] assms(1)
        by (metis Femto_VHDL_raw.keys_def finite.emptyI init'_raw_almost_all_zero trans_empty_keys)
      hence "finite {x. (\<tau>(t := 0)) x \<noteq> 0}"
        using \<open>t = Femto_VHDL_raw.next_time 0 \<tau>\<close> rem_next_time_almost_all_zero by blast
      thus ?thesis
        using b_simulate_fin_almost_all_zero2[OF _ _ \<open>finite {x. \<theta> x \<noteq> 0}\<close>] bsf 
        using \<open>\<theta> = 0\<close> by auto
    qed
    moreover have "(map_prod id (map_prod id (map_prod lookup lookup)) (t', \<sigma>', Abs_poly_mapping \<theta>', Abs_poly_mapping \<tau>')) =
                   (t', \<sigma>', lookup (Abs_poly_mapping \<theta>'), lookup (Abs_poly_mapping \<tau>'))"
      by auto
    ultimately show ?thesis
      unfolding simulate.rep_eq using bs lookup_Abs_poly_mapping by simp
  qed
  hence "simulate_ind maxtime def cs ctrans (t', \<sigma>', \<gamma>', Abs_poly_mapping \<theta>', Abs_poly_mapping \<tau>')"
    using simulate_eq_simulate_ind by blast
  thus "simulate_ind maxtime def cs ctrans beh"
    unfolding the_beh[THEN sym]  using assms(4) functional_simulate_complete the_beh
    by fastforce
qed

theorem
  assumes "Femto_VHDL_raw.init' 0 def {} 0 def cs (lookup ctrans) \<tau>"
  assumes "update_config_raw (0, def, {}, 0, def) \<tau> = (t, \<sigma>, \<gamma>, \<theta>, def)"
  assumes "simulate_ss maxtime def cs (\<tau>(t:=0), t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>', t', \<sigma>', \<gamma>', \<theta>', def')"
  assumes "maxtime = t'" and "0 < maxtime"
  shows "functional_simulate maxtime def cs ctrans = beh \<longleftrightarrow> simulate_ind maxtime def cs ctrans beh"
  using assms functional_simulate_sound functional_simulate_complete by metis

subsection \<open>Code abbreviation for evaluating raw functions\<close>

lemma [code_abbrev]:
  "lookup (to_transaction2' xs sig) = to_trans_raw_sig (lookup xs) sig"
  unfolding to_transaction2'_def
  by (transfer')(rule ext, auto simp add: when_def zero_fun_def zero_option_def to_trans_raw_sig_def)

lemma evaluate_to_trans_raw_sig:
  "to_trans_raw_sig (lookup test_beh) A 1 = Some (Bv True)"
  by eval

lemma [code_abbrev]:
  "beval now \<sigma> \<gamma> hist exp = beval_raw now \<sigma> \<gamma> (lookup hist) exp"
  by transfer' auto

lemma [code_abbrev]:
  "lookup (purge \<tau> t dly sig def val) = purge_raw (lookup \<tau>) t dly sig def val"
  by transfer' auto

(* lemma evaluate_beval_raw:
  "beval_raw 0 (\<lambda>x. Bv False) {} (lookup (Pm_fmap (fmap_of_list []))) (\<lambda>x. Bv False) (Bsig A) (Bv False)"
  by eval *)

lemma evaluate_purge_raw:
  "(purge_raw (lookup (Pm_fmap (fmap_of_list []))) 1 1 C (Bv True) (Bv False)) 1 C = None"
  by eval

lemma evaluate_post_raw:
  "post_raw C (Bv False) (lookup test_beh) 10 10 C = Some (Bv False)"
  by eval

lemma evaluate_preempt_raw:
  "preempt_raw A (lookup test_beh) 20 1 A = Some (Bv True)"
  by eval

(* lemma evaluate_b_seq_exec:
  "b_seq_exec 0 def_state {} (lookup (Pm_fmap (fmap_of_list []))) (Bnull :: sig seq_stmt)
              (lookup (Pm_fmap (fmap_of_list []))) 10 A = None"
  by eval

lemma evaluate_b_conc_exec:
  "b_conc_exec 1 def_state {A, B} (lookup test_beh) (process {A} : seq1) (lookup (Pm_fmap (fmap_of_list []))) 2 C = Some True"
  by eval
 *)

lemma evaluate_quiet_raw:
  "Femto_VHDL_raw.quiet ((lookup (Pm_fmap (fmap_of_list []))) :: sig trans_raw) {}"
  by eval

lemma evaluate_next_time_raw:
  "Femto_VHDL_raw.next_time 0 ((lookup (Pm_fmap (fmap_of_list []))) :: sig trans_raw) = 1"
  by eval

lemma evaluate_next_state_raw:
  "Femto_VHDL_raw.next_state 0 ((lookup (Pm_fmap (fmap_of_list []))) :: sig trans_raw) (\<lambda>x. Bv False) B = Bv False"
  by eval

lemma evaluate_next_event:
  "Femto_VHDL_raw.next_event 0 ((lookup (Pm_fmap (fmap_of_list []))) :: sig trans_raw) (\<lambda>x. Bv False) = {}"
  by eval

hide_const exp1 exp2 seq1 seq2

end