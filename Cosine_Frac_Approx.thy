(*
 * Copyright 2019, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Cosine_Frac_Approx                           
  imports "HOL-Decision_Procs.Approximation"
begin

lemma fact8:
  "fact 8 = (40320 :: int)"
  by eval

lemma fact6: 
  "fact 6 = (720 :: int)" 
  by eval

lemma fact4:
  "fact 4 = (24 :: int)"
  by eval

definition floatarith8 :: "floatarith" where
  "floatarith8 = floatarith.Inverse (floatarith.Num (Float 40320 0))"

definition floatarith6 :: "floatarith" where
  "floatarith6 = floatarith.Inverse (floatarith.Num (Float 720 0))"

definition floatarith4 :: "floatarith" where
  "floatarith4 = floatarith.Inverse (floatarith.Num (Float 24 0))"

value [code] "approx 18 floatarith8 []"

lemma
  "1 / ((fact 8) :: int) \<in> {Float 53261 (- 31) .. Float 426089 (- 34)}"
  unfolding fact8 by (approximation 18)

definition "approx_eighth = 53261" 

value [code] "approx 23 floatarith6 []"

lemma
  "1 / ((fact 6) :: int) \<in> {Float 372827 (- 28) .. Float 11930465 (- 33)}"
  unfolding fact6 by (approximation 23)

lemma
  "1 / ((fact 6) :: int) \<in> {Float 2982616 (- 31) .. Float 11651 (- 23)}"
  unfolding fact6 by (approximation 23)

definition "approx_sixth = 2982616" 

lemma "Float 372827 (-28) = Float approx_sixth (-31)"
  by eval

value [code ] "approx 24 floatarith4 []"

lemma
  "1 / ((fact 4) :: int) \<in> {Float 22369621 (- 29) ..  Float 11184811 (- 28)}"
  unfolding fact4 by (approximation 24)

lemma
  "1 / ((fact 4) :: int) \<in> {Float 89478484 (- 31) .. Float 10923 (- 18)}"
  unfolding fact4 by (approximation 24)

definition "approx_fourth = 89478484"

lemma "Float 22369621 (-29) = Float approx_fourth (-31)" 
  by eval  

lemma
  "1 / ((fact 2) :: int) = Float 1 (-1)"
  by eval

lemma
  "1 / ((fact 2) :: int) = Float 1073741824 (-31)"
  by eval

definition "approx_half = 1073741824"

definition "approx_one = 2147483647"

end