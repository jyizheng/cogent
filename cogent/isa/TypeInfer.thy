theory TypeInfer
  imports Cogent
  (* "../../autocorres/lib/Apply_Trace_Cmd" *)
begin

lemma canonical_trans_less_add1:
  fixes x y z :: "'a :: canonically_ordered_monoid_add"
  shows "z < x \<Longrightarrow> z < x + y"
  by (meson le_iff_add less_le_trans)

lemma canonical_trans_less_add2:
  fixes x y z :: "'a :: canonically_ordered_monoid_add"
  shows "z < y \<Longrightarrow> z < x + y"
  by (metis add.commute canonical_trans_less_add1)

lemma canonical_trans_le_add1:
  fixes x y z :: "'a :: canonically_ordered_monoid_add"
  shows "x + y \<le> z \<Longrightarrow> x \<le> z"
  by (meson le_iff_add order_trans)

lemma canonical_trans_le_add2:
  fixes x y z :: "'a :: canonically_ordered_monoid_add"
  shows "x + y \<le> z \<Longrightarrow> y \<le> z"
  by (metis add.commute canonical_trans_le_add1)

lemma canonical_smaller_add_impossible1:
  fixes x y z :: "'a :: canonically_ordered_monoid_add"
  shows "\<lbrakk> \<not> z < x + y; z < x \<rbrakk> \<Longrightarrow> False"
  using canonical_trans_less_add1 by blast

lemma canonical_smaller_add_impossible2:
  fixes x y z :: "'a :: canonically_ordered_monoid_add"
  shows "\<lbrakk> \<not> z < x + y; z < y \<rbrakk> \<Longrightarrow> False"
  using canonical_trans_less_add2 by blast

lemma neq_le_eq_less:
  fixes a b :: "'a :: order"
  shows "a \<noteq> b \<Longrightarrow> a \<le> b \<longleftrightarrow> a < b"
  by (simp add: le_less)

(*
  What structures satisfy?
 1. \<lbrakk>c1 + c2 \<le> 1 \<rbrakk> \<Longrightarrow> c1 \<le> 1
 2. \<lbrakk>c1 + c2 \<le> 1 \<rbrakk> \<Longrightarrow> c2 \<le> 1
 3. \<lbrakk> 1 + 1 \<le> 1; c1 = 1; c2 = 1\<rbrakk> \<Longrightarrow> False
 4. \<lbrakk> c1 \<le> 1; c2 \<le> 1; c1 \<noteq> 1\<rbrakk> \<Longrightarrow> c1 + c2 \<le> 1
 5. \<lbrakk> c1 \<le> 1; c2 \<le> 1; c2 \<noteq> 1\<rbrakk> \<Longrightarrow> c1 + c2 \<le> 1

  \<lbrakk>\<not> 1 < sup c1 c2; 1 < c1\<rbrakk> \<Longrightarrow> False
  \<lbrakk>\<not> 1 < sup c1 c2; 1 < c2\<rbrakk> \<Longrightarrow> False
  \<lbrakk>1 < sup c1 c2 \<Longrightarrow> \<not> 1 < c1; \<not> 1 < c2\<rbrakk> \<Longrightarrow> False
*)

(* Cogent lemmas (TODO move) *)

lemma weakening_comp_trans:
  "weakening_comp K a b \<Longrightarrow> weakening_comp K b c \<Longrightarrow> weakening_comp K a c"
  by (force simp add: weakening_comp.simps)

lemma weakening_trans:
  "K \<turnstile> xs \<leadsto>w ys \<Longrightarrow> K \<turnstile> ys \<leadsto>w zs \<Longrightarrow> K \<turnstile> xs \<leadsto>w zs"
  by (fastforce simp add: weakening_conv_all_nth weakening_comp.simps)

lemma consume_weakening:
  "\<lbrakk>K \<turnstile> xs \<leadsto>w ys; K \<turnstile> ys consumed\<rbrakk> \<Longrightarrow> K \<turnstile> xs consumed"
  by (metis is_consumed_def weakening_length weakening_trans)



section {* Lemmas about split and weakening *}

lemma split_weaken_comp:
  assumes "K \<turnstile> a \<leadsto> a1 \<parallel> a2"
    and "weakening_comp K a wa"
  shows "\<exists>wa1 wa2. (K \<turnstile> wa \<leadsto> wa1 \<parallel> wa2) \<and> (weakening_comp K a1 wa1) \<and> (weakening_comp K a2 wa2)"
  using assms
  apply (cases a1)
   apply (fastforce simp add: split_comp.simps weakening_comp.simps)
  apply (cases a2)
   apply (fastforce simp add: split_comp.simps weakening_comp.simps)
  apply (clarsimp simp add: split_comp.simps weakening_comp.simps, blast)
  done

lemma split_weaken:
  assumes "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    and "K \<turnstile> \<Gamma> \<leadsto>w w\<Gamma>"
  shows "\<exists>w\<Gamma>1 w\<Gamma>2. (K \<turnstile> w\<Gamma> \<leadsto> w\<Gamma>1 | w\<Gamma>2) \<and> (K \<turnstile> \<Gamma>1 \<leadsto>w w\<Gamma>1) \<and> (K \<turnstile> \<Gamma>2 \<leadsto>w w\<Gamma>2)"
  using assms
proof (induct \<Gamma> arbitrary: w\<Gamma> \<Gamma>1 \<Gamma>2)
  case Nil
  then show ?case
    using split_length weakening_length by fastforce
next
  case (Cons a \<Gamma>')
  then obtain a1 \<Gamma>1' a2 \<Gamma>2' wa w\<Gamma>'
    where ctx_simps:
      "\<Gamma>1 = a1 # \<Gamma>1'"
      "\<Gamma>2 = a2 # \<Gamma>2'"
      "w\<Gamma> = wa # w\<Gamma>'"
    using weakening_def split_length
    by (metis list.rel_distinct(2) length_0_conv neq_Nil_conv)

  have prems_elims:
    "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1' | \<Gamma>2'"
    "K \<turnstile> a \<leadsto> a1 \<parallel> a2"
    "K \<turnstile> \<Gamma>' \<leadsto>w w\<Gamma>'"
    "weakening_comp K a wa"
    using Cons.prems
    by (fastforce simp add: split_def elim: list_all3.cases simp add: weakening_def ctx_simps)+
  then obtain wa1 wa2
    where weak_of_split_comps:
      "K \<turnstile> wa \<leadsto> wa1 \<parallel> wa2"
      "weakening_comp K a1 wa1"
      "weakening_comp K a2 wa2"
    using split_weaken_comp by blast

  obtain w\<Gamma>1' w\<Gamma>2'
    where ih_on_subctxs:
      "K \<turnstile> w\<Gamma>' \<leadsto> w\<Gamma>1' | w\<Gamma>2'"
      "K \<turnstile> \<Gamma>1' \<leadsto>w w\<Gamma>1'"
      "K \<turnstile> \<Gamma>2' \<leadsto>w w\<Gamma>2'"
    using prems_elims Cons.hyps weakening_def split_cons prems_elims
    by blast

  have "K \<turnstile> wa # w\<Gamma>' \<leadsto> wa1 # w\<Gamma>1' | wa2 # w\<Gamma>2'"
    and "K \<turnstile> a1 # \<Gamma>1' \<leadsto>w wa1 # w\<Gamma>1'"
    and "K \<turnstile> a2 # \<Gamma>2' \<leadsto>w wa2 # w\<Gamma>2'"
    using ih_on_subctxs weak_of_split_comps split_cons weakening_def list.rel_intros(2)
    by metis+
  then show ?case
    using ctx_simps by blast
qed

lemma wksplit_to_splitwks_comp:
  assumes
    "split_comp K g g1 g2"
    "weakening_comp K d g"
  shows
    "\<exists>d1 d2. split_comp K d d1 d2 \<and> weakening_comp K d1 g1 \<and> weakening_comp K d2 g2"
  using assms
  by (fastforce
      simp add: split_comp.simps weakening_comp.simps type_wellformed_pretty_def
      intro: kinding_imp_wellformed[simplified type_wellformed_pretty_def])

lemma wksplit_to_splitwks:
  assumes
    "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    "K \<turnstile> \<Delta> \<leadsto>w \<Gamma>"
  shows
    "\<exists>\<Delta>1 \<Delta>2. K \<turnstile> \<Delta> \<leadsto> \<Delta>1 | \<Delta>2 \<and> K \<turnstile> \<Delta>1 \<leadsto>w \<Gamma>1 \<and> K \<turnstile> \<Delta>2 \<leadsto>w \<Gamma>2"
  using assms
  apply (clarsimp simp add: weakening_conv_all_nth split_conv_all_nth)
  using wksplit_to_splitwks_comp
  sorry


lemma weaken_and_split_comp:
  assumes "K \<turnstile> a \<leadsto> a1 \<parallel> a2"
    and "weakening_comp K a1 wa1"
    and "weakening_comp K a2 wa2"
  shows "\<exists>wa. weakening_comp K a wa \<and> K \<turnstile> wa \<leadsto> wa1 \<parallel> wa2"
  using assms
  by (fastforce
      dest: kinding_to_wellformedD
      simp add: split_comp.simps weakening_comp.simps type_wellformed_pretty_def)

lemma weaken_and_split:
  assumes "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    and "K \<turnstile> \<Gamma>1 \<leadsto>w w\<Gamma>1"
    and "K \<turnstile> \<Gamma>2 \<leadsto>w w\<Gamma>2"
  shows "\<exists>w\<Gamma>. (K \<turnstile> \<Gamma> \<leadsto>w w\<Gamma>) \<and> (K \<turnstile> w\<Gamma> \<leadsto> w\<Gamma>1 | w\<Gamma>2)"
  using assms
proof (induct arbitrary: w\<Gamma>1 w\<Gamma>2 rule: split_induct)
  case (split_cons a \<Gamma> a1 \<Gamma>1 a2 \<Gamma>2)

  obtain wa1 w\<Gamma>1' wa2 w\<Gamma>2'
    where ctx_simps:
      "w\<Gamma>1 = wa1 # w\<Gamma>1'"
      "w\<Gamma>2 = wa2 # w\<Gamma>2'"
    by (metis split_cons.prems list_all2_Cons1 weakening_def)
  have subweakenings:
    "weakening_comp K a1 wa1"
    "K \<turnstile> \<Gamma>1 \<leadsto>w w\<Gamma>1'"
    "weakening_comp K a2 wa2"
    "K \<turnstile> \<Gamma>2 \<leadsto>w w\<Gamma>2'"
    by (metis ctx_simps list.rel_inject(2) split_cons.prems weakening_def)+
  then obtain w\<Gamma>' wa
    where IHsplitsweakens:
      "K \<turnstile> wa \<leadsto> wa1 \<parallel> wa2"
      "K \<turnstile> w\<Gamma>' \<leadsto> w\<Gamma>1'| w\<Gamma>2'"
      "weakening_comp K a wa"
      "K \<turnstile> \<Gamma> \<leadsto>w w\<Gamma>'"
    using split_cons.hyps weaken_and_split_comp
    by blast
  then have
    "K \<turnstile> wa # w\<Gamma>' \<leadsto> wa1 # w\<Gamma>1' | wa2 # w\<Gamma>2'"
    "K \<turnstile> a # \<Gamma> \<leadsto>w wa # w\<Gamma>'"
    unfolding weakening_def
    using IHsplitsweakens
    by (simp add: split_def weakening_def)+
  then show ?case
    using ctx_simps by blast
qed (force simp add: weakening_def split_def)

(*
lemma weaken_and_split_bang_comp:
  assumes "K , dobang \<turnstile> a \<leadsto>b a1 \<parallel> a2"
    and "weakening_comp K a1 wa1"
    and "weakening_comp K a2 wa2"
  shows "\<exists>wa dobang. (weakening_comp K a wa) \<and> (K , dobang \<turnstile> wa m\<leadsto>b wa1 \<parallel> wa2)"
  using assms
proof (cases rule: split_bang_comp.cases)
  case none
  then show ?thesis
    using assms
    apply -
    apply (erule split_comp.cases)
       apply (fastforce simp add: split_comp.simps weakening_comp.simps split_min_comp.simps)
      apply clarsimp
      apply (cases wa1)
       apply (auto simp add: weakening_comp.simps split_min_comp.simps split_comp.simps)[1]
      apply (clarsimp simp add: weakening_comp.simps split_min_comp.simps split_comp.simps, meson)
     apply (cases wa2)
      apply (auto simp add: weakening_comp.simps split_min_comp.simps split_comp.simps)[2]
    apply (cases wa1; cases wa2)
       apply (auto simp add: weakening_comp.simps split_min_comp.simps split_comp.simps)[4]
    done
next
  case (dobang x)
  then show ?thesis
    using assms
    by (cases wa1; cases wa2;
            (clarsimp simp add: weakening_comp.simps split_min_comp.simps split_comp.simps, auto))
qed


lemma weaken_and_split_bang:
  assumes "K , is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
    and "K \<turnstile> \<Gamma>1 \<leadsto>w w\<Gamma>1"
    and "K \<turnstile> \<Gamma>2 \<leadsto>w w\<Gamma>2"
  shows "\<exists>w\<Gamma> is. (K \<turnstile> \<Gamma> \<leadsto>w w\<Gamma>) \<and> (K , is \<turnstile> w\<Gamma> m\<leadsto>b w\<Gamma>1 | w\<Gamma>2)"
  using assms
proof (induct arbitrary: w\<Gamma>1 w\<Gamma>2 "is" rule: split_bang.inducts)
  case (split_bang_cons is' "is" K \<Gamma>' \<Gamma>1' \<Gamma>2' a a1 a2)

  obtain w\<Gamma>1' w\<Gamma>2' wa1 wa2
    where ctx_simps:
      "w\<Gamma>1 = wa1 # w\<Gamma>1'"
      "w\<Gamma>2 = wa2 # w\<Gamma>2'"
    using split_bang_cons.prems
    by (fastforce simp add: list_all2_Cons1 weakening_def)
  then have subweakenings:
    "weakening_comp K a1 wa1"
    "weakening_comp K a2 wa2"
    "K \<turnstile> \<Gamma>1' \<leadsto>w w\<Gamma>1'"
    "K \<turnstile> \<Gamma>2' \<leadsto>w w\<Gamma>2'"
    using split_bang_cons.prems weakening_nth
    by (fastforce simp add: weakening_def)+

  obtain w\<Gamma>' isa
    where IHresults:
      "K \<turnstile> \<Gamma>' \<leadsto>w w\<Gamma>'"
      "K , isa \<turnstile> w\<Gamma>' m\<leadsto>b w\<Gamma>1' | w\<Gamma>2'"
    using split_bang_cons.hyps(3) subweakenings by blast

  obtain wa dobang
    where weaken_split_bang_step:
      "weakening_comp K a wa"
      "K , dobang \<turnstile> wa m\<leadsto>b wa1 \<parallel> wa2"
    using split_bang_cons.hyps subweakenings weaken_and_split_bang_comp
    by blast

  have
    "K \<turnstile> a # \<Gamma>' \<leadsto>w wa # w\<Gamma>'"
    using weaken_split_bang_step IHresults
    by (simp add: weakening_def)
  moreover have "K , (if dobang then insert 0 (Suc ` isa) else Suc ` isa) \<turnstile> wa # w\<Gamma>' m\<leadsto>b wa1 # w\<Gamma>1' | wa2 # w\<Gamma>2'"
    using IHresults weaken_split_bang_step
    by (fastforce intro: split_min.intros simp add: remove_def zero_notin_Suc_image set_pred_left_inverse_suc)
  ultimately show ?case
    using ctx_simps by fast
qed (simp add: split_min_empty weakening_def)
*)




lemma typing_weaken_context:
shows "\<Xi>, K, \<Gamma> \<turnstile>  e  : t  \<Longrightarrow> K \<turnstile> \<Gamma>' \<leadsto>w \<Gamma> \<Longrightarrow> \<Xi>, K, \<Gamma>' \<turnstile>  e  : t"
and   "\<Xi>, K, \<Gamma> \<turnstile>* es : ts \<Longrightarrow> K \<turnstile> \<Gamma>' \<leadsto>w \<Gamma> \<Longrightarrow> \<Xi>, K, \<Gamma>' \<turnstile>* es : ts"
proof (induct arbitrary: \<Gamma>' and \<Gamma>' rule: typing_typing_all.inducts)
  case typing_var then show ?case
    by (bestsimp
        intro!: typing_typing_all.intros
        simp add: weakening_conv_all_nth Cogent.empty_def
        dest: weakening_comp_trans)
next
  case typing_afun then show ?case
    by (fastforce intro!: typing_typing_all.intros dest: consume_weakening)
next
  case typing_fun then show ?case
    by (fastforce intro!: typing_typing_all.intros dest: consume_weakening)
next
  case (typing_app K \<Gamma> \<Gamma>1 \<Gamma>2)
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> \<Gamma>'2 \<leadsto>w \<Gamma>2"
    by (force dest: wksplit_to_splitwks)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_tuple K \<Gamma> \<Gamma>1 \<Gamma>2)
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> \<Gamma>'2 \<leadsto>w \<Gamma>2"
    by (force dest: wksplit_to_splitwks)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_split K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t u y t')
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> Some t # Some u # \<Gamma>'2 \<leadsto>w Some t # Some u # \<Gamma>2"
    by (force dest: wksplit_to_splitwks simp add: weakening_Cons weakening_comp.simps)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_let K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u)
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> Some t # \<Gamma>'2 \<leadsto>w Some t # \<Gamma>2"
    by (force dest: wksplit_to_splitwks simp add: weakening_Cons weakening_comp.simps)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_letb K "is" \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u k)
  then show ?case sorry
next
  case (typing_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts tag t a u b)
  then show ?case sorry
next
  case (typing_if K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x a t b)
  then show ?case sorry
next
  case (typing_take K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t k taken e' u)
  then show ?case sorry
next
  case (typing_put K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t taken k e')
  then show ?case sorry
next
  case (typing_all_empty \<Gamma> n \<Xi> K)
  then show ?case
    apply (safe intro!: typing_typing_all.intros)
    sorry
next
  case (typing_all_cons K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e t es ts)
  then show ?case sorry
qed (fastforce intro!: typing_typing_all.intros dest: consume_weakening)+

(* main theory *)


definition countPlus :: "('a :: plus) list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<oplus>" 75) where
  "xs \<oplus> ys \<equiv> map2 (+) xs ys"

lemma countPlus_simps[simp]:
  "countPlus [] [] = []"
  "countPlus (x # xs) (y # ys) = (x+y) # (xs \<oplus> ys)"
  "countPlus [] (y # ys) = []"
  "countPlus (x # xs) [] = []"
  by (simp add: countPlus_def)+

lemma countPlus_length[simp]:
  "length (C1 \<oplus> C2) = min (length C1) (length C2)"
  by (simp add: countPlus_def)

lemma countPlus_eq_Nil[simp]:
  "(C1 \<oplus> C2 = []) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countPlus_length length_greater_0_conv min_less_iff_conj)
lemma countPlus_eq_Nil2[simp]:
  "([] = C1 \<oplus> C2) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countPlus_length length_greater_0_conv min_less_iff_conj)

lemma countPlus_eq_Cons:
  "(C1 \<oplus> C2 = x # xs) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = y + z \<and> xs = ys \<oplus> zs)"
  by (case_tac C1; case_tac C2; force)
lemma countPlus_eq_Cons2:
  "(x # xs = C1 \<oplus> C2) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = y + z \<and> xs = ys \<oplus> zs)"
  by (case_tac C1; case_tac C2; force)


lemma countPlus_nth[simp]:
  "i < length C1 \<Longrightarrow> i < length C2 \<Longrightarrow> (C1 \<oplus> C2) ! i = C1 ! i + C2 ! i"
  by (simp add: countPlus_def)


definition countMax :: "('a :: sup) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "countMax xs ys \<equiv> map2 sup xs ys"

lemma countMax_simps[simp]:
  "countMax [] [] = []"
  "countMax (x # xs) (y # ys) = (sup x y) # (countMax xs ys)"
  "countMax [] (y # ys) = []"
  "countMax (x # xs) [] = []"
  by (simp add: countMax_def)+

lemma countMax_length[simp]:
  "length (countMax C1 C2) = min (length C1) (length C2)"
  by (simp add: countMax_def)

lemma countMax_eq_Nil[simp]:
  "(countMax C1 C2 = []) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countMax_length length_greater_0_conv min_less_iff_conj)
lemma countMax_eq_Nil2[simp]:
  "([] = countMax C1 C2) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countMax_length length_greater_0_conv min_less_iff_conj)

lemma countMax_eq_Cons:
  "(countMax C1 C2 = x # xs) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = sup y z \<and> xs = countMax ys zs)"
  by (case_tac C1; case_tac C2; force)
lemma countMax_eq_Cons2:
  "(x # xs = countMax C1 C2) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = sup y z \<and> xs = countMax ys zs)"
  by (case_tac C1; case_tac C2; force)

lemma countMax_nth[simp]:
  "i < length C1 \<Longrightarrow> i < length C2 \<Longrightarrow> countMax C1 C2 ! i = sup (C1 ! i) (C2 ! i)"
  by (induct C1 arbitrary: C2 i)
    (force simp add: less_Suc_eq_0_disj Suc_less_eq2 neq_Nil_conv length_Suc_conv)+


datatype linearity = LMany ("\<omega>") | LOne | LNone

instantiation linearity :: "{one, linorder, bounded_lattice, canonically_ordered_monoid_add}"
begin

definition "bot_linearity \<equiv> LNone"
fun sup_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> linearity" where
  "sup_linearity LNone b = b"
| "sup_linearity LOne LNone = LOne"
| "sup_linearity LOne b = b"
| "sup_linearity LMany b = LMany"
definition "top_linearity \<equiv> LMany"
fun inf_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> linearity" where
  "inf_linearity LMany b = b"
| "inf_linearity LOne LMany = LOne"
| "inf_linearity LOne b = b"
| "inf_linearity LNone b = LNone"

definition "zero_linearity \<equiv> LNone"

definition "one_linearity \<equiv> LOne"

fun less_eq_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> bool" where
  "less_eq_linearity LNone _ = True"
| "less_eq_linearity LOne LNone = False"
| "less_eq_linearity LOne _ = True"
| "less_eq_linearity LMany LMany = True"
| "less_eq_linearity LMany _ = False"

fun less_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> bool" where
  "less_linearity LNone LNone = False"
| "less_linearity LNone _ = True"
| "less_linearity LOne LOne = False"
| "less_linearity LOne LNone = False"
| "less_linearity LOne _ = True"
| "less_linearity LMany _ = False"

fun plus_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> linearity" where
  "plus_linearity LNone x = x"
| "plus_linearity LOne LNone = LOne"
| "plus_linearity LOne LOne = LMany"
| "plus_linearity LOne LMany = LMany"
| "plus_linearity LMany x = LMany"

lemma lin_add_sym: "a + b = b + (a :: linearity)"
  by (cases a; cases b; simp)

lemma lin_sup_sym: "sup a b = sup b (a :: linearity)"
  by (cases a; cases b; simp)


lemma linearity_1plus1[simp]: "1 + 1 = \<omega>"
  by (simp add: one_linearity_def)

lemma linearity_add_to_none_are_nones[simp]: "a + b = LNone \<longleftrightarrow> (a = LNone \<and> b = LNone)"
  using plus_linearity.elims by auto
lemmas linearity_add_to_none_are_nones2[simp] =
  trans[OF eq_commute linearity_add_to_none_are_nones]

lemma linearity_add_to_one_has_nonzero: "a + b = LOne \<Longrightarrow> (a \<noteq> LNone \<or> b \<noteq> LNone)"
  by auto

lemma linearity_sup_to_many_some_many[simp]: "sup a b = \<omega> \<longleftrightarrow> (a = \<omega> \<or> b = \<omega>)"
  using sup_linearity.elims
  by (cases a; cases b; simp)
lemmas linearity_sup_to_many_some_many2[simp] =
  trans[OF eq_commute linearity_sup_to_many_some_many]

instance
proof
  fix x y z :: linearity
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x; cases y; simp)
  show "x \<le> x"
    by (cases x; simp)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z; simp)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y; simp)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y; simp)
next
  fix a b c :: linearity
  show "a + b + c = a + (b + c)"
    by (cases a; cases b; cases c; simp)
  show "a + b = b + a"
    by (cases a; cases b; simp)
  show "0 + a = a"
    by (cases a; simp add: zero_linearity_def)
next
  fix a :: linearity
  show "bot \<le> a"
    by (simp add: bot_linearity_def)
  show "a \<le> top"
    by (cases a; simp add: top_linearity_def)
next
  fix x y z :: linearity
  show "inf x y \<le> x"
    by (cases x; cases y; simp)
  show "inf x y \<le> y"
    by (cases x; cases y; simp)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
    by (cases x; cases y; cases z; simp)
  show "x \<le> sup x y"
    by (cases x; cases y; simp)
  show "y \<le> sup x y"
    by (cases x; cases y; simp)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x"
    by (cases x; cases y; cases z; simp)
next
  fix a b :: linearity
  show "(a \<le> b) = (\<exists>c. b = a + c)"
    by (cases "(a,b)" rule: less_eq_linearity.cases
        ; simp, (metis plus_linearity.simps(2-3))?)
qed

end

lemma linearity_extra_simps[simp]:
  "(\<omega> = 1) = False"
  "(\<omega> = 0) = False"
  "(1 = \<omega>) = False"
  "(0 = \<omega>) = False"
  "(1 = (0::linearity)) = False"
  "(0 = (1::linearity)) = False"
  "(LOne = 0) = False"
  "(0 = LOne) = False"
  "(1 = LNone) = False"
  "(LNone = 1) = False"
  "(LNone \<noteq> 0) = False"
  "(0 \<noteq> LNone) = False"
  "(LOne \<noteq> 1) = False"
  "(1 \<noteq> LOne) = False"
  by (simp add: lin_add_sym zero_linearity_def one_linearity_def)+

lemma plus_linearity_simps[simp]:
  "x + LNone = x"
  "x + \<omega> = \<omega>"
  by (simp add: lin_add_sym zero_linearity_def one_linearity_def)+

lemma sup_linearity_simps[simp]:
  "sup 1 \<omega> = \<omega>"
  "sup x LNone = x"
  "sup x 0 = x"
  "sup 0 x = x"
  by (simp add: zero_linearity_def one_linearity_def bot_linearity_def[symmetric])+

lemma linearity_zero_case[simp]: "case_linearity p q r 0 = r"
  by (simp add: zero_linearity_def)

lemma linearity_one_case[simp]: "case_linearity p q r 1 = q"
  by (simp add: one_linearity_def)

lemmas linearity_order_simps[simp] =
  order_top_class.top_greatest[where a="a :: linearity" for a, simplified top_linearity_def]
  order_bot_class.bot_least[where a="a :: linearity" for a, simplified bot_linearity_def]
  order_bot_class.bot_least[where a="a :: linearity" for a, simplified bot_linearity_def zero_linearity_def[symmetric]]

lemma linearity_neq_none_iff: "x \<noteq> LNone \<longleftrightarrow> x = \<omega> \<or> x = LOne"
  by (cases x; simp)
lemmas linearity_neq_none_iff2 =
  linearity_neq_none_iff[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]

lemma linearity_neq_one_iff: "x \<noteq> LOne \<longleftrightarrow> x = \<omega> \<or> x = LNone"
  by (cases x; simp)
lemmas linearity_neq_one_iff2 =
  linearity_neq_one_iff[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]

lemma linearity_neq_many_iff: "x \<noteq> \<omega> \<longleftrightarrow> x = LOne \<or> x = LNone"
  by (cases x; simp)
lemmas linearity_neq_many_iff2 =
  linearity_neq_many_iff[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]

lemma linearity_none_impl_iff: "(x = 0 \<longrightarrow> P) \<longleftrightarrow> x = 1 \<or> x = \<omega> \<or> P"
  by (force simp add: imp_conv_disj linearity_neq_none_iff2 simp del: disj_not1)

lemmas linearity_none_impl_iff2 = linearity_none_impl_iff[simplified zero_linearity_def one_linearity_def]

lemma linearity_one_impl_iff:  "(x = 1 \<longrightarrow> P) \<longleftrightarrow> x = 0 \<or> x = \<omega> \<or> P"
  by (force simp add: imp_conv_disj linearity_neq_one_iff2 simp del: disj_not1)

lemmas linearity_one_impl_iff2 = linearity_one_impl_iff[simplified zero_linearity_def one_linearity_def]

lemma linearity_many_impl_iff:  "(x = \<omega> \<longrightarrow> P) \<longleftrightarrow> x = 0 \<or> x = 1 \<or> P"
  by (force simp add: imp_conv_disj linearity_neq_many_iff2 simp del: disj_not1)

lemmas linearity_many_impl_iff2 = linearity_many_impl_iff[simplified zero_linearity_def one_linearity_def]

lemma linearity_add_to_one_iff: "(c1 :: linearity) + c2 = 1 \<longleftrightarrow> c1 = 1 \<and> c2 = 0 \<or> c1 = 0 \<and> c2 = 1"
  by (cases c1; cases c2; simp add: zero_linearity_def one_linearity_def)

lemma linearity_one_lt_eq_many:
  "1 < c \<longleftrightarrow> c = \<omega>"
  by (cases c; simp add: one_linearity_def)

lemma linearity_one_le_eq_one_or_many:
  "1 \<le> c \<longleftrightarrow> c = 1 \<or> c = \<omega>"
  by (cases c; simp add: one_linearity_def)


definition droppable :: "kind env \<Rightarrow> type \<Rightarrow> bool" where
  "droppable K t \<equiv> D \<in> kinding_fn K t"

lemma droppable_simps[simp]:
  "\<And>K i. i < length K \<Longrightarrow> droppable K (TVar i) \<longleftrightarrow> D \<in> K ! i"
  "\<And>K i. droppable K (TVarBang i) \<longleftrightarrow> True"
  "\<And>K n ts s. droppable K (TCon n ts s) \<longleftrightarrow> list_all (droppable K) ts \<and> D \<in> sigil_kind s"
  "\<And>K ta tb. droppable K (TFun ta tb) \<longleftrightarrow> True"
  "\<And>K p. droppable K (TPrim p) \<longleftrightarrow> True"
  "\<And>K ts. droppable K (TSum ts) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_variant_state True (droppable K t) y) ts"
  "\<And>K ta tb. droppable K (TProduct ta tb) \<longleftrightarrow> droppable K ta \<and> droppable K tb"
  "\<And>K ts s. droppable K (TRecord ts s) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_record_state True (droppable K t) y) ts \<and> D \<in> sigil_kind s"
  "\<And>K. droppable K TUnit \<longleftrightarrow> True"
  by (force simp add: droppable_def all_set_conv_all_nth list_all_length split: variant_state.splits record_state.splits)+

lemma kinding_includes_drop_eq[simp]:
  "(\<exists>k. (K \<turnstile> t :\<kappa> k) \<and> D \<in> k) \<longleftrightarrow> K \<turnstile> t wellformed \<and> droppable K t"
  by (force simp add: kinding_def droppable_def)

definition shareable :: "kind env \<Rightarrow> type \<Rightarrow> bool" where
  "shareable K t \<equiv> S \<in> kinding_fn K t"

lemma shareable_simps[simp]:
  "\<And>K i. i < length K \<Longrightarrow> shareable K (TVar i) \<longleftrightarrow> S \<in> K ! i"
  "\<And>K i. shareable K (TVarBang i) \<longleftrightarrow> True"
  "\<And>K n ts s. shareable K (TCon n ts s) \<longleftrightarrow> list_all (shareable K) ts \<and> S \<in> sigil_kind s"
  "\<And>K ta tb. shareable K (TFun ta tb) \<longleftrightarrow> True"
  "\<And>K p. shareable K (TPrim p) \<longleftrightarrow> True"
  "\<And>K ts. shareable K (TSum ts) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_variant_state True (shareable K t) y) ts"
  "\<And>K ta tb. shareable K (TProduct ta tb) \<longleftrightarrow> shareable K ta \<and> shareable K tb"
  "\<And>K ts s. shareable K (TRecord ts s) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_record_state True (shareable K t) y) ts \<and> S \<in> sigil_kind s"
  "\<And>K. shareable K TUnit \<longleftrightarrow> True"
  by (force simp add: shareable_def all_set_conv_all_nth list_all_length split: variant_state.splits record_state.splits)+

lemma kinding_includes_share_eq[simp]:
  "(\<exists>k. (K \<turnstile> t :\<kappa> k) \<and> S \<in> k) \<longleftrightarrow> K \<turnstile> t wellformed \<and> shareable K t"
  by (force simp add: kinding_def shareable_def)

definition nonlinear :: "kind env \<Rightarrow> type \<Rightarrow> bool" where
  "nonlinear K t \<equiv> droppable K t \<and> shareable K t"

lemma nonlinear_simps[simp]:
  "\<And>K i. i < length K \<Longrightarrow> nonlinear K (TVar i) \<longleftrightarrow> D \<in> K ! i \<and> S \<in> K ! i"
  "\<And>K i. nonlinear K (TVarBang i) \<longleftrightarrow> True"
  "\<And>K n ts s. nonlinear K (TCon n ts s) \<longleftrightarrow> list_all (nonlinear K) ts \<and> D \<in> sigil_kind s \<and> S \<in> sigil_kind s"
  "\<And>K ta tb. nonlinear K (TFun ta tb) \<longleftrightarrow> True"
  "\<And>K p. nonlinear K (TPrim p) \<longleftrightarrow> True"
  "\<And>K ts. nonlinear K (TSum ts) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_variant_state True (nonlinear K t) y) ts"
  "\<And>K ta tb. nonlinear K (TProduct ta tb) \<longleftrightarrow> nonlinear K ta \<and> nonlinear K tb"
  "\<And>K ts s. nonlinear K (TRecord ts s) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_record_state True (nonlinear K t) y) ts \<and> D \<in> sigil_kind s \<and> S \<in> sigil_kind s"
  "\<And>K. nonlinear K TUnit \<longleftrightarrow> True"
  by (force simp add: nonlinear_def all_set_conv_all_nth list_all_length split: variant_state.splits record_state.splits)+



lemma sigil_kind_drop_impl_share:
  "D \<in> sigil_kind s \<Longrightarrow> S \<in> sigil_kind s"
  using sigil_kind.elims by auto

lemma sigil_kind_share_impl_drop:
  "S \<in> sigil_kind s \<Longrightarrow> D \<in> sigil_kind s"
  using sigil_kind.elims by auto

lemma sigil_kind_drop_iff_share:
  "D \<in> sigil_kind s \<longleftrightarrow> S \<in> sigil_kind s"
  using sigil_kind.elims by auto


definition well_kinded :: "kind \<Rightarrow> bool" where
  "well_kinded k \<equiv> D \<in> k \<longleftrightarrow> S \<in> k"

definition well_kinded_all :: "kind list \<Rightarrow> bool" where
  "well_kinded_all \<equiv> list_all well_kinded"


lemma droppable_iff_nonlinear:
  "well_kinded_all K \<Longrightarrow> K \<turnstile> t wellformed \<Longrightarrow> droppable K t \<longleftrightarrow> nonlinear K t"
  by (induct t)
      (clarsimp
        simp add: list_all_length well_kinded_all_def well_kinded_def sigil_kind_drop_iff_share
        prod_eq_iff_proj_eq in_set_conv_nth type_wellformed_pretty_def
        split: prod.splits variant_state.splits record_state.splits; metis)+

lemma shareable_iff_nonlinear:
  "well_kinded_all K \<Longrightarrow> K \<turnstile> t wellformed \<Longrightarrow> shareable K t \<longleftrightarrow> nonlinear K t"
  by (induct t)
      (clarsimp
        simp add: list_all_length well_kinded_all_def well_kinded_def sigil_kind_drop_iff_share
        prod_eq_iff_proj_eq in_set_conv_nth type_wellformed_pretty_def
        split: prod.splits variant_state.splits record_state.splits; metis)+

lemma droppable_iff_shareable:
  "well_kinded_all K \<Longrightarrow> K \<turnstile> t wellformed \<Longrightarrow> droppable K t \<longleftrightarrow> shareable K t"
  by (simp add: droppable_iff_nonlinear shareable_iff_nonlinear)

lemma shareable_iff_droppable:
  "well_kinded_all K \<Longrightarrow> K \<turnstile> t wellformed \<Longrightarrow> shareable K t \<longleftrightarrow> droppable K t"
  by (simp add: droppable_iff_nonlinear shareable_iff_nonlinear)


definition is_used :: "kind env \<Rightarrow> type \<Rightarrow> ('a :: {one, order}) \<Rightarrow> bool" where
  "is_used K t c \<equiv> c \<ge> 1 \<or> droppable K t"

definition is_shared :: "kind list \<Rightarrow> type \<Rightarrow> ('a :: {one, semilattice_sup}) \<Rightarrow> bool" where
  "is_shared K t c \<equiv> c \<le> 1 \<or> shareable K t"

lemma is_used_linearity_simps[simp]:
  "is_used K t \<omega> = True"
  "is_used K t LOne = True"
  "is_used K t LNone = droppable K t"
  by (clarsimp simp add: one_linearity_def is_used_def)+

lemmas is_used_linearity_simps2[simp] =
  is_used_linearity_simps(2-)[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]

lemma is_shared_linearity_simps[simp]:
  "is_shared K t \<omega> = shareable K t"
  "is_shared K t LOne = True"
  "is_shared K t LNone = True"
  by (clarsimp simp add: is_shared_def one_linearity_def)+

lemmas is_shared_linearity_simps2[simp] =
  is_shared_linearity_simps(2-)[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]


definition merge_drop_condition_comp :: "kind list \<Rightarrow> type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool" where
  "merge_drop_condition_comp K t c1 c2 \<equiv> (c1 = 0 \<and> c2 \<noteq> 0) \<or> (c1 \<noteq> 0 \<and> c2 = 0) \<longrightarrow> droppable K t"

definition merge_drop_condition :: "kind list \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> linearity list \<Rightarrow> bool" where
  "merge_drop_condition K \<equiv> list_all3 (merge_drop_condition_comp K)"

lemmas merge_drop_condition_conv_all_nth =
  list_all3_conv_all_nth[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]

lemmas merge_drop_condition_Nil1[simp] =
  list_all3_Nil1[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]
lemmas merge_drop_condition_Nil2[simp] =
  list_all3_Nil2[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]
lemmas merge_drop_condition_Nil3[simp] =
  list_all3_Nil3[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]

lemmas merge_drop_condition_Cons[simp] =
  list_all3_Cons[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]

lemmas merge_drop_condition_Cons1 =
  list_all3_Cons1[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]
lemmas merge_drop_condition_Cons2 =
  list_all3_Cons2[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]
lemmas merge_drop_condition_Cons3 =
  list_all3_Cons3[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]

lemma merge_drop_condition_nthD[dest]:
  "\<lbrakk> merge_drop_condition K G C1 C2; C1 ! i = 0; C2 ! i \<noteq> 0; i < length G \<rbrakk> \<Longrightarrow> droppable K (G ! i)"
  "\<lbrakk> merge_drop_condition K G C1 C2; C1 ! i \<noteq> 0; C2 ! i = 0; i < length G \<rbrakk> \<Longrightarrow> droppable K (G ! i)"
  by (clarsimp simp add: merge_drop_condition_conv_all_nth merge_drop_condition_comp_def)+


(*
\<Gamma> is input.
C is output.
The expression is input.
For synthesising, the type is output.
For checking, the type is input.

Not that C being output means that in an assumption, C should be a variable.
If you want to enforce a structure on C, you have to use an equality so it can do computation.
*)
inductive tyinf_synth :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _ , _ \<turnstile>\<down> _ : _" [30,0,0,0,0,20] 60)
      and tyinf_check :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _ , _ \<turnstile>\<up> _ : _" [30,0,0,0,0,20] 60)
      and tyinf_all_synth :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> bool"
          ("_, _, _, _ \<turnstile>\<down>* _ : _" [30,0,0,0,0,20] 60) where

(* synthesising *)

  tyinf_var    : "\<lbrakk> i < length \<Gamma>
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, (replicate (length \<Gamma>) 0)[i := 1] \<turnstile>\<down> Var i : (\<Gamma> ! i)"

| tyinf_tuple  : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> t : \<tau>1
                  ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<down> u : \<tau>2
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<down> Tuple t u : TProduct \<tau>1 \<tau>2"

| tyinf_con    : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : t
                  ; (tag, t, Unchecked) \<in> set ts
                  ; K \<turnstile> TSum ts wellformed
                  ; ts = ts'
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Con ts tag x : TSum ts'"

| tyinf_esac   : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : TSum ts
                  ; [(n, t, Unchecked)] = filter ((=) Unchecked \<circ> snd \<circ> snd) ts
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Esac x n : t"


| tyinf_lit    : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down> Lit l : TPrim (lit_type l)"

| tyinf_slit   : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down> SLit s : TPrim String"

| tyinf_unit   : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down> Unit : TUnit"

| tyinf_member : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : TRecord ts s
                  ; shareable K (TRecord ts s)
                  ; f < length ts
                  ; snd (snd (ts ! f)) = Present
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Member e f : fst (snd (ts ! f))"

| tyinf_put    : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> e : \<tau>1
                  ; \<tau>1 = TRecord ts s
                  ; sigil_perm s \<noteq> Some ReadOnly
                  ; f < length ts
                  ; ts ! f = (n, t, taken)
                  ; droppable K t \<or> taken = Taken
                  ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<up> e' : t
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<down> Put e f e' : TRecord (ts[f := (n,t,Present)]) s"

| tyinf_prim   : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down>* args : map TPrim ts
                  ; prim_op_type oper = (ts,t)
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Prim oper args : TPrim t"

| tyinf_struct : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down>* es : ts
                  ; ts = ts' \<^cancel>\<open>FIXME: remove ts'\<close>
                  ; length ns = length ts'
                  ; distinct ns
                  ; vs = zip ns (map (\<lambda>t. (t,Present)) ts)
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Struct ns ts' es : TRecord vs Unboxed"

(* checking *)

| tyinf_cast   : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : \<tau>1
                  ; \<tau>1 = TPrim (Num nt)
                  ; upcast_valid nt nt1
                  ; nt1 = nt2 \<^cancel>\<open>FIXME: nt1 is unecessary\<close>
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> Cast nt1 e : TPrim (Num nt2)"

| tyinf_app    : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> a : \<tau>1
                  ; \<tau>1 = TFun x y
                  ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<up> b : x
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> App a b : y"

| tyinf_split  : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : TProduct t u
                  ; \<Xi>, K, (t # u # \<Gamma>), C2o \<turnstile>\<up> y : t'
                  ; C2o = ct # cu # C2
                  ; is_used K t ct
                  ; is_used K u cu
                  ; is_shared K t ct
                  ; is_shared K u cu
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> Split x y : t'"

| tyinf_let    : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : t
                  ; \<Xi>, K, (t # \<Gamma>), C2o \<turnstile>\<up> y : u
                  ; C2o = ct # C2
                  ; is_used K t ct
                  ; is_shared K t ct
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> Let x y : u"

| tyinf_letb   : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : t
                  ; \<Xi>, K, (t # \<Gamma>), (ct # C2) \<turnstile>\<up> y : u
                  ; is_used K t ct
                  ; E \<in> kinding_fn K t
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> LetBang is x y : u"

| tyinf_case   : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : \<tau>1
                  ; \<tau>1 = TSum ts
                  ; (tag, t, Unchecked) \<in> set ts
                  ; \<Xi>, K, (t # \<Gamma>), C2ao \<turnstile>\<up> a : u
                  ; C2ao = ct # C2a
                  ; is_used K t ct
                  ; is_shared K t ct
                  ; \<Xi>, K, (TSum (tagged_list_update tag (t, Checked) ts) # \<Gamma>), C2bo \<turnstile>\<up> b : u
                  ; C2bo = csum # C2b
                  ; is_used K (TSum (tagged_list_update tag (t, Checked) ts)) csum
                  ; is_shared K (TSum (tagged_list_update tag (t, Checked) ts)) csum
                  ; merge_drop_condition K \<Gamma> C2a C2b
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> (countMax C2a C2b) \<turnstile>\<up> Case x tag a b : u"

| tyinf_if     : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : \<tau>
                  ; \<tau> = TPrim Bool
                  ; \<Xi>, K, \<Gamma>, C2a \<turnstile>\<up> a : t
                  ; \<Xi>, K, \<Gamma>, C2b \<turnstile>\<up> b : t
                  ; merge_drop_condition K \<Gamma> C2a C2b
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> (countMax C2a C2b) \<turnstile>\<up> If x a b : t"

| tyinf_take   : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> e : \<tau>1
                  ; \<tau>1 = TRecord ts s
                  ; sigil_perm s \<noteq> Some ReadOnly
                  ; f < length ts
                  ; ts ! f = (n, t, Present)
                  ; shareable K t \<or> taken = Taken
                  ; \<Xi>, K, (t # TRecord (ts [f := (n,t,taken)]) s # \<Gamma>), C2o \<turnstile>\<up> e' : u
                  ; C2o = ct # cr # C2
                  ; is_used K t ct
                  ; is_used K (TRecord (ts [f := (n,t,taken)]) s) cr
                  ; is_shared K t ct
                  ; is_shared K (TRecord (ts [f := (n,t,taken)]) s) cr
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> Take e f e' : u"

| tyinf_switch: "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : \<tau>
                 ; \<tau> = \<tau>'
                 \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> x : \<tau>'"

(* TODO: we don't need promote expressions *)
| tyinf_promote: "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : t'
                  ; K \<turnstile> t' \<sqsubseteq> t
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> Promote t x : t"

| tyinf_all_empty : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down>* [] : []"

| tyinf_all_cons  : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> e : t
                     ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<down>* es : ts
                     \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<down>* (e # es) : (t # ts)"

(*
| tyinf_afun   : "\<lbrakk> \<Xi> f = (K', t, u)
                   ; t' = instantiate ts t
                   ; u' = instantiate ts u
                   ; list_all2 (kinding K) ts K'
                   ; K' \<turnstile> TFun t u wellformed
                   ; K \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile> AFun f ts : TFun t' u'"

| tyinf_fun    : "\<lbrakk> \<Xi>, K', [Some t] \<turnstile> f : u
                   ; t' = instantiate ts t
                   ; u' = instantiate ts u
                   ; K \<turnstile> \<Gamma> consumed
                   ; K' \<turnstile> t wellformed
                   ; list_all2 (kinding K) ts K'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Fun f ts : TFun t' u'"
*)

inductive_cases tyinf_synth_varE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Var i : t"
inductive_cases tyinf_synth_tupleE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Tuple e1 e2 : t"
inductive_cases tyinf_synth_conE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Con ts tag x : t"
inductive_cases tyinf_synth_esacE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Esac x n : t"
inductive_cases tyinf_synth_litE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Lit l : t"
inductive_cases tyinf_synth_slitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> SLit s : t"
inductive_cases tyinf_synth_unitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Unit : t"
inductive_cases tyinf_synth_memberE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Member e f : t"
inductive_cases tyinf_synth_putE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Put e f e' : t"
inductive_cases tyinf_synth_primE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Prim oper arg : t"
inductive_cases tyinf_synth_structE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Struct ns ts es : t"

inductive_cases tyinf_check_castE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Cast nm e : t"
inductive_cases tyinf_check_appE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> App x y : t"
inductive_cases tyinf_check_splitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Split x y : t"
inductive_cases tyinf_check_letE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Let x y : t"
inductive_cases tyinf_check_letbE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> LetBang is x y : t"
inductive_cases tyinf_check_caseE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Case x tag a b : t"
inductive_cases tyinf_check_ifE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> If x a b : t"
inductive_cases tyinf_check_takeE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Take e f e' : t"

inductive_cases tyinf_check_varE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Var i : t"
inductive_cases tyinf_check_tupleE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Tuple e1 e2 : t"
inductive_cases tyinf_check_conE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Con ts tag x : t"
inductive_cases tyinf_check_esacE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Esac x n : t"
inductive_cases tyinf_check_litE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Lit l : t"
inductive_cases tyinf_check_slitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> SLit s : t"
inductive_cases tyinf_check_unitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Unit : t"
inductive_cases tyinf_check_memberE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Member e f : t"
inductive_cases tyinf_check_putE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Put e f e' : t"
inductive_cases tyinf_check_primE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Prim oper arg : t"
inductive_cases tyinf_check_structE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Struct ns ts es : t"

inductive_cases tyinf_check_promoteE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Promote t x : t"

inductive_cases tyinf_all_synth_consE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* (e # es) : ts"
inductive_cases tyinf_all_synth_nilE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* [] : ts"

lemmas tyinf_synth_safe_intros =
  tyinf_var tyinf_tuple tyinf_con tyinf_esac tyinf_lit tyinf_slit tyinf_unit tyinf_member tyinf_put
  tyinf_prim tyinf_struct

lemmas tyinf_checking_safe_intros =
  tyinf_cast tyinf_app tyinf_split tyinf_let tyinf_letb tyinf_case tyinf_if tyinf_take
  tyinf_promote tyinf_all_empty tyinf_all_cons
  tyinf_synth_safe_intros[THEN tyinf_switch]

lemmas tyinf_safe_intros = tyinf_synth_safe_intros tyinf_checking_safe_intros



(* Obviously true, but ensures C' and t' are schematic *)
lemma tyinf_checkI:
  "\<lbrakk> \<Xi>, K, \<Gamma>, C' \<turnstile>\<down> e : t'
   ; C = C'
   ; t = t'
   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : t"
  by fast

ML \<open>
fun trace_tac ctxt (st : thm) = print_tac ctxt (@{make_string} st) st
fun trace_tac' ctxt  _ = trace_tac ctxt

  fun typinfer_tac_N (n : int) (ctxt : Proof.context) : tactic =
    let val tac = (resolve_tac ctxt @{thms tyinf_safe_intros} ORELSE'
                  fast_force_tac (ctxt addsimps @{thms kinding_simps}));
     in REPEAT_DETERM_N n (FIRSTGOAL tac)
     end

  val typinfer_tac = typinfer_tac_N ~1
\<close>






definition
  ty1 :: " Cogent.type"
where
  "ty1 \<equiv> TRecord [(''b'', (TPrim (Num U8), Present)), (''a'', (TPrim (Num U32), Present))] Unboxed"

definition
  expr1 :: "string Cogent.expr"
where
  "expr1 \<equiv> Take (Var 0) 0 (Take (Var 1) 1 (Struct [''b'',''a''] [TPrim (Num U8), TPrim (Num U32)] [Var 2, Var 0]))"

schematic_goal typing1: "\<Xi>, [], [ty1], ?C \<turnstile>\<up> expr1 : ty1"
  unfolding expr1_def ty1_def
  apply clarsimp
  apply (tactic \<open>typinfer_tac_N 7 @{context}\<close>)
  apply simp
  apply (tactic \<open>typinfer_tac_N 31 @{context}\<close>)

  oops


definition
  ty2a :: "Cogent.type"
where
  "ty2a \<equiv> TRecord
            [ (''a'', TCon ''A'' [] (Boxed Writable undefined), Present)
            , (''b'', TCon ''A'' [] (Boxed Writable undefined), Taken)]
            Unboxed"

definition
  ty2b :: "Cogent.type"
where
  "ty2b \<equiv> TRecord
            [ (''a'', TCon ''A'' [] (Boxed Writable undefined), Taken)
            , (''b'', TCon ''A'' [] (Boxed Writable undefined), Present)]
            Unboxed"

definition
  expr2 :: "string Cogent.expr"
where
  "expr2 \<equiv> Take (Var 0) 0 (Put (Var 1) 1 (Var 0))"

schematic_goal typing2: "\<Xi>, [], [ty2a], ?C \<turnstile>\<up> expr2 : ty2b"
  unfolding expr2_def ty2a_def ty2b_def
  apply clarsimp
  apply (tactic \<open>typinfer_tac @{context}\<close>)
  done
thm typing2[simplified]

schematic_goal typing3:
  "\<exists>ts. \<Xi>, [], [TCon ''A'' [] (Boxed Writable undefined)], ?C \<turnstile>\<down> Struct [''a'',''b''] ts [Var 0, Var 0] : ?t"
  apply (rule exI)
  apply (rule tyinf_checkI)
    apply (tactic \<open>typinfer_tac @{context}\<close>)
  done
thm typing3[simplified]







definition shareable_constraint :: "kind list \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> bool" where
  "shareable_constraint K \<equiv> list_all2 (is_shared K)"

lemmas shareable_constraint_conv_all_nth =
  list_all2_conv_all_nth[where P=\<open>is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                         simplified shareable_constraint_def[symmetric]]

lemmas shareable_constraint_Nil1[simp] =
  list_all2_Nil[where P=\<open>is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                 simplified shareable_constraint_def[symmetric]]
lemmas shareable_constraint_Nil2[simp] =
  list_all2_Nil2[where P=\<open>is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                 simplified shareable_constraint_def[symmetric]]

lemmas shareable_constraint_Cons[simp] =
  list_all2_Cons[where P=\<open>is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                 simplified shareable_constraint_def[symmetric]]
lemmas shareable_constraint_Cons1 =
  list_all2_Cons1[where P=\<open>is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                  simplified shareable_constraint_def[symmetric]]
lemmas shareable_constraint_Cons2 =
  list_all2_Cons2[where P=\<open>is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                  simplified shareable_constraint_def[symmetric]]

lemma shareable_constraint_shareable_nthD[dest]:
  "shareable_constraint K G C \<Longrightarrow> C ! i > 1 \<Longrightarrow> i < length G \<Longrightarrow> shareable K (G ! i)"
  by (force simp add: shareable_constraint_conv_all_nth is_shared_def)

lemma shareable_constraint_shareable_nth_manyD[dest]:
  "shareable_constraint K G C \<Longrightarrow> C ! i = \<omega> \<Longrightarrow> i < length G \<Longrightarrow> shareable K (G ! i)"
  by (simp add: shareable_constraint_shareable_nthD linearity_one_lt_eq_many)

lemma shareable_constraint_add[dest]:
  assumes "length C1 = length C2"
  shows
    "shareable_constraint K \<Gamma> (C1 \<oplus> C2) \<Longrightarrow> shareable_constraint K \<Gamma> C1"
    "shareable_constraint K \<Gamma> (C1 \<oplus> C2) \<Longrightarrow> shareable_constraint K \<Gamma> C2"
  using assms
  by (force dest: canonical_trans_le_add1 canonical_trans_le_add2
      simp add: shareable_constraint_conv_all_nth lin_add_sym is_shared_def)+



definition new_is_shared :: "kind list \<Rightarrow> type \<Rightarrow> ('a :: {one, canonically_ordered_monoid_add}) \<Rightarrow> 'a \<Rightarrow> bool" where
  "new_is_shared K \<equiv> (\<lambda>t c1 c2. c1 + c2 \<le> 1 \<or> shareable K t)"

definition new_shareable_constraint :: "kind list \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> linearity list \<Rightarrow> bool" where
  "new_shareable_constraint K \<equiv> list_all3 (new_is_shared K)"

lemmas new_shareable_constraint_conv_all_nth =
  list_all3_conv_all_nth[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                        , simplified new_shareable_constraint_def[symmetric]]

lemmas new_shareable_constraint_Nil[simp,intro!] =
  all3Nil[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
         , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Nil1[simp] =
  list_all3_Nil1[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Nil2[simp] =
  list_all3_Nil2[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Nil3[simp] =
  list_all3_Nil3[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                , simplified new_shareable_constraint_def[symmetric]]

lemmas new_shareable_constraint_Cons =
  list_all3_Cons[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Cons1 =
  list_all3_Cons1[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                 , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Cons2 =
  list_all3_Cons2[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                 , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Cons3 =
  list_all3_Cons3[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                 , simplified new_shareable_constraint_def[symmetric]]

lemma is_shared_plus_iff:
  "is_shared K t (c1 + c2) \<longleftrightarrow> is_shared K t c1 \<and> is_shared K t c2 \<and> new_is_shared K t c1 c2"
  unfolding is_shared_def new_is_shared_def
  by (force dest: canonical_trans_le_add1 canonical_trans_le_add2)

lemma shareable_constraint_plus_iff:
  assumes "length C1 = length C2"
  shows
    "shareable_constraint K \<Gamma> (C1 \<oplus> C2) \<longleftrightarrow>
      shareable_constraint K \<Gamma> C1
      \<and> shareable_constraint K \<Gamma> C2
      \<and> new_shareable_constraint K \<Gamma> C1 C2"
  using assms
  by (force simp add: shareable_constraint_conv_all_nth new_shareable_constraint_conv_all_nth
      is_shared_plus_iff)

lemma is_shared_max_iff:
  shows "is_shared K t (sup c1 c2) \<longleftrightarrow> is_shared K t c1 \<and> is_shared K t c2"
  by (force simp add: is_shared_def one_linearity_def)

lemma shareable_constraint_max_iff:
  assumes "length C1 = length C2"
  shows "shareable_constraint K \<Gamma> (countMax C1 C2) \<longleftrightarrow> shareable_constraint K \<Gamma> C1 \<and> shareable_constraint K \<Gamma> C2"
  using assms
  by (force simp add: shareable_constraint_conv_all_nth new_shareable_constraint_conv_all_nth
      is_shared_max_iff)


inductive tycount_context_constraint_comp :: "kind list \<Rightarrow> type \<Rightarrow> linearity \<Rightarrow> type option \<Rightarrow> bool" where
  "shareable K t \<Longrightarrow> tycount_context_constraint_comp K t \<omega> (Some t)"
| "tycount_context_constraint_comp K t 1 (Some t)"
| "tycount_context_constraint_comp K t 0 None"

definition tycount_context_constraint :: "kind list \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> type option list \<Rightarrow> bool" where
  "tycount_context_constraint K \<equiv> list_all3 (tycount_context_constraint_comp K)"

lemmas tycount_context_constraint_conv_all_nth =
  list_all3_conv_all_nth[where P=\<open>tycount_context_constraint_comp K\<close> for K, simplified tycount_context_constraint_def[symmetric]]

lemmas tycount_context_constraint_Cons[simp] =
  list_all3_Cons[where P=\<open>tycount_context_constraint_comp K\<close> for K, simplified tycount_context_constraint_def[symmetric]]

lemmas tycount_context_constraint_Cons12[simp] =
  list_all3_Cons12[where P=\<open>tycount_context_constraint_comp K\<close> for K, simplified tycount_context_constraint_def[symmetric]]

lemma tycount_context_constraint_empty:
  "tycount_context_constraint K G (replicate (length G) 0) (replicate (length G) None)"
  by (simp add: tycount_context_constraint_conv_all_nth tycount_context_constraint_comp.simps)

lemma tycount_context_constraint_one:
  "tycount_context_constraint K G (replicate (length G) 1) (map Some G)"
  by (simp add: tycount_context_constraint_conv_all_nth tycount_context_constraint_comp.simps)




lemma tyinf_context_lengths:
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : t    \<Longrightarrow> length C = length \<Gamma>"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> e : t    \<Longrightarrow> length C = length \<Gamma>"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* es : ts \<Longrightarrow> length C = length \<Gamma>"
  by (induct rule: tyinf_synth_tyinf_check_tyinf_all_synth.inducts) simp+


lemma tyinf_preserves_wellformed[dest]:
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : t    \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> K \<turnstile> t wellformed"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> e : t    \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> K \<turnstile> t wellformed"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* es : ts \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> K \<turnstile>* ts wellformed"
proof (induct rule: tyinf_synth_tyinf_check_tyinf_all_synth.inducts)
  case tyinf_esac then show ?case
    by (clarsimp simp add: type_wellformed_pretty_simps type_wellformed_all_pretty_def
        prod_eq_iff_proj_eq
        list_all_length map_fst_zip_take less_Suc_eq_0_disj singleton_filter_iff)
next
  case tyinf_put then show ?case
    by (force intro: distinct_upd_sameI simp add: type_wellformed_pretty_simps type_wellformed_all_length map_update nth_list_update)
next
  case tyinf_case then show ?case
    by (force simp add: type_wellformed_pretty_simps type_wellformed_all_length in_set_conv_nth All_less_Suc2)
next
  case tyinf_take then show ?case
    by (clarsimp simp add: type_wellformed_pretty_simps type_wellformed_all_length
        prod_eq_iff_proj_eq distinct_fst_tags_update list_all_length nth_list_update All_less_Suc2)
next
  case tyinf_promote then show ?case
    by (force dest: subtyping_wellformed_preservation)
qed (simp; simp add: type_wellformed_pretty_simps type_wellformed_all_length list_all_length map_fst_zip_take less_Suc_eq_0_disj)+

lemmas tyinf_shareable_constraint_plus_iff =
  shareable_constraint_plus_iff[OF trans[OF tyinf_context_lengths(1) tyinf_context_lengths(1)[symmetric]]]
  shareable_constraint_plus_iff[OF trans[OF tyinf_context_lengths(1) tyinf_context_lengths(2)[symmetric]]]
  shareable_constraint_plus_iff[OF trans[OF tyinf_context_lengths(2) tyinf_context_lengths(1)[symmetric]]]
  shareable_constraint_plus_iff[OF trans[OF tyinf_context_lengths(2) tyinf_context_lengths(2)[symmetric]]]

  shareable_constraint_plus_iff[OF trans[OF tyinf_context_lengths(1) tyinf_context_lengths(2)[symmetric, where \<Gamma>="x # \<Gamma>" and C="cx # C" for x \<Gamma> cx C, simplified]]]
  shareable_constraint_plus_iff[OF trans[OF tyinf_context_lengths(1) tyinf_context_lengths(2)[symmetric, where \<Gamma>="x # y # \<Gamma>" and C="cx # cy # C" for x y \<Gamma> cx cy C, simplified]]]

lemmas tyinf_shareable_constraint_max_iff =
  shareable_constraint_max_iff[OF trans[OF tyinf_context_lengths(1) tyinf_context_lengths(1)[symmetric]]]
  shareable_constraint_max_iff[OF trans[OF tyinf_context_lengths(1) tyinf_context_lengths(2)[symmetric]]]
  shareable_constraint_max_iff[OF trans[OF tyinf_context_lengths(2) tyinf_context_lengths(1)[symmetric]]]
  shareable_constraint_max_iff[OF trans[OF tyinf_context_lengths(2) tyinf_context_lengths(2)[symmetric]]]

  shareable_constraint_max_iff[OF trans[OF tyinf_context_lengths(1) tyinf_context_lengths(2)[symmetric, where \<Gamma>="x # \<Gamma>" and C="cx # C" for x \<Gamma> cx C, simplified]]]
  shareable_constraint_max_iff[OF trans[OF tyinf_context_lengths(1) tyinf_context_lengths(2)[symmetric, where \<Gamma>="x # y # \<Gamma>" and C="cx # cy # C" for x y \<Gamma> cx cy C, simplified]]]



lemma weakening_context_correspond:
  assumes
    "i < length \<Gamma>"
  shows
    "tycount_context_constraint K \<Gamma> ((replicate (length \<Gamma>) 0)[i := 1]) ((replicate (length \<Gamma>) None)[i := Some (\<Gamma> ! i)])"
  using assms
  by (clarsimp simp add: tycount_context_constraint_conv_all_nth tycount_context_constraint_comp.simps nth_list_update split: linearity.splits)


definition join_contexts_comp :: "type \<Rightarrow> linearity \<Rightarrow> type option" where
  "join_contexts_comp t c \<equiv> if c = LNone then None else Some t"

definition join_contexts :: "type list \<Rightarrow> linearity list \<Rightarrow> type option list" where
  "join_contexts \<equiv> map2 join_contexts_comp"

lemma join_contexts_length_eq[simp]:
  "length (join_contexts G C) = min (length G) (length C)"
  by (simp add: join_contexts_def)

lemma join_contexts_nth[simp]:
  assumes
    "i < length G"
    "i < length C"
  shows
    "join_contexts G C ! i = join_contexts_comp (G ! i) (C ! i)"
  using assms
  by (simp add: join_contexts_def)


subsubsection \<open> join with + respects tycount_context_constraint \<close>

lemma join_contexts_tycount_context_constraint_comp:
  assumes
    "tycount_context_constraint_comp K t c1 mt1"
    "tycount_context_constraint_comp K t c2 mt2"
    "new_is_shared K t c1 c2"
  shows
    "tycount_context_constraint_comp K t (c1 + c2) (join_contexts_comp t (c1 + c2))"
  using assms
  apply (simp add: split_comp.simps tycount_context_constraint_comp.simps join_contexts_comp_def)
  apply (elim disjE; clarsimp simp add: zero_linearity_def one_linearity_def new_is_shared_def)
  done

lemma join_contexts_tycount_context_constraint:
  assumes
    "tycount_context_constraint K G C1 \<Gamma>1"
    "tycount_context_constraint K G C2 \<Gamma>2"
    "new_shareable_constraint K G C1 C2"
  shows
    "tycount_context_constraint K G (C1 \<oplus> C2) (join_contexts G (C1 \<oplus> C2))"
  using assms
  by (force simp add:
      split_conv_all_nth tycount_context_constraint_conv_all_nth type_wellformed_all_length
      new_shareable_constraint_conv_all_nth join_contexts_tycount_context_constraint_comp)

subsubsection \<open> join with + respects split \<close>

lemma join_contexts_split_comp:
  assumes
    "K \<turnstile> t wellformed"
    "tycount_context_constraint_comp K t c1 mt1"
    "tycount_context_constraint_comp K t c2 mt2"
    "new_is_shared K t c1 c2"
  shows
    "K \<turnstile> join_contexts_comp t (c1 + c2) \<leadsto> mt1 \<parallel> mt2"
  using assms
  apply (simp add: split_comp.simps tycount_context_constraint_comp.simps join_contexts_comp_def)
  apply (elim disjE; clarsimp simp add: zero_linearity_def one_linearity_def new_is_shared_def)
  done

lemma join_contexts_split:
  assumes
    "K \<turnstile>* G wellformed"
    "tycount_context_constraint K G C1 \<Gamma>1"
    "tycount_context_constraint K G C2 \<Gamma>2"
    "new_shareable_constraint K G C1 C2"
  shows
    "K \<turnstile> join_contexts G (C1 \<oplus> C2) \<leadsto> \<Gamma>1 | \<Gamma>2"
  using assms
  by (clarsimp simp add:
      split_conv_all_nth tycount_context_constraint_conv_all_nth type_wellformed_all_length
      new_shareable_constraint_conv_all_nth join_contexts_split_comp)


subsubsection \<open> join with sup respects tycount_context_constraint \<close>

lemma join_contexts_max_tycount_context_constraint_comp:
  assumes
    "tycount_context_constraint_comp K t c1 mt1"
    "tycount_context_constraint_comp K t c2 mt2"
  shows
    "tycount_context_constraint_comp K t (sup c1 c2) (join_contexts_comp t (sup c1 c2))"
  using assms
  apply (simp add: split_comp.simps tycount_context_constraint_comp.simps join_contexts_comp_def)
  apply (elim disjE; clarsimp simp add: zero_linearity_def one_linearity_def new_is_shared_def)
  done

lemma join_contexts_max_tycount_context_constraint:
  assumes
    "K \<turnstile>* G wellformed"
    "tycount_context_constraint K G C1 \<Gamma>1"
    "tycount_context_constraint K G C2 \<Gamma>2"
  shows
    "tycount_context_constraint K G (countMax C1 C2) (join_contexts G (countMax C1 C2))"
  using assms
  by (force simp add:
      split_conv_all_nth tycount_context_constraint_conv_all_nth type_wellformed_all_length
      new_shareable_constraint_conv_all_nth join_contexts_max_tycount_context_constraint_comp)


subsubsection \<open> join with sup respects split \<close>

lemma join_contexts_max_split_comp:
  assumes
    "K \<turnstile> t wellformed"
    "tycount_context_constraint_comp K t c1 mt1"
    "tycount_context_constraint_comp K t c2 mt2"
    "new_is_shared K t c1 c2"
  shows
    "K \<turnstile> join_contexts_comp t (sup c1 c2) \<leadsto> mt1 \<parallel> mt2"
  using assms
  by (force simp add: zero_linearity_def one_linearity_def new_is_shared_def
      split_comp.simps tycount_context_constraint_comp.simps join_contexts_comp_def)

lemma join_contexts_max_split:
  assumes
    "K \<turnstile>* G wellformed"
    "tycount_context_constraint K G C1 \<Gamma>1"
    "tycount_context_constraint K G C2 \<Gamma>2"
    "new_shareable_constraint K G C1 C2"
  shows
    "K \<turnstile> join_contexts G (countMax C1 C2) \<leadsto> \<Gamma>1 | \<Gamma>2"
  using assms
  by (clarsimp simp add:
      split_conv_all_nth tycount_context_constraint_conv_all_nth type_wellformed_all_length
      new_shareable_constraint_conv_all_nth join_contexts_max_split_comp)

subsubsection \<open> join sup can be weakened \<close>

lemma join_contexts_weaken_max_comp:
  assumes
    "K \<turnstile> t wellformed"
    "merge_drop_condition_comp K t c1 c2"
    "tycount_context_constraint_comp K t c1 mt1"
    "tycount_context_constraint_comp K t c2 mt2"
  shows
    "weakening_comp K (join_contexts_comp t (sup c1 c2)) mt1"
    "weakening_comp K (join_contexts_comp t (sup c1 c2)) mt2"
  using assms
  by (force simp add:
      join_contexts_comp_def weakening_comp.simps tycount_context_constraint_comp.simps
      merge_drop_condition_comp_def
      zero_linearity_def one_linearity_def droppable_def imp_conjL linearity_none_impl_iff2)+

lemma join_contexts_weaken_max:
  assumes
    "K \<turnstile>* G wellformed"
    "merge_drop_condition K G C1 C2"
    "tycount_context_constraint K G C1 \<Gamma>1"
    "tycount_context_constraint K G C2 \<Gamma>2"
  shows
    "K \<turnstile> join_contexts G (countMax C1 C2) \<leadsto>w \<Gamma>1"
    "K \<turnstile> join_contexts G (countMax C1 C2) \<leadsto>w \<Gamma>2"
  using assms
  by (fastforce intro: join_contexts_weaken_max_comp
      simp add: tycount_context_constraint_conv_all_nth type_wellformed_all_length
      weakening_conv_all_nth merge_drop_condition_conv_all_nth)+



section \<open> Main Theorem: An Inferred Typing Implies a Non-Algorithmic Typing \<close>

theorem tyinf_to_typing:
  assumes
    "well_kinded_all K"
    "shareable_constraint K G C"
    "K \<turnstile>* G wellformed"
  shows
  "\<Xi>, K, G, C \<turnstile>\<down> e : t    \<Longrightarrow> \<exists>\<Gamma>. tycount_context_constraint K G C \<Gamma> \<and> \<Xi>, K, \<Gamma> \<turnstile> e : t"
  "\<Xi>, K, G, C \<turnstile>\<up> e : t    \<Longrightarrow> \<exists>\<Gamma>. tycount_context_constraint K G C \<Gamma> \<and> \<Xi>, K, \<Gamma> \<turnstile> e : t"
  "\<Xi>, K, G, C \<turnstile>\<down>* es : ts \<Longrightarrow> \<exists>\<Gamma>. tycount_context_constraint K G C \<Gamma> \<and> \<Xi>, K, \<Gamma> \<turnstile>* es : ts"
  using assms
proof (induct rule: tyinf_synth_tyinf_check_tyinf_all_synth.inducts)
  case tyinf_var then show ?case
    by (fastforce
        intro!: typing_typing_all.intros weakening_context_correspond weakening_refl
        simp add: Cogent.empty_def type_wellformed_all_length)
next case tyinf_tuple then show ?case
    by (fastforce
        intro!: typing_typing_all.intros join_contexts_tycount_context_constraint join_contexts_split
        simp add: tyinf_shareable_constraint_plus_iff)
next
  case tyinf_member then show ?case
    by (force intro!: typing_typing_all.intros kinding_kinding_allI
              simp add: prod_eq_iff_proj_eq shareable_def tyinf_context_lengths shareable_constraint_plus_iff)
next
  case tyinf_put then show ?case
    by (simp add: tyinf_shareable_constraint_plus_iff droppable_def,
        blast intro: join_contexts_tycount_context_constraint typing_typing_all.intros
        join_contexts_split kinding_kinding_allI)
next
  case tyinf_struct then show ?case
    by (force intro!: typing_typing_all.intros simp add: zip_map2)
next
  case tyinf_app then show ?case
    by (fastforce
        intro!: join_contexts_tycount_context_constraint typing_typing_all.intros
        join_contexts_split kinding_kinding_allI
        simp add: tyinf_shareable_constraint_plus_iff)
next
  case (tyinf_split \<Xi> K \<Gamma> C1 x t u C2o y t' ct cu C2)
  moreover have
    "K \<turnstile> t wellformed"
    "K \<turnstile> u wellformed"
    using tyinf_split
    by (fastforce dest: tyinf_preserves_wellformed(1)[where t="TProduct t u", simplified type_wellformed_pretty_simps])+
  ultimately show ?case
    apply (clarsimp simp add: shareable_iff_nonlinear droppable_iff_nonlinear
        tyinf_shareable_constraint_plus_iff)
    apply (rule exI, rule conjI)
     apply (rule join_contexts_tycount_context_constraint; blast)
    apply (rule typing_typing_all.intros)
      apply (rule join_contexts_split; blast)
     apply blast
      (* TODO: box the weakening_comp bit up into a lemma *)
    apply (force intro: typing_weaken_context weakening_refl simp add: weakening_Cons
        tycount_context_constraint_comp.simps weakening_comp.simps droppable_def is_used_def)
    done
next
  case (tyinf_let \<Xi> K \<Gamma> C1 x t C2o y u ct C2)
  moreover have
    "K \<turnstile> t wellformed"
    using tyinf_let by force
  ultimately show ?case
    apply (clarsimp simp add: shareable_iff_nonlinear droppable_iff_nonlinear
        tyinf_shareable_constraint_plus_iff)
    apply (rule exI, rule conjI)
     apply (rule join_contexts_tycount_context_constraint; blast)

    apply (rule typing_typing_all.intros)
      apply (rule join_contexts_split; blast)
     apply blast
    apply (force intro: typing_weaken_context weakening_refl simp add: weakening_Cons
        tycount_context_constraint_comp.simps weakening_comp.simps droppable_def is_used_def)
    done
next
  case (tyinf_letb \<Xi> K \<Gamma> C1 x t ct C2 y u "is")
  then show ?case
    sorry
next
  case (tyinf_case \<Xi> K \<Gamma> C1 x \<tau>1 ts tag t C2ao a u c2a C2a C2bo b c2b C2b)
  moreover have C_lengths: "length C2a = length \<Gamma>" "length C2b = length \<Gamma>" "length C1 = length \<Gamma>"
    using tyinf_case
    by (force dest!: tyinf_context_lengths)+
  moreover then have
    "shareable_constraint K \<Gamma> C1"
    "shareable_constraint K \<Gamma> C2a"
    "shareable_constraint K \<Gamma> C2b"
    "new_shareable_constraint K \<Gamma> C1 (countMax C2a C2b)"
    using tyinf_case.prems
    by (clarsimp simp add: shareable_constraint_plus_iff shareable_constraint_max_iff)+
  moreover have
    "K \<turnstile> t wellformed"
    "K \<turnstile> TSum (tagged_list_update tag (t, Checked) ts) wellformed"
    using tyinf_case
    by (blast intro: type_wellformed_pretty_tsum_updateI wellformed_sum_wellformed_elem tyinf_preserves_wellformed)+
  ultimately show ?case
    apply clarsimp
    apply (intro exI conjI)
     apply (rule join_contexts_tycount_context_constraint)
       apply blast
      apply (rule join_contexts_max_tycount_context_constraint; blast)
     apply blast

    apply (rule typing_typing_all.intros)
        apply (rule join_contexts_split)
           apply blast
          apply blast
         apply (rule join_contexts_max_tycount_context_constraint; blast)
        apply (simp add: shareable_constraint_plus_iff tycount_context_constraint_conv_all_nth)

       apply blast
      apply blast

     apply (rule typing_weaken_context[OF _ weakening_cons], blast)
      apply (force simp add: tycount_context_constraint_comp.simps weakening_comp.simps droppable_def is_used_def)
     apply (rule join_contexts_weaken_max(1); blast)

    apply (rule typing_weaken_context[OF _ weakening_cons], blast)
     apply (force simp add: tycount_context_constraint_comp.simps weakening_comp.simps droppable_def is_used_def)
    apply (rule join_contexts_weaken_max(2); blast)
    done
next
  case (tyinf_if \<Xi> K \<Gamma> C1 x \<tau> C2a a t C2b b)
  moreover have C_lengths: "length C2a = length \<Gamma>" "length C2b = length \<Gamma>" "length C1 = length \<Gamma>"
    using tyinf_if
    by (force dest!: tyinf_context_lengths)+
  moreover then have
    "shareable_constraint K \<Gamma> C1"
    "shareable_constraint K \<Gamma> C2a"
    "shareable_constraint K \<Gamma> C2b"
    "new_shareable_constraint K \<Gamma> C1 (countMax C2a C2b)"
    using tyinf_if.prems
    by (clarsimp simp add: shareable_constraint_plus_iff shareable_constraint_max_iff)+
  ultimately show ?case
    apply clarsimp
    apply (intro exI conjI)
     apply (rule join_contexts_tycount_context_constraint)
       apply blast
      apply (rule join_contexts_max_tycount_context_constraint; blast)
     apply blast

    apply (rule typing_typing_all.intros)
       apply (rule join_contexts_split)
          apply blast
         apply blast
        apply (rule join_contexts_max_tycount_context_constraint; blast)
       apply (simp add: shareable_constraint_plus_iff tycount_context_constraint_conv_all_nth)
      apply blast
     apply (blast intro!: typing_weaken_context join_contexts_weaken_max(1))
    apply (blast intro!: typing_weaken_context join_contexts_weaken_max(2))
    done
next
  case (tyinf_take \<Xi> K \<Gamma> C1 e \<tau>1 ts s f n t taken C2o e' u ct cr C2)
  moreover have
    "K \<turnstile> t wellformed"
    "K \<turnstile> TRecord (ts[f := (n, t, taken)]) s wellformed"
    sorry
  ultimately show ?case
    apply -
    apply (clarsimp simp add: tyinf_shareable_constraint_plus_iff shareable_def)
    apply (intro exI conjI)
     apply (rule join_contexts_tycount_context_constraint; blast)
    apply (intro typing_typing_all.intros)
           apply (rule join_contexts_split; blast)
          apply blast
         apply blast
        apply blast
       apply blast
      apply (rule kinding_kinding_allI; blast)
     apply assumption

    apply (rule typing_weaken_context)
     apply blast
    apply (simp add: weakening_Cons)
    apply (intro conjI)
      apply (force simp add: tycount_context_constraint_comp.simps weakening_comp.simps droppable_def is_used_def)
     apply (force simp add: tycount_context_constraint_comp.simps weakening_comp.simps droppable_def is_used_def)
    apply (blast intro: weakening_refl)
    done
next
  case (tyinf_promote \<Xi> K \<Gamma> C x t' t)
  then show ?case
    sorry
next
  case (tyinf_all_cons \<Xi> K \<Gamma> C1 e t C2 es ts)
  then show ?case sorry
qed (fastforce intro: tycount_context_constraint_empty typing_typing_all.intros
        simp add: type_wellformed_all_length is_consumed_conv_all_nth weakening_comp_simps2)+

end
