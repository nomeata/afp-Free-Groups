header {* Cancelation of words of generators and their inverses *}

theory Cancelation
imports
   "~~/src/HOL/Algebra/Group"
   List
   "~~/src/HOL/Lambda/Commutation"
begin

text {*
This theory defines cancelation via relations. The one-step relation @{term
"cancels_to_1 a b"} describes that @{term b} is obtained from @{term a} by removing
exactly one pair of generators, while @{term cancels_to} is the reflexive
transitive hull of that relation. Due to confluence, this relation has a normal
form, allowing for the definition of @{term normalize}.
*}


subsection {* Auxillary results about relations *}

text {*
These were helpfully provided by Andreas Lochbihler.
*}

theorem lconfluent_confluent:
  "[| wfP (R^--1); !!a b c. R a b ==> R a c ==> \<exists>d. R^** b d \<and> R^** c d  |] ==> confluent R"
by(auto simp add: diamond_def commute_def square_def intro: newman)

lemma confluentD:
  "[| confluent R; R^** a b; R^** a c  |] ==> \<exists>d. R^** b d \<and> R^** c d"
by(auto simp add: commute_def diamond_def square_def)

lemma tranclp_DomainP: "R^++ a b ==> DomainP R a"
by(auto elim: converse_tranclpE)

lemma confluent_unique_normal_form:
  "[| confluent R; R^** a b; R^** a c; ~ DomainP R b; ~ DomainP R c  |] ==> b = c"
apply(drule confluentD[of R a b c], assumption+)
apply clarify
apply(drule rtranclpD[where a=b])
apply(drule rtranclpD[where a=c])
apply(auto dest: tranclp_DomainP)
done

subsection {* Definition of the @{term "canceling"} relation *}

types 'a "g_i" = "(bool \<times> 'a)" (* A generator or its inverse *)
types 'a "word_g_i" = "'a g_i list" (* A word in the generators or their inverses *)

text {*
These type aliases encode the notion of a ``generator or its inverse''
(@{typ "'a g_i"}) and the notion of a ``word in generators and their inverse''
(@{typ "'a word_g_i"}), which form the building blocks of Free Groups.
*}
(* Too bad I cannot use antiquotations _before_ the definition, it would make
the text easier to read. *)

definition canceling :: "'a g_i => 'a g_i => bool"
 where "canceling a b = ((snd a = snd b) \<and> (fst a ~= fst b))"

text {*
A generators cancels with its inverse, either way.
*}

subsubsection {* Simple results about canceling *}
lemma cancel_cancel: "[| canceling a b ; canceling b c  |] ==> a = c"
apply (simp add:canceling_def)
apply(rule prod_eqI)
apply auto
done

lemma cancel_sym: "canceling a b ==> canceling b a"
apply (simp add:canceling_def)
done

lemma cancel_sym_neg: "~canceling a b ==> ~canceling b a"
apply (rule classical)
apply (simp add:canceling_def)
done

subsection {* Definition of the @{term "cancels_to"} relation *}

text {*
First, we define the function that removes the @{term i}th and @{text "(i+1)"}st
element from a word of generators, together with basic properties.
*}

definition cancel_at :: "nat => 'a word_g_i => 'a word_g_i"
where "cancel_at i l = take i l @ drop (2+i) l"

lemma cancel_at_length[simp]: "[| 1+i < length l  |] ==> length (cancel_at i l) = length l - 2"
apply(auto simp add: cancel_at_def)
done

lemma cancel_at_nth1[simp]: "[| n < i; 1+i < length l  |] ==> (cancel_at i l) ! n = l !n"
apply(auto simp add: cancel_at_def nth_append)
done

lemma cancel_at_nth2[simp]: "[| n \<ge> i; n < length l - 2  |] ==> (cancel_at i l) ! n = l ! (n + 2)"
apply(auto simp add: cancel_at_def nth_append nth_via_drop)
apply(subgoal_tac "i = min (length l) i")
prefer 2
apply auto
done

text {*
Then we can define the relation @{term "cancels_to_1_at i a b"} which specifies
that @{term b} can be obtained by @{term a} by canceling the @{term i}th and
@{text "(i+1)"}st position.

Base on that, we existentially quantify over the position @{text i} to obtain
the relation @{text "cancels_to_1"}, of wich @{text "cancels_to"} is the
transitive hull.

A word is @{text "canceled"} if it can not be canceled any futher.
*}

definition cancels_to_1_at ::  "nat => 'a word_g_i => 'a word_g_i => bool"
where  "cancels_to_1_at i l1 l2 = (0\<le>i \<and> (1+i) < length l1
                              \<and> canceling (l1 ! i) (l1 ! (1+i))
                              \<and> (l2 = cancel_at i l1))"

definition cancels_to_1 :: "'a word_g_i => 'a word_g_i => bool"
where "cancels_to_1 l1 l2 = (\<exists>i. cancels_to_1_at i l1 l2)"

definition cancels_to  :: "'a word_g_i => 'a word_g_i => bool"
where "cancels_to = cancels_to_1^**"

definition canceled :: "'a word_g_i => bool"
 where "canceled l = (~ DomainP cancels_to_1 l)"

(*
lemma "cancels_to_1 [(True,(1::nat)),(False,1)] []"
  by (auto simp add:cancels_to_1_def canceling_def cancel_at_def cancels_to_1_at_def)
lemma "cancels_to [(True,(1::nat)),(False,1)] []"
  by (auto simp add:cancels_to_1_def canceling_def cancel_at_def cancels_to_1_at_def)
*)

subsubsection {* Existence of the normal form *}

text {*
One of two steps to show that we have a normal form is the following lemma,
quaranteeing that by canceling, we always end up at a fully canceled word.
*}

lemma canceling_terminates: "wfP (cancels_to_1^--1)"
apply(simp add:wfP_def)
apply (rule_tac r = "measure size" in wf_subset)
apply(auto simp add: cancels_to_1_def cancel_at_def cancels_to_1_at_def)
done

lemma cancels_to_1E: "[| cancels_to_1 l1 l2 ;
  !! i. [| cancels_to_1_at i l1 l2   |]
   ==> P  |] ==> P"
apply (auto  simp add:cancels_to_1_def)
done

text {*
The next two lemmas preper for the proof of confluence. It does not matter in
which order we cancel, we can obtain the same result.
*}

lemma canceling_neighbor: "[| cancels_to_1_at i l a; cancels_to_1_at (Suc i) l b  |] ==> a = b"
apply(auto simp add: cancel_at_def cancels_to_1_at_def)
apply(subgoal_tac "l ! i = l ! Suc (Suc i)")
prefer 2
apply(erule cancel_cancel)
apply assumption
apply(thin_tac "canceling ?x ?y")
apply(thin_tac "canceling ?x ?y")
apply(case_tac "drop (Suc (Suc i)) l")
apply auto[1]
apply(auto simp add: take_Suc_conv_app_nth)
apply(subgoal_tac "(a,b)=l!i")
apply auto[1]
apply(simp only:nth_via_drop)
apply(subgoal_tac "list = tl (drop (Suc (Suc i)) l)")
apply(auto simp add:drop_tl drop_Suc)
done

lemma canceling_indep: "[| cancels_to_1_at i l a; cancels_to_1_at j l b ; j > Suc i |] ==> \<exists> c. cancels_to_1_at (j - 2) a c \<and> cancels_to_1_at i b c"
apply(auto simp add:  cancels_to_1_at_def)[1]

apply(auto simp add:cancel_at_def)
apply(subgoal_tac "Suc (Suc (j - 2)) = j")
prefer 2
apply auto[1]
apply auto[1]

apply(thin_tac "canceling ?x ?y")
apply(thin_tac "canceling ?x ?y")

apply(subgoal_tac "min i j = i")
prefer 2
apply auto[1]
apply simp

apply(subgoal_tac "min (length l) i = i")
prefer 2
apply auto[1]
apply simp

apply(subgoal_tac "min (j - 2) i = i")
prefer 2
apply auto[1]
apply simp

apply(thin_tac "min ?x ?y = ?z")
apply(thin_tac "min ?x ?y = ?z")
apply(thin_tac "min ?x ?y = ?z")

apply(subgoal_tac "(Suc (Suc (j + i - 2))) = j+i")
prefer 2
apply auto[1]
apply (simp add:drop_take)
done

text {* This is the confluence lemma *}

lemma lconf: "confluent cancels_to_1"
apply(rule lconfluent_confluent)
apply(rule canceling_terminates)
apply(simp add: cancels_to_1_def)
apply(erule exE)
apply(erule exE)
apply(rename_tac a b c i j)

apply(case_tac "j=i")
apply(simp add: cancels_to_1_at_def)
apply(rule_tac x="b" in exI)
apply auto[1]

apply(case_tac "j=Suc i")
apply clarsimp
apply(rule_tac x="b" in exI)
apply(subgoal_tac "b=c")
prefer 2
apply(erule canceling_neighbor)
apply assumption
apply auto[1]

apply(case_tac "i=Suc j")
apply clarsimp
apply(rule_tac x="c" in exI)
apply(subgoal_tac "c=b")
prefer 2
apply(erule canceling_neighbor)
apply assumption
apply auto[1]

apply(subgoal_tac "\<exists>d. cancels_to_1 b d \<and> cancels_to_1 c d")
apply auto[1]
apply(simp add:cancels_to_1_def)

apply(case_tac "i<j")
apply(subgoal_tac "\<exists>d. cancels_to_1_at (j - 2) b d \<and> cancels_to_1_at i c d")
apply auto[1]
apply(erule canceling_indep)
apply auto[2]

apply(subgoal_tac "\<exists>d. cancels_to_1_at (i - 2) c d \<and> cancels_to_1_at j b d")
apply auto[1]
apply(erule canceling_indep)
apply auto[2]
done

text {*
And finally, we show that there exists a unique normal form for each word.
*}

lemma inv_rtrcl: "R^**^--1 = R^--1^**"
apply (auto simp add:expand_fun_eq intro: dest:rtranclp_converseD intro:rtranclp_converseI)
done

lemma norm_form_uniq: "[| cancels_to a b; cancels_to a c; canceled b; canceled c  |] ==> b = c"
apply(simp add: cancels_to_def canceled_def)
apply(rule_tac R="cancels_to_1" and a="a" in confluent_unique_normal_form)
apply(rule lconf)
apply auto
done

subsubsection {* Some properties on cancelation *}

text {*
Distributivity rules of cancelation and @{text append}.
*}

lemma cancel_to_1_append_left: "cancels_to_1 a b ==> cancels_to_1 (l@a) (l@b)"
apply(simp add:cancels_to_1_def)
apply(erule exE)
apply(rule_tac x="length l + i" in exI)
apply(auto simp add:cancels_to_1_at_def nth_append cancel_at_def)
done

lemma cancel_to_1_append_right: "cancels_to_1 a b ==> cancels_to_1 (a@l) (b@l)"
apply(simp add:cancels_to_1_def)
apply(erule exE)
apply(rule_tac x="i" in exI)
apply(auto simp add:cancels_to_1_at_def nth_append cancel_at_def)
done

lemma cancel_to_append_left: "cancels_to a b ==> cancels_to (l@a) (l@b)"
apply(simp add:cancels_to_def)
apply(induct rule:rtranclp.induct)
apply auto
apply(subgoal_tac "cancels_to_1 (l@b) (l@c)")
prefer 2
apply(rule cancel_to_1_append_left)
apply assumption
apply auto
done

lemma cancel_to_append_right: "cancels_to a b ==> cancels_to (a@l) (b@l)"
apply(simp add:cancels_to_def)
apply(induct rule:rtranclp.induct)
apply auto
apply(subgoal_tac "cancels_to_1 (b@l) (c@l)")
prefer 2
apply(rule cancel_to_1_append_right)
apply assumption
apply auto
done

lemma cancel_to_append: "[| cancels_to a a' ; cancels_to b b' |] ==> cancels_to (a@b) (a'@b')"
apply(subgoal_tac  "cancels_to (a@b) (a@b')")
prefer 2
apply(rule cancel_to_append_left)
apply assumption
apply(simp add:cancels_to_def)
apply(induct rule:rtranclp.induct)
apply auto
apply(subgoal_tac "cancels_to_1 (ba@b') (c@b')")
prefer 2
apply(rule cancel_to_1_append_right)
apply assumption
apply auto
done

text {*
The empty list is cancelled.
*}

lemma empty_canceled[simp]: "canceled []"
by(auto simp:add canceled_def cancels_to_1_def cancels_to_1_at_def)

lemma cancels_to_self[simp]: "cancels_to l l" by(simp add:cancels_to_def)

subsection {* Definition of normalization *}

text {*
Using the THE construct, we can define the normalization function
@{text normalize} as the unique fully cancled word that the argument cancels
to.
*}

definition normalize :: "'a word_g_i => 'a word_g_i"
where "normalize l = (THE l'. cancels_to l l' \<and> canceled l')"

text {*
Some obvious properties of the normalize function, and other useful lemmas.
*}

lemma foo: "\<exists>l'. cancels_to l l' \<and> canceled l'"
apply(insert canceling_terminates)
apply(simp add:cancels_to_def canceled_def)
apply(simp add:wfP_eq_minimal)
apply(erule_tac x="{l'. cancels_to_1^** l l'}" in allE)
apply auto
apply(rule_tac x="z" in exI)
apply auto
apply(erule_tac x="b" in allE)
apply auto
apply(subgoal_tac "cancels_to_1^** l b")
apply auto[1]
apply(subgoal_tac "cancels_to_1^** z b")
prefer 2
apply (auto)[1]
apply(erule rtranclp_trans)
apply assumption
done

lemma foo': "(!!l'. cancels_to l l' \<and> canceled l' ==> P) ==> P"
apply(insert foo)
apply(rotate_tac 1)
apply(erule_tac x=l in meta_allE)
apply(rotate_tac 1)
apply(erule exE)
apply(erule_tac x=l' in meta_allE)
apply auto
done

lemma normalized_props: "cancels_to l (normalize l) \<and> canceled (normalize l)"
apply(rule_tac l=l in foo')
apply (simp add:normalize_def)
apply(rule_tac a="l'" in theI)
apply (auto elim:norm_form_uniq)
done

lemma normalized_canceled[simp]: "canceled (normalize l)" by (auto simp add:normalized_props)

lemma normalized_cancels_to[simp]: "cancels_to l (normalize l)" by (auto simp add:normalized_props)


lemma normalize_discover: "[| canceled l'; cancels_to l l' |] ==> normalize l = l'"
apply(subgoal_tac "cancels_to l l' \<and> canceled l'")
prefer 2
apply auto[1]
apply(simp add:normalize_def)
apply (auto elim:norm_form_uniq)
done

text {* Words, related by cancelation, have the same normal form *}

lemma normalize_canceled[simp]: "cancels_to l l' ==> normalize l = normalize l'"
apply(rule normalize_discover)
apply auto
apply(simp add:normalize_def)
apply(rule_tac a="normalize l'" in theI2)
apply auto
apply(auto simp add:cancels_to_def normalize_discover)
done


text {* Normalization is idempotent *}

lemma normalize_idemp[simp]: "[| canceled l  |] ==> normalize l = l"
apply(erule  normalize_discover)
apply(auto simp add:cancels_to_def)
done

text {*
This lemma lifts the distributivity results from above to the normalize
function.
*}

lemma normalize_append_cancel_to: "[| cancels_to l1 l1' ; cancels_to l2 l2'  |] ==> normalize (l1 @ l2) = normalize (l1' @ l2')"
apply(subgoal_tac "cancels_to (l1 @ l2) (normalize (l1@l2))")
prefer 2
apply(auto simp add: normalized_props)[1]

apply(subgoal_tac "cancels_to (l1 @ l2) (normalize (l1'@l2'))")
prefer 2

apply(subgoal_tac "cancels_to (l1 @ l2) (l1'@l2')")
prefer 2
apply(rule cancel_to_append)
apply assumption+

apply(subgoal_tac "cancels_to (l1' @ l2') (normalize (l1'@l2'))")
prefer 2
apply(auto simp add: normalized_props)[1]

apply(simp only:cancels_to_def)
apply auto[1]
done

end
