header {* Definition of the Free Group *}

theory "Free-Groups"
imports "Cancelation"
begin

text {*
Based on the work in @{theory Cancelation}, the free group is now easily defined
over the set of fully canceled words.
*}

typedef 'a free_group_set = "{x :: 'a word_g_i. canceled x}"
apply(rule_tac x="[]" in exI)
apply (auto simp add:normalize_def)
done

text {*
Multiplication is concatenation, followed by normalization.
*}

definition mult_norm :: "'a word_g_i \<Rightarrow> 'a word_g_i \<Rightarrow> 'a word_g_i"
where "mult_norm l1 l2 = normalize (l1@l2)"

text {*
To define the inverse of a word, we first create a helper function that inverts
a single generator, and show that it is self-inverse.
*}

definition inv1 :: "'a g_i \<Rightarrow> 'a g_i"
 where "inv1 a = (\<not> fst a, snd a)"

lemma inv1_inv1[simp]: "inv1 \<circ> inv1 = id"
apply(simp add: expand_fun_eq comp_def inv1_def)
done

text {*
The inverse of a word is obtained by reversing the order of the generator and
inverting each generator using @{term inv1}. Some properties of @{term inv_fg}
are noted.
*}

definition inv_fg :: "'a word_g_i \<Rightarrow> 'a word_g_i"
 where "inv_fg l = rev (map inv1 l)"

lemma cancelling_inf[simp]: "canceling (inv1 a) (inv1 b) = canceling a b"
apply(simp add: canceling_def inv1_def)
done

lemma inv_fg_closure: "l \<in> free_group_set \<Longrightarrow> inv_fg l \<in> free_group_set"
apply(simp add:inv_fg_def free_group_set_def canceled_def)
apply(auto)
apply(subgoal_tac "cancels_to_1 l (rev (map inv1 b))")
apply auto[1]
apply(thin_tac "\<not> DomainP cancels_to_1 l")


apply(simp add:cancels_to_1_def)
apply auto[1]

apply(rule_tac x="length l - i - 2" in exI)
apply(auto simp add:cancels_to_1_at_def)
apply(auto simp add:rev_nth)
apply(rule cancel_sym)
apply(subgoal_tac "Suc (length l - Suc (Suc i)) = length l - Suc i")
apply simp
apply auto[1]
apply(subgoal_tac "Suc (Suc (length l - Suc (Suc i))) = length l - i")
apply(auto simp add: id_def cancel_at_def rev_map rev_take rev_drop take_map drop_map)
done

text {*
Finally, we can define the Free Group, and show that it is indeed a group.
*}

constdefs
  "free_group \<equiv> (|carrier = free_group_set, mult = mult_norm, one = []|)"

lemma  "group free_group"
unfolding free_group_def
apply(rule groupI)
apply(auto)
apply(simp add:mult_norm_def free_group_set_def)
apply(simp add:empty_canceled free_group_set_def)
prefer 2
apply(auto elim: normalize_idemp simp add:mult_norm_def free_group_set_def)[1]

apply(simp add:mult_norm_def)
apply(subgoal_tac "normalize (normalize (x @ y) @ z) = normalize ((x @ y) @ z)")
prefer 2
apply(rule sym)
apply(rule normalize_append_cancel_to)
apply auto
apply(subgoal_tac "normalize (x @ normalize (y @ z)) = normalize (x @ (y @ z))")
prefer 2
apply(rule sym)
apply(rule normalize_append_cancel_to)
apply auto

apply(rename_tac l)
apply(rule_tac x="inv_fg l" in bexI)
apply(induct_tac l)
apply(auto simp add:inv_fg_def mult_norm_def)[1]
apply(auto simp add:inv_fg_def mult_norm_def)[1]
apply(subgoal_tac "cancels_to (rev (map inv1 list) @ inv1 (a, b) # (a, b) # list)  (rev (map inv1 list) @ list)")
apply auto[1]
apply(subgoal_tac "cancels_to (inv1 (a, b) # (a, b) # list) list")
prefer 2
apply(subgoal_tac "cancels_to_1_at 0 (inv1 (a, b) # (a, b) # list) list")
prefer 2
apply(simp add:cancels_to_1_at_def inv1_def cancel_at_def canceling_def)
apply(simp add:cancels_to_def)
apply(rule  r_into_rtranclp )
apply(simp add:cancels_to_1_def)
apply(rule_tac x="0" in exI)
apply assumption
apply(rule cancel_to_append_left)
apply assumption
apply(rule inv_fg_closure)
apply assumption
done

end
