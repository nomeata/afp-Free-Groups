header {* Definition of the Free Group *}

theory "Free-Groups"
imports "Cancelation"
begin

text {*
Based on the work in @{theory Cancelation}, the free group is now easily defined
over the set of fully canceled words with the corresponding operations.
*}

text {*
To define the inverse of a word, we first create a helper function that inverts
a single generator, and show that it is self-inverse.
*}

definition inv1 :: "'a g_i \<Rightarrow> 'a g_i"
 where "inv1 a = (\<not> fst a, snd a)"

lemma inv1_inv1[simp]: "inv1 \<circ> inv1 = (\<lambda>x. x)"
  by (simp add: expand_fun_eq comp_def inv1_def)

text {*
The inverse of a word is obtained by reversing the order of the generator and
inverting each generator using @{term inv1}. Some properties of @{term inv_fg}
are noted.
*}

definition inv_fg :: "'a word_g_i \<Rightarrow> 'a word_g_i"
 where "inv_fg l = rev (map inv1 l)"

lemma cancelling_inf[simp]: "canceling (inv1 a) (inv1 b) = canceling a b"
  by(simp add: canceling_def inv1_def)

lemma inv_idemp: "inv_fg (inv_fg l) = l"
  by (auto simp add:inv_fg_def rev_map)

lemma inv_fg_cancel: "normalize (l @ inv_fg l) = []"
proof(induct l rule:rev_induct)
  show "normalize ([] @ inv_fg []) = []"
    by (auto simp add: inv_fg_def)
next
  fix x :: "'a g_i"
  fix xs :: "'a word_g_i"
  assume "normalize (xs @ inv_fg xs) = []"
  
  have "canceling x (inv1 x)" by (simp add:inv1_def canceling_def)
  moreover
  let ?i = "length xs"
  have "Suc ?i < length xs + 1 + 1 + length xs"
    by auto
  moreover
  have "inv_fg (xs @ [x]) = [inv1 x] @ inv_fg xs"
    by (auto simp add:inv_fg_def)
  ultimately
  have "cancels_to_1_at ?i (xs @ [x] @ (inv_fg (xs @ [x]))) (xs @ inv_fg xs)"
    by (auto simp add:cancels_to_1_at_def cancel_at_def nth_append)
  hence "cancels_to_1 (xs @ [x] @ (inv_fg (xs @ [x]))) (xs @ inv_fg xs)"
    by (auto simp add: cancels_to_1_def)
  hence "cancels_to (xs @ [x] @ (inv_fg (xs @ [x]))) (xs @ inv_fg xs)"
    by (auto simp add:cancels_to_def)
  with `normalize (xs @ (inv_fg xs)) = []`
  show "normalize ((xs @ [x]) @ (inv_fg (xs @ [x]))) = []"
    by auto
qed

lemma inv_fg_cancel2: "normalize (inv_fg l @ l) = []"
proof-
  have "normalize (inv_fg l @ inv_fg (inv_fg l)) = []" by (rule inv_fg_cancel)
  thus "normalize (inv_fg l @ l) = []" by (simp add: inv_idemp)
qed

lemma inv_fg_closure:
  assumes "canceled l"
  shows "canceled (inv_fg l)"
proof(rule ccontr)
  assume "\<not>canceled (inv_fg l)"
  hence "DomainP cancels_to_1 (inv_fg l)" by (simp add: canceled_def)
  then obtain l' where "cancels_to_1 (inv_fg l) l'" by auto
  then obtain i where "cancels_to_1_at i (inv_fg l) l'" by (auto simp add:cancels_to_1_def)
  hence "Suc i < length (inv_fg l)"
    and "canceling (inv_fg l ! i) (inv_fg l ! Suc i)"
    by (auto simp add:cancels_to_1_at_def)
  let ?x = "length l - i - 2"
  from `Suc i < length (inv_fg l)`
  have "Suc i < length l" by (simp add: inv_fg_def)
  hence "Suc ?x < length l" by auto

  moreover
  from `Suc i < length l`
  have "i < length l" and "length l - Suc i = Suc(length l - Suc (Suc i))" by auto
  hence "inv_fg l ! i = inv1 (l ! Suc ?x)"
    by (auto simp add:inv_fg_def rev_nth map_nth)
  from `Suc i < length l`
  have "inv_fg l ! Suc i = inv1 (l ! ?x)"
    by (auto simp add:inv_fg_def rev_nth map_nth)
  from `canceling (inv_fg l ! i) (inv_fg l ! Suc i)`
   and `inv_fg l ! i = inv1 (l ! Suc ?x)`
   and `inv_fg l ! Suc i = inv1 (l ! ?x)`
  have "canceling (inv1 (l ! Suc ?x)) (inv1 (l ! ?x))" by auto
  hence "canceling (inv1 (l ! ?x)) (inv1 (l ! Suc ?x))" by (rule cancel_sym)
  hence "canceling (l ! ?x) (l ! Suc ?x)" by simp
   ultimately
  have "cancels_to_1_at ?x l (cancel_at ?x l)" 
    by (auto simp add:cancels_to_1_at_def)
  hence "cancels_to_1 l (cancel_at ?x l)"
    by (auto simp add:cancels_to_1_def)
  hence "\<not>canceled l"
    by (auto simp add:canceled_def)
  with `canceled l` show False by contradiction
qed

text {*
Finally, we can define the Free Group, and show that it is indeed a group.
*}

constdefs
  "free_group \<equiv> (|carrier = {x :: 'a word_g_i. canceled x}, mult = \<lambda> x y . normalize (x @ y), one = []|)"

lemma  "group free_group"
proof
  fix x y
  show "x \<otimes>\<^bsub>free_group\<^esub> y \<in> carrier free_group"
    by (auto simp add:free_group_def)
next
  fix x y z
  have "cancels_to (x @ y) (normalize (x @ (y::'a word_g_i)))"
   and "cancels_to z (z::'a word_g_i)"
    by auto
  hence "normalize (normalize (x @ y) @ z) = normalize ((x @ y) @ z)"
    by (rule normalize_append_cancel_to[THEN sym])
  moreover
  have "\<dots> = normalize (x @ (y @ z))" by auto
  moreover
  have "cancels_to (y @ z) (normalize (y @ (z::'a word_g_i)))"
   and "cancels_to x (x::'a word_g_i)"
    by auto
  hence "normalize (x @ (y @ z)) = normalize (x @ normalize (y @ z))"
    by -(rule normalize_append_cancel_to)
  ultimately
  have "normalize (normalize (x @ y) @ z) = normalize (x @ normalize (y @ z))"
    by simp
  thus "x \<otimes>\<^bsub>free_group\<^esub> y \<otimes>\<^bsub>free_group\<^esub> z =
        x \<otimes>\<^bsub>free_group\<^esub> (y \<otimes>\<^bsub>free_group\<^esub> z)"
    by (auto simp add:free_group_def)
next
  show "\<one>\<^bsub>free_group\<^esub> \<in> carrier free_group" 
    by (auto simp add:free_group_def)
next
  fix x
  assume "x \<in> carrier free_group" 
  thus "\<one>\<^bsub>free_group\<^esub> \<otimes>\<^bsub>free_group\<^esub> x = x"
    by (auto simp add:free_group_def)
next
  fix x
assume "x \<in> carrier free_group"
  thus "x \<otimes>\<^bsub>free_group\<^esub> \<one>\<^bsub>free_group\<^esub> = x"
    by (auto simp add:free_group_def)
next
  show "carrier free_group \<subseteq> Units free_group"
  proof (simp add:free_group_def Units_def, rule subsetI)
    fix x :: "'b word_g_i"
    let ?x = "inv_fg x"
    assume "x \<in> {y. canceled y}"
    hence "canceled ?x" by (auto elim:inv_fg_closure)
    moreover
    have "normalize (?x @ x) = []"
     and "normalize (x @ ?x) = []"
      by (auto simp add:inv_fg_cancel inv_fg_cancel2)
    ultimately
    have "\<exists>x'. canceled x' \<and> normalize (x' @ x) = [] \<and> normalize (x @ x') = []" by auto
    with `x \<in> {y. canceled y}`
    show "x \<in> {y. canceled y \<and>
               (\<exists>x. canceled x \<and> normalize (x @ y) = [] \<and> normalize (y @ x) = [])}"
      by auto
  qed
qed

end
