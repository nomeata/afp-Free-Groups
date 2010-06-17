header {* The Free Group *}

theory "Free-Groups"
imports
   "~~/src/HOL/Algebra/Group"
   "Cancelation"
   "Generators"
begin

text {*
Based on the work in @{theory Cancelation}, the free group is now easily defined
over the set of fully canceled words with the corresponding operations.
*}

subsection {* Inversion *}

text {*
To define the inverse of a word, we first create a helper function that inverts
a single generator, and show that it is self-inverse.
*}

definition inv1 :: "'a g_i \<Rightarrow> 'a g_i"
 where "inv1 = apfst Not"

lemma inv1_inv1: "inv1 \<circ> inv1 = id"
  by (simp add: expand_fun_eq comp_def inv1_def)

lemmas inv1_inv1_simp [simp] = inv1_inv1[unfolded id_def]

lemma snd_inv1: "snd \<circ> inv1 = snd"
  by(simp add: expand_fun_eq comp_def inv1_def)

text {*
The inverse of a word is obtained by reversing the order of the generators and
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
  case Nil thus ?case
    by (auto simp add: inv_fg_def)
next
  case (snoc x xs)
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

lemma canceled_rev:
  assumes "canceled l"
  shows "canceled (rev l)"
proof(rule ccontr)
  assume "\<not>canceled (rev l)"
  hence "DomainP cancels_to_1 (rev l)" by (simp add: canceled_def)
  then obtain l' where "cancels_to_1 (rev l) l'" by auto
  then obtain i where "cancels_to_1_at i (rev l) l'" by (auto simp add:cancels_to_1_def)
  hence "Suc i < length (rev l)"
    and "canceling (rev l ! i) (rev l ! Suc i)"
    by (auto simp add:cancels_to_1_at_def)
  let ?x = "length l - i - 2"
  from `Suc i < length (rev l)`
  have "Suc ?x < length l" by auto
  moreover
  from `Suc i < length (rev l)`
  have "i < length l" and "length l - Suc i = Suc(length l - Suc (Suc i))" by auto
  hence "rev l ! i = l ! Suc ?x" and "rev l ! Suc i = l ! ?x"
    by (auto simp add: rev_nth map_nth)
  with `canceling (rev l ! i) (rev l ! Suc i)`
  have "canceling (l ! Suc ?x) (l ! ?x)" by auto
  hence "canceling (l ! ?x) (l ! Suc ?x)" by (rule cancel_sym)
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

lemma inv_fg_closure1:
  assumes "canceled l"
  shows "canceled (inv_fg l)"
unfolding inv_fg_def and inv1_def and apfst_def
proof-
  have "inj Not" by (auto intro:injI)
  moreover
  have "inj_on id (occuring_generators l)" by auto
  ultimately
  have "canceled (map (prod_fun Not id) l)" 
    using `canceled l` by -(rule rename_gens_canceled)
  thus "canceled (rev (map (prod_fun Not id) l))" by (rule canceled_rev)
qed

lemma inv_fg_closure2:
  "occuring_generators (inv_fg l) = occuring_generators l"
 unfolding occuring_generators_def and inv_fg_def
proof-
  have "set (map snd (rev (map inv1 l))) = set (rev (map snd (map inv1 l)))" by auto
  also have "\<dots> = set (rev (map (snd \<circ> inv1) l))" by auto
  also have "... = set (rev (map snd l))" by (simp add: snd_inv1)
  also have "\<dots> = set (map snd l)" by simp
  finally
  show "set (map snd (rev (map inv1 l))) = set (map snd l)".
qed

subsection {* The definition *}

text {*
Finally, we can define the Free Group over a set of generators, and show that it
is indeed a group.
*}

definition free_group :: "'a set => ((bool * 'a) list) monoid"
where 
  "free_group gens \<equiv> (|
     carrier = {l :: 'a word_g_i. canceled l \<and> occuring_generators l \<subseteq> gens },
     mult = \<lambda> x y. normalize (x @ y),
     one = []
  |)"

lemma occuring_gens_in_element:
  "x \<in> carrier (free_group gens) \<Longrightarrow> occuring_generators x \<subseteq> gens"
by(auto simp add:free_group_def)

theorem free_group_is_group: "group (free_group gens)"
proof
  fix x y
  assume "x \<in> carrier (free_group gens)" hence x: "occuring_generators x \<subseteq> gens" by
    (rule occuring_gens_in_element)
  assume "y \<in> carrier (free_group gens)" hence y: "occuring_generators y \<subseteq> gens" by
    (rule occuring_gens_in_element)

  have "occuring_generators (x \<otimes>\<^bsub>free_group gens\<^esub> y) = occuring_generators (normalize (x @ y))"
    by (auto simp add:free_group_def)
  also have "\<dots> \<subseteq> occuring_generators (x @ y)"
    by (rule normalize_preserves_generators)
  also have "\<dots> \<subseteq> occuring_generators x \<union> occuring_generators y"
    by (rule occuring_generators_concat)
  also from x and y have "\<dots> \<subseteq> gens" by simp
  finally have "occuring_generators (x \<otimes>\<^bsub>free_group gens\<^esub> y) \<subseteq> gens".
  
  thus "x \<otimes>\<^bsub>free_group gens\<^esub> y \<in> carrier (free_group gens)"
    by (auto simp add:free_group_def)
next
  fix x y z
  have "cancels_to (x @ y) (normalize (x @ (y::'a word_g_i)))"
   and "cancels_to z (z::'a word_g_i)"
    by auto
  hence "normalize (normalize (x @ y) @ z) = normalize ((x @ y) @ z)"
    by (rule normalize_append_cancel_to[THEN sym])
  also
  have "\<dots> = normalize (x @ (y @ z))" by auto
  also
  have "cancels_to (y @ z) (normalize (y @ (z::'a word_g_i)))"
   and "cancels_to x (x::'a word_g_i)"
    by auto
  hence "normalize (x @ (y @ z)) = normalize (x @ normalize (y @ z))"
    by -(rule normalize_append_cancel_to)
  finally
  show "x \<otimes>\<^bsub>free_group gens\<^esub> y \<otimes>\<^bsub>free_group gens\<^esub> z =
        x \<otimes>\<^bsub>free_group gens\<^esub> (y \<otimes>\<^bsub>free_group gens\<^esub> z)"
    by (auto simp add:free_group_def)
next
  show "\<one>\<^bsub>free_group gens\<^esub> \<in> carrier (free_group gens)"
    by (auto simp add:free_group_def)
next
  fix x
  assume "x \<in> carrier (free_group gens)"
  thus "\<one>\<^bsub>free_group gens\<^esub> \<otimes>\<^bsub>free_group gens\<^esub> x = x"
    by (auto simp add:free_group_def)
next
  fix x
  assume "x \<in> carrier (free_group gens)"
  thus "x \<otimes>\<^bsub>free_group gens\<^esub> \<one>\<^bsub>free_group gens\<^esub> = x"
    by (auto simp add:free_group_def)
next
  show "carrier (free_group gens) \<subseteq> Units (free_group gens)"
  proof (simp add:free_group_def Units_def, rule subsetI)
    fix x :: "'a word_g_i"
    let ?x' = "inv_fg x"
    assume "x \<in> {y. canceled y \<and> occuring_generators y \<subseteq> gens}"
    hence "canceled ?x' \<and> occuring_generators ?x' \<subseteq> gens" by (auto elim:inv_fg_closure1 simp add:inv_fg_closure2)
    moreover
    have "normalize (?x' @ x) = []"
     and "normalize (x @ ?x') = []"
      by (auto simp add:inv_fg_cancel inv_fg_cancel2)
    ultimately
    have "\<exists>x'. canceled x' \<and> occuring_generators x' \<subseteq> gens \<and> normalize (x' @ x) = [] \<and> normalize (x @ x') = []" by auto
    with `x \<in> {y. canceled y \<and> occuring_generators y \<subseteq> gens}`
    show "x \<in> {y. canceled y \<and> occuring_generators y \<subseteq> gens \<and>
          (\<exists>x. canceled x \<and> occuring_generators x \<subseteq> gens \<and>
              normalize (x @ y) = [] \<and> normalize (y @ x) = [])}"
      by auto
  qed
qed

subsection {* Isomorphisms of Free Groups *}

subsubsection {* The Free Group over the empty set *}

text {* The Free Group over an empty set of generators is isomorphic to the trivial
group. (TODO: Find the formalization of the trivial group in HOLs library) *}

subsubsection {* Free Groups over isomorphic sets of generators *}

text {* Free Groups are isomorphic if their set of generators are isomorphic. The
converse holds as well, but is not shown here. That result could be achieved by
showing that it holds for free abelian groups, which are the abelianization of
free groups. *}

definition lift_generator_function :: "('a \<Rightarrow> 'b) \<Rightarrow> (bool \<times> 'a) list \<Rightarrow> (bool \<times> 'b) list"
where "lift_generator_function f = map (prod_fun id f)"

text {* Nicer way of proving that something is a group homomorphism or isomorphism *}

lemma group_homI[intro]:
  assumes range: "h ` (carrier g1) \<subseteq> carrier g2"
      and hom: "\<forall>x\<in>carrier g1. \<forall>y\<in>carrier g1. h (x \<otimes>\<^bsub>g1\<^esub> y) = h x \<otimes>\<^bsub>g2\<^esub> h y"
  shows "h \<in> hom g1 g2"
proof-
  have "h \<in> carrier g1 \<rightarrow> carrier g2" using range  by auto
  thus "h \<in> hom g1 g2" using hom unfolding hom_def by auto
qed

lemma group_isoI[intro]:
  assumes inj: "inj_on h (carrier g1)"
      and surj: "h ` (carrier g1) = carrier g2"
      and hom: "\<forall>x\<in>carrier g1. \<forall>y\<in>carrier g1. h (x \<otimes>\<^bsub>g1\<^esub> y) = h x \<otimes>\<^bsub>g2\<^esub> h y"
  shows "h \<in> g1 \<cong> g2"
proof-
  from inj and surj
  have bij: "bij_betw h (carrier g1) (carrier g2)"
    unfolding bij_betw_def by (rule conjI)
  hence "h \<in> carrier g1 \<rightarrow> carrier g2"
    by (rule bij_betw_imp_funcset)
  with hom have "h \<in> hom g1 g2"
    unfolding hom_def by auto
  with bij show "h \<in> g1 \<cong> g2"
    unfolding iso_def by auto
qed

theorem isomorphic_free_groups:
  assumes "bij_betw f gens1 gens2"
  shows "lift_generator_function f \<in> free_group gens1 \<cong> free_group gens2"
unfolding lift_generator_function_def
proof
  from `bij_betw f gens1 gens2` have "inj_on f gens1" by (auto simp:bij_betw_def)
  hence "inj_on (prod_fun id f) (UNIV \<times> gens1)" by(auto simp add:prod_fun_inj_on)
  moreover
  have "\<Union>set ` carrier (free_group gens1) \<subseteq> (UNIV :: bool set) \<times> gens1"
    by (auto simp add:free_group_def occuring_generators_def)
  ultimately
  have "inj_on (prod_fun id f) (\<Union>set ` carrier (free_group gens1))"
    by (auto dest:inj_on_subset)
  thus "inj_on (map (prod_fun id f)) (carrier (free_group gens1))"
    by(rule inj_on_mapI)
next
  from `bij_betw f gens1 gens2` have "inj_on f gens1" by (auto simp:bij_betw_def)
  show "map (prod_fun id f) ` carrier (free_group gens1) = carrier (free_group gens2)"
  proof(rule set_ext,rule iffI)
    from `bij_betw f gens1 gens2` have "f ` gens1 = gens2" by (auto simp:bij_betw_def)
    fix x :: "(bool \<times> 'b) list"
    assume "x \<in> image (map (prod_fun id f)) (carrier (free_group gens1))"
    then obtain y :: "(bool \<times> 'a) list" where "x = map (prod_fun id f) y"
                    and "y \<in> carrier (free_group gens1)" by auto
    from `y \<in> carrier (free_group gens1)`
    have "canceled y" and "occuring_generators y \<subseteq> gens1" by (auto simp add:free_group_def)
    hence "set (map snd y) \<subseteq> gens1" unfolding occuring_generators_def by simp
    
    from `x = map (prod_fun id f) y`
    have "occuring_generators x = occuring_generators (map (prod_fun id f) y)"
      by simp
    also have "... = set (map snd (map (prod_fun id f) y))"
      unfolding occuring_generators_def ..
    also have "\<dots> = set (map (snd \<circ> prod_fun id f) y)" by simp
    also have "\<dots> = set (map (f \<circ> snd) y)" by auto
    also have "\<dots> = set (map f (map snd y))" by auto
    also have "\<dots> = f ` set (map snd y)" by (simp only: set_map)
    also from `set (map snd y) \<subseteq> gens1`
         have "\<dots> \<subseteq> f ` gens1" by auto
    also from `image f gens1 = gens2`
         have  "\<dots> \<subseteq> gens2" by simp
    finally
    have "occuring_generators x \<subseteq> gens2" .
    moreover
    from `inj_on f gens1` and `occuring_generators y \<subseteq> gens1`
    have "inj_on f (occuring_generators y)" by -(rule subset_inj_on)
    with `canceled y` have "canceled (map (prod_fun id f) y)"
      by -(rule rename_gens_canceled)
    with `x = map (prod_fun id f) y` have "canceled x" by simp
    ultimately
    show "x \<in> carrier (free_group gens2)" by (simp add:free_group_def)
  next
    fix x
    assume "x \<in> carrier (free_group gens2)"
    hence "canceled x" and "occuring_generators x \<subseteq> gens2"
      unfolding free_group_def by auto
    def y \<equiv> "map (prod_fun id (the_inv_into gens1 f)) x"
    have "map (prod_fun id f) y =
          map (prod_fun id f) (map (prod_fun id (the_inv_into gens1 f)) x)"
      by (simp add:y_def)
    also have "\<dots> = map (prod_fun id f \<circ> prod_fun id (the_inv_into gens1 f)) x"
      by simp
    also have "\<dots> = map (prod_fun id (f \<circ> the_inv_into gens1 f)) x"
      by auto
    also have "\<dots> = map id x"
    proof(rule map_ext, rule impI)
      fix xa :: "bool \<times> 'b"
      assume "xa \<in> set x"
      from `occuring_generators x \<subseteq> gens2`
      have "set (map snd x) \<subseteq> gens2"
        unfolding occuring_generators_def .
      hence "snd ` set x \<subseteq> gens2" by (simp add: set_map)
      with `xa \<in> set x` have "snd xa \<in> gens2" by auto
      with `bij_betw f gens1 gens2` have "snd xa \<in> f`gens1" 
        by (auto simp add: bij_betw_def)

      have "prod_fun id (f \<circ> the_inv_into gens1 f) xa
            = prod_fun id (f \<circ> the_inv_into gens1 f) (fst xa, snd xa)" by simp
      also have "\<dots> = (fst xa, f (the_inv_into gens1 f (snd xa)))"
        by (auto simp del:pair_collapse)
      also with `snd xa \<in> image f gens1` and `inj_on f gens1`
           have "\<dots> = (fst xa, snd xa)" 
           by (auto elim:f_the_inv_into_f simp del:pair_collapse)
      also have "\<dots> = id xa" by simp
      finally show "prod_fun id (f \<circ> the_inv_into gens1 f) xa = id xa".    
    qed
    also have "\<dots> = x" unfolding id_def by auto
    finally have "map (prod_fun id f) y = x".
    moreover
    {
      from `bij_betw f gens1 gens2`
      have "bij_betw (the_inv_into gens1 f) gens2 gens1" by (rule bij_betw_the_inv_into)
      hence "inj_on (the_inv_into gens1 f) gens2" by (rule bij_betw_imp_inj_on)
      with `occuring_generators x \<subseteq> gens2`
      have "inj_on (the_inv_into gens1 f) (occuring_generators x)" by -(rule subset_inj_on)
      with `canceled x`
      have "canceled y" unfolding y_def by-(rule rename_gens_canceled)
      moreover
      { 
        have "occuring_generators y
              = set (map snd (map (prod_fun id (the_inv_into gens1 f)) x))"
          by (simp add:y_def occuring_generators_def)
        also have "\<dots> = set (map ((the_inv_into gens1 f) \<circ> snd) x)" by simp
        also have "\<dots> = set (map (the_inv_into gens1 f) (map snd x))" by simp
        also have "\<dots> = (the_inv_into gens1 f) ` set (map snd x)"
               by (auto simp del:map_map)
        also from `occuring_generators x \<subseteq> gens2`
             have "\<dots> \<subseteq> (the_inv_into gens1 f) ` gens2"
               by (auto simp add: occuring_generators_def)
        also from `bij_betw (the_inv_into gens1 f) gens2 gens1`
             have "\<dots> \<subseteq> gens1" by (simp add:bij_betw_def)
        finally have "occuring_generators y \<subseteq> gens1".
      }
      ultimately
      have "y \<in> carrier (free_group gens1)" by (simp add:free_group_def)
    }
    ultimately
    show "x \<in> map (prod_fun id f) ` carrier (free_group gens1)" by auto
  qed
next
  from `bij_betw f gens1 gens2` have "inj_on f gens1" by (auto simp:bij_betw_def)
  {
  fix x
  assume "x \<in> carrier (free_group gens1)"
  fix y
  assume "y \<in> carrier (free_group gens1)"

  from `x \<in> carrier (free_group gens1)` and `y \<in> carrier (free_group gens1)`
  have "occuring_generators x \<subseteq> gens1" and "occuring_generators y \<subseteq> gens1"
    by (auto simp add:occuring_gens_in_element)
  hence "occuring_generators (x@y) \<subseteq> gens1"
    by(auto simp add:occuring_generators_def)
  with `inj_on f gens1` have "inj_on f (occuring_generators (x@y))"
    by (rule inj_on_subset)

  have "map (prod_fun id f) (x \<otimes>\<^bsub>free_group gens1\<^esub> y)
       = map (prod_fun id f) (normalize (x@y))" by (simp add:free_group_def)
  also from `inj_on f (occuring_generators (x@y))`
       have "\<dots> = normalize (map (prod_fun id f) (x@y))"
       by(auto simp add:rename_gens_normalize[THEN sym])
  also have "\<dots> = normalize (map (prod_fun id f) x @ map (prod_fun id f) y)"
       by (auto)
  also have "\<dots> = map (prod_fun id f) x \<otimes>\<^bsub>free_group gens2\<^esub> map (prod_fun id f) y"
       by (simp add:free_group_def)
  finally have "map (prod_fun id f) (x \<otimes>\<^bsub>free_group gens1\<^esub> y) =
                map (prod_fun id f) x \<otimes>\<^bsub>free_group gens2\<^esub> map (prod_fun id f) y".
  }
  thus "\<forall>x\<in>carrier (free_group gens1).
       \<forall>y\<in>carrier (free_group gens1).
          map (prod_fun id f) (x \<otimes>\<^bsub>free_group gens1\<^esub> y) =
          map (prod_fun id f) x \<otimes>\<^bsub>free_group gens2\<^esub> map (prod_fun id f) y"
   by auto
qed

subsection {* The universal property *}

text {* Free Groups are important due to the universal properties: Every map of
the set of generators to another group can be extended uniquely to an
homomorphism from the Free Group. *}

definition insert
  where "insert g = [(False, g)]"

definition (in group) lift_gi
  where "lift_gi f gi = (if fst gi then m_inv G (f (snd gi)) else f (snd gi))"

lemma (in group) lift_gi_closed:
  assumes cl: "f ` gens \<subseteq> carrier G"
      and "snd gi \<in> gens"
  shows "lift_gi f gi \<in> carrier G"
using assms by (auto simp add:lift_gi_def)

definition (in group) lift
  where "lift f w = m_concat (map (lift_gi f) w)"

lemma (in group) lift_closed[simp]:
  assumes cl: "f ` gens \<subseteq> carrier G"
      and "occuring_generators x \<subseteq> gens"
  shows "lift f x \<in> carrier G"
proof-
  have "set (map (lift_gi f) x) \<subseteq> carrier G"
    using cl and `occuring_generators x \<subseteq> gens`
    by (auto simp add:lift_gi_closed occuring_generators_def)
  thus "lift f x \<in> carrier G"
    by (auto simp add:lift_def)
qed

lemma (in group) lift_append[simp]:
  assumes cl: "f ` gens \<subseteq> carrier G"
      and "occuring_generators x \<subseteq> gens"
      and "occuring_generators y \<subseteq> gens"
  shows "lift f (x @ y) = lift f x \<otimes> lift f y"
proof-
  from `occuring_generators x \<subseteq> gens`
  have "set (map snd x) \<subseteq> gens" unfolding occuring_generators_def by simp
  with `image f gens \<subseteq> carrier G`
  have "set (map (lift_gi f) x) \<subseteq> carrier G"
    by (induct x)(auto simp add:lift_gi_def)
  moreover
  from `occuring_generators y \<subseteq> gens`
  have "set (map snd y) \<subseteq> gens" unfolding occuring_generators_def by simp
  with `image f gens \<subseteq> carrier G`
  have "set (map (lift_gi f) y) \<subseteq> carrier G"
    by (induct y)(auto simp add:lift_gi_def)
  ultimately
  show "lift f (x @ y) = lift f x \<otimes> lift f y"
    by (auto simp add:lift_def m_assoc simp del:set_map foldl_append)
qed

lemma (in group) lift_cancels_to:
  assumes "cancels_to x y"
      and "occuring_generators x \<subseteq> gens"
      and cl: "f ` gens \<subseteq> carrier G"
  shows "lift f x = lift f y"
using assms
unfolding cancels_to_def
proof(induct rule:rtranclp_induct)
  case (step y z)
    from `cancels_to_1\<^sup>*\<^sup>* x y`
    have "occuring_generators y \<subseteq> occuring_generators x"
      by -(rule cancels_to_preserves_generators, simp add:cancels_to_def)
    hence "occuring_generators y \<subseteq> gens"
      using `occuring_generators x \<subseteq> gens` by simp
    hence "lift f x = lift f y"
      using step by auto
    also
    from `cancels_to_1 y z`
    obtain ys1 y1 y2 ys2
      where "y = ys1 @ [y1] @ [y2] @ ys2"
      and "z = ys1 @ ys2"
      and "canceling y1 y2"
    by (rule cancels_to_1_unfold)
    have "lift f y  = lift f (ys1 @ [y1] @ [y2] @ ys2)"
      using `y = ys1 @ [y1] @ [y2] @ ys2` by simp
    also
    from `occuring_generators y \<subseteq> gens`
     and `y = ys1 @ [y1] @ [y2] @ ys2`
    have "occuring_generators ys1 \<subseteq> gens"
     and "occuring_generators ([y1]@[y2]@ys2) \<subseteq> gens"
     and "occuring_generators ([y2]@ys2) \<subseteq> gens"
     and "occuring_generators [y1] \<subseteq> gens"
     and "occuring_generators [y2] \<subseteq> gens"
     and "occuring_generators ys2 \<subseteq> gens"
    unfolding occuring_generators_def by auto
    with `y = ys1 @ [y1] @ [y2] @ ys2` and cl
    have "lift f (ys1 @ [y1] @ [y2] @ ys2)
        = lift f ys1 \<otimes> (lift f [y1] \<otimes> lift f [y2]) \<otimes> lift f ys2"
      by (auto intro:lift_append simp del: append_Cons simp add:m_assoc)
    also
    from `occuring_generators [y1] \<subseteq> gens`
    and `occuring_generators [y2] \<subseteq> gens`
    and cl
    and `canceling y1 y2`
    have "(lift f [y1] \<otimes> lift f [y2]) = \<one>"
    by (auto simp add:lift_def occuring_generators_def lift_gi_def canceling_def)
    hence "lift f ys1 \<otimes> (lift f [y1] \<otimes> lift f [y2]) \<otimes> lift f ys2
           = lift f ys1 \<otimes> \<one> \<otimes> lift f ys2"
      by simp
    also
    from `occuring_generators ys1 \<subseteq> gens`
     and `occuring_generators ys2 \<subseteq> gens`
     and cl
     have "lift f ys1 \<otimes> \<one> \<otimes> lift f ys2 = lift f (ys1 @ ys2)"
      by (auto intro:lift_append)
    also
    from `z = ys1 @ ys2`
    have "lift f (ys1 @ ys2) = lift f z" by simp
    finally show "lift f x = lift f z" .
qed auto

lemma (in group) lift_is_hom:
  assumes cl: "f ` gens \<subseteq> carrier G"
  shows "lift f \<in> hom (free_group gens) G"
proof-
  {
    fix x
    assume "x \<in> carrier (free_group gens)"
    hence "set (map snd x) \<subseteq> gens"
      unfolding free_group_def and occuring_generators_def by simp
    hence "lift f x \<in> carrier G"
     using cl by (induct x rule:rev_induct, auto simp add:lift_def lift_gi_def)
  } 
  moreover
  { fix x
    assume "x \<in> carrier (free_group gens)"
    fix y
    assume "y \<in> carrier (free_group gens)"

    from `x \<in> carrier (free_group gens)` and `y \<in> carrier (free_group gens)`
    have "occuring_generators x \<subseteq> gens" and "occuring_generators y \<subseteq> gens"
      by (auto simp add:free_group_def)
    hence "occuring_generators (x@y) \<subseteq> gens" 
      unfolding occuring_generators_def by auto

    have "lift f (x \<otimes>\<^bsub>free_group gens\<^esub> y) 
         = lift f (normalize (x @ y))" by (simp add:free_group_def)
    also
    have "cancels_to (x @ y) (normalize (x @ y))" by simp
    with `occuring_generators (x@y) \<subseteq> gens`
     and lift_cancels_to[THEN sym] and cl
    have "lift f (normalize (x @ y)) = lift f (x @ y)"
      by(blast)
    also
    from `occuring_generators x \<subseteq> gens`
     and `occuring_generators y \<subseteq> gens` and cl
    have "lift f (x @ y) = lift f x \<otimes> lift f y"
      by simp
    finally
    have "lift f (x \<otimes>\<^bsub>free_group gens\<^esub> y) = lift f x \<otimes> lift f y" .
  }
  ultimately
  show "lift f \<in> hom (free_group gens) G"
    by auto
qed

end
