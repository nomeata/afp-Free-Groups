header {* Isomorphisms of Free Groups *}

theory "Isomorphisms"
imports
   "Free-Groups"
   "UnitGroup"
begin

subsection {* The Free Group over the empty set *}

text {* The Free Group over an empty set of generators is isomorphic to the trivial
group. *}

lemma free_group_over_empty_set: "\<exists>h. h \<in> free_group {} \<cong> unit_group"
proof(rule group.unit_group_unique)
  show "group (free_group {})" by (rule free_group_is_group)
next
  have "carrier (free_group ({}::'a set)) = {[]}"
    by(auto simp add:free_group_def occuring_generators_def)
  thus "card (carrier (free_group ({}::'a set))) = 1"
    by simp
qed


subsection {* Free Groups over isomorphic sets of generators *}

text {* Free Groups are isomorphic if their set of generators are isomorphic. The
converse holds as well, but is not shown here. That result could be achieved by
showing that it holds for free abelian groups, which are the abelianization of
free groups. *}

definition lift_generator_function :: "('a \<Rightarrow> 'b) \<Rightarrow> (bool \<times> 'a) list \<Rightarrow> (bool \<times> 'b) list"
where "lift_generator_function f = map (prod_fun id f)"


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

end