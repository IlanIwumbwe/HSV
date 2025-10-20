theory HSV_lecture1 imports Complex_Main
begin

(*
  hence: following from the previous statement, this statement holds
  when we need to go to some arbitrary place in the proof, we can refer to it by name
*)

find_theorems "_ \<in> \<rat>"
thm Rats_abs_nat_div_natE

theorem "sqrt 2 \<notin> \<rat>"
proof
  assume "sqrt 2 \<in> \<rat>"
  then obtain m n where "n\<noteq>0" and "\<bar>sqrt 2\<bar> = real m / real n" and ** : "coprime m n" using
  Rats_abs_nat_div_natE by metis
  hence "\<bar>sqrt 2\<bar>^2 = (real m)^2 / (real n)^2" 
    using power_divide by auto
  hence "2 = (real m)^2 / (real n)^2" 
    by auto
  hence "2 * (real n)^2 = (real m)^2"
    by (metis div_by_0 nonzero_eq_divide_eq zero_neq_numeral)
  hence *: "2*(n^2) = m^2"
    using of_nat_eq_iff by fastforce
  hence "even (m^2)"
    by presburger
  hence ***:"even m" by simp
  then obtain m' where "m = 2*m'" by blast
  hence "2*(n^2) = (2*m')^2" using * by blast
  hence "n^2 = 2*(m'^2)" by simp
  hence "even (n^2)" by presburger
  hence "even n" by simp  
  thus False using ** *** by auto
qed

end